"use strict";
// Projects and local copies: saving, opening against the shown revision, the
// changed-since-save indicator, and managing backup copies under Web Locks.
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene} = require("./reliability-harness.cjs");
const json = v => JSON.parse(JSON.stringify(v));

test("project save contains full inventory, stones and preferences without changing layout export", () => {
  const h = harness(); h.el("project-name").value = "My bridge";
  h.el("max-pieces").value = 52; h.el("slop").value = 1.5;
  const p = h.run("projectSnapshot()");
  assert.equal(p.name, "My bridge"); assert.equal(p.session.inventory.straight, 17);
  assert.equal(p.session.stones.stone_stop, 2);
  assert.equal(p.preferences.search.max_pieces, 52);
  assert.equal(p.session.layout.format, "duplotrain-layout/1");
  h.el("max-pieces").value = -1; assert.throws(() => h.run("projectSnapshot()"), /valid search/);
});

test("project preferences are only installed after a successful restore", async () => {
  const h = harness({overrides: {api: async () => { throw new Error("bad project"); }, redraw() {}}});
  h.el("project-name").value = "Original";
  await assert.rejects(h.context.openProject({}), /bad project/);
  assert.equal(h.el("project-name").value, "Original"); assert.equal(h.context.S.revision, 1);
  const next = {...scene([], 2), project: {name: "Loaded", preferences: {
    view: {x: 1, y: 2, scale: 2}, search: {max_pieces: 60, slop: 1, reversing: true}}}};
  h.context.api = async () => next; await h.context.openProject({});
  assert.equal(h.context.S.revision, 2); assert.equal(h.el("project-name").value, "Loaded");
  assert.equal(h.context.view.scale, 2); assert.equal(h.el("max-pieces").value, "60");
});

test("slow project selection cannot replace a newer selected project", async () => {
  let finish;
  const opened = [];
  const h = harness({overrides: {openProject: async p => opened.push(p)}});
  const slow = h.context.readProjectFile({target: {files: [{size: 2,
    text: () => new Promise(resolve => { finish = resolve; })}]}});
  await h.context.readProjectFile({target: {files: [{size: 2, text: async () => '{"name":"new"}'}]}});
  finish('{"name":"old"}'); await slow;
  assert.deepEqual(opened.map(p => p.name), ["new"]);
});

test("a project file opens against the revision shown when it was chosen", async () => {
  // An edit that lands while the file is read must make the engine refuse the open.
  const opens = [];
  const h = harness({overrides: {redraw() {}, api: async (path, body) => {
    opens.push({path, revision: body.revision}); throw new Error("Your action was not applied");
  }}});
  let finish;
  const reading = h.context.readProjectFile({target: {files: [{size: 2,
    text: () => new Promise(resolve => { finish = resolve; })}]}});
  h.run("S = {...S, revision: 2}");
  finish('{"format": "duplotrain-project/1"}'); await reading;
  assert.deepEqual(opens, [{path: "/api/project/open", revision: 1}]);
  assert.match(h.notices.at(-1).text, /Project not opened: Your action was not applied/);
});

test("project changed indicator tracks content, view and settings, not revision or autosave", async () => {
  const h=harness({events:true});h.el("project-name").value="Named";
  await h.run("saveLocalProject()");assert.match(h.el("project-status").textContent,/Unchanged/);
  h.run("S.revision++; updateProjectStatus()");assert.match(h.el("project-status").textContent,/Unchanged/);
  h.context.view={x:9,y:0,scale:1};h.run("updateProjectStatus()");assert.match(h.el("project-status").textContent,/Changed/);
  h.context.view={x:0,y:0,scale:1};h.run("updateProjectStatus()");assert.match(h.el("project-status").textContent,/Unchanged/);
  h.el("max-pieces").value=52;h.el("max-pieces").listeners.input();assert.match(h.el("project-status").textContent,/Changed/);
  h.el("max-pieces").value=26;h.run("updateProjectStatus()");assert.match(h.el("project-status").textContent,/Unchanged/);
  h.context.S={...h.context.S,snapshot:{...h.context.S.snapshot,unlimited:true}};h.run("updateProjectStatus()");
  assert.match(h.el("project-status").textContent,/Changed/);
  h.context.localStorage.setItem=()=>{throw new Error("quota");};await h.run("saveLocalProject()");
  assert.match(h.el("project-status").textContent,/Changed/);
});

test("named local saves append copies, preserve autosave, and handle quota failures", async () => {
  const h = harness(); h.el("project-name").value = "Bridge";
  h.saved.set("duplotrain-session/2:/test/", "another tab checkpoint");
  await h.run("saveLocalProject(); saveLocalProject()");
  assert.equal(h.saved.size, 3);
  assert.equal(h.saved.get("duplotrain-session/2:/test/"), "another tab checkpoint");
  const before = [...h.saved];
  h.context.localStorage.setItem = () => { throw new Error("quota"); };
  await h.run("saveLocalProject()");
  assert.deepEqual([...h.saved], before); assert.match(h.notices.at(-1).text, /not saved.*quota/);
});

function stored(h, key, {name="Bridge", saved_at, count=3}={}) {
  const data = h.run("projectSnapshot()"); data.name=name;
  // Deep clone first so a fixture never edits the accepted UI snapshot.
  const copy = json(data); copy.session.layout.placements = Array(count).fill({piece:"curve"});
  if (saved_at) copy.saved_at=saved_at;
  const full = h.run("PROJECT_PREFIX")+key; h.saved.set(full,JSON.stringify(copy)); return full;
}

test("backup labels distinguish duplicate names, sort newest first, and keep legacy/corrupt copies", () => {
  const h = harness();
  const old = stored(h,"old",{saved_at:"2026-01-01T01:00:00.000Z"});
  const recent = stored(h,"new",{saved_at:"2026-02-01T01:00:00.000Z",count:83});
  stored(h,"legacy",{}); h.saved.set(h.run("PROJECT_PREFIX")+"corrupt", "not json");
  h.run("renderProjects()");
  const options=h.el("project-slots").children;
  assert.equal(options[0].value,recent); assert.equal(options[1].value,old);
  assert.match(options[0].textContent,/Bridge.*83 pieces.*new/);
  assert.ok(options.some(o => /date unknown/.test(o.textContent)));
  assert.ok(options.some(o => /Unreadable.*kept/.test(o.textContent)));
  h.el("project-slots").value=old; h.run("renderProjects()"); assert.equal(h.el("project-slots").value,old);
});

for (const action of ["rename", "delete"]) test(`backup ${action} requires confirmation and changes only the captured copy`, async () => {
  const h = harness({events:true}); const key=stored(h,"chosen",{saved_at:"2026-01-01T00:00:00Z"});
  const other=stored(h,"other",{}), otherRaw=h.saved.get(other), current=JSON.stringify(h.context.S);
  h.run("renderProjects()"); h.el("project-slots").value=key;
  await h.el(action+"-local").click();
  assert.ok(h.saved.has(key)); assert.equal(h.el("project-manage").hidden,false);
  const children=h.el("project-manage").children;
  if(action === "rename") children[1].children[0].value="Renamed copy";
  await children.find(c=>c.textContent === "Confirm "+action).click();
  assert.equal(h.saved.get(other),otherRaw); assert.equal(JSON.stringify(h.context.S),current);
  if(action === "delete") assert.equal(h.saved.has(key),false);
  else { const saved=JSON.parse(h.saved.get(key)); assert.equal(saved.name,"Renamed copy"); assert.equal(saved.saved_at,"2026-01-01T00:00:00Z"); }
});

for (const action of ["rename", "delete"]) test(`stale backup ${action} checks bytes inside the lock and never changes another tab's copy`, async () => {
  let acquire;
  const h=harness({events:true, overrides:{navigator:{locks:{request:(_name, fn)=>new Promise((resolve,reject)=>{acquire=()=>{try{resolve(fn());}catch(e){reject(e);}};})}}}});
  const key=stored(h,"target",{}); h.run("renderProjects()"); h.el("project-slots").value=key;
  await h.el(action+"-local").click(); const children=h.el("project-manage").children;
  if(action === "rename") children[1].children[0].value="New name";
  const pending=children.find(c=>c.textContent === "Confirm "+action).click();
  h.saved.set(key,"newer bytes from another tab"); acquire(); await pending;
  assert.equal(h.saved.get(key),"newer bytes from another tab"); assert.match(h.notices.at(-1).text,/not changed.*another tab/);
});

test("cancelling or choosing another backup invalidates its old confirmation", async () => {
  const h=harness({events:true}); const first=stored(h,"one",{}),second=stored(h,"two",{});
  h.run("renderProjects()");h.el("project-slots").value=first;await h.el("delete-local").click();
  const confirm=h.el("project-manage").children.find(c=>c.textContent==="Confirm delete");
  h.el("project-slots").value=second;h.el("project-slots").listeners.change();await confirm.click();
  assert.ok(h.saved.has(first));assert.ok(h.saved.has(second));
});

test("unsafe backup management is refused when Web Locks are unavailable", async () => {
  const h=harness({events:true,overrides:{navigator:{}}});stored(h,"old",{});h.run("renderProjects()");
  await h.el("delete-local").click();assert.equal(h.saved.size,1);
  assert.match(h.notices.at(-1).text,/Safe backup management unavailable/);
});
