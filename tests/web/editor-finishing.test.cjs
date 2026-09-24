"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track} = require("./reliability-harness.cjs");
const json = v => JSON.parse(JSON.stringify(v));
const tracks = () => [track([[-100, 0, 100], [100, 0, 100]], "Top"),
  track([[0, -100, 0], [0, 100, 0]], "Bottom"), track([[1000, 0, 0], [1100, 0, 0]], "Distant")];

for (const action of ["precise", "tool", "diagnostic", "end", "cancel", "replace"]) {
  test(`overlap removal is invalidated by ${action}, even without a revision change`, async () => {
    const h = harness({state: scene(tracks()), events: true, overrides: {redraw() {}}});
    h.context.showOverlapPicker([{placement: 0, z: 100}, {placement: 1, z: 0}], true);
    const confirm = h.el("overlap-picker").children[2];
    if (action === "precise") { h.el("piece-select").value = 2; h.el("piece-select").listeners.change(); }
    if (action === "tool") h.run('selectTool({piece:{piece:"straight",entry:0}})');
    if (action === "diagnostic") h.run("focusPieces([2])");
    if (action === "end") await h.run("activateEnd([2,0])");
    if (action === "cancel") h.el("overlap-picker").children[3].click();
    if (action === "replace") h.context.showOverlapPicker([{placement: 1, z: 0}], true);
    await confirm.click();
    assert.equal(h.calls.length, 0);
  });
}

test("overlap confirmation owns its target and refuses an injected nonmember", async () => {
  const h = harness({state: scene(tracks()), overrides: {redraw() {}}});
  h.context.showOverlapPicker([{placement: 0, z: 100}, {placement: 1, z: 0}], true);
  h.run("selectedPiece = 2");
  await h.el("overlap-picker").children[2].click();
  assert.equal(h.calls[0].body.placement, 0);
  h.context.showOverlapPicker([{placement: 0, z: 100}, {placement: 1, z: 0}], true);
  const select = h.el("overlap-picker").children[1]; select.value = 2; select.listeners.change();
  await h.el("overlap-picker").children[2].click();
  assert.equal(h.calls.length, 1);
});

test("only the overlap dialog target is highlighted while confirming removal", () => {
  const strokes = [];
  const h = harness({state: scene(tracks()), overrides: {strokeSegment: (a, b) => strokes.push([a, b])}});
  h.run("selectedPiece=2; hoveredPiece=2; highlightedPieces=[2]");
  h.context.showOverlapPicker([{placement: 0, z: 100}, {placement: 1, z: 0}], true);
  h.run("drawHighlights()");
  assert.deepEqual(json(strokes), [[[-100, 0, 100], [100, 0, 100]]]);
});

for (const immediate of [true, false]) test(`train ${immediate ? "immediate" : "downstream"} stop has a playable terminal event`, async () => {
  const strokes = [];
  const trace = {revision: 1, outcome: "stopped", start: [0, 0],
    steps: immediate ? [] : [[0, 0, 1]], terminal: {placement: 1, entry: 0, at_port: null, reason: "stop_stone"},
    cycle_start: null, period: null, reversals: 0, visited: [0, 1], visited_drivable: [0, 1],
    drivable_count: 3, unvisited: [2], cycle_pieces: [], complete: true};
  const h = harness({state: scene(tracks()), events: true,
    overrides: {api: async () => trace, strokeSegment: (a, b) => strokes.push([a, b])}});
  h.el("train-start").value = "[0,0]"; await h.run("testTrain()");
  assert.equal(h.el("train-play").disabled, false);
  if (!immediate) await h.el("train-step").click();
  await h.el("train-step").click();
  assert.match(h.el("train-report").textContent, /Final event: #2.*midpoint — stop stone/);
  assert.match(h.el("train-report").textContent, /2 \/ 3 drivable pieces visited/);
  h.run("drawHighlights()"); assert.deepEqual(json(strokes.at(-1)), [[0, -100, 0], [0, 100, 0]]);
  assert.equal(trace.steps.length, immediate ? 0 : 1);
  assert.equal(h.el("train-step").disabled, true);
  await h.el("train-play").click();
  while (h.intervals.size) [...h.intervals.values()][0]();
  assert.equal(h.run("trainStep"), trace.steps.length);
});

test("step limit disables playback and coverage rather than highlighting supposedly unvisited track", async () => {
  const h = harness({state: scene(tracks()), events: true, overrides: {api: async () => ({
    revision: 1, outcome: "limit", limit: 3, steps: [], complete: false, terminal: null, unvisited: null,
  })}});
  h.el("train-start").value = "[0,0]"; await h.run("testTrain()");
  assert.match(h.el("train-report").textContent, /3-step limit.*no verdict or coverage claim/);
  for (const id of ["train-play", "train-step", "train-unvisited", "train-cycle"]) assert.ok(h.el(id).disabled);
});

test("coverage overlays distinguish unvisited and cycle pieces and expire with new settings", async () => {
  const strokes = [];
  const trace = {revision: 1, outcome: "endless", start: [0, 0], steps: [[0,0,1],[1,0,1]],
    cycle_start: 1, period: 1, reversals: 0, visited: [0,1], visited_drivable: [0,1],
    drivable_count: 3, unvisited: [2], cycle_pieces: [1], terminal: null, complete: true};
  const h = harness({state: scene(tracks()), events: true,
    overrides: {api: async () => trace, strokeSegment: (a, b, w, color) => strokes.push({a, b, color})}});
  h.el("train-start").value = "[0,0]"; await h.run("testTrain()");
  h.el("train-unvisited").checked = true; h.el("train-cycle").checked = true;
  h.run("drawHighlights()");
  assert.ok(strokes.some(x => x.a[0] === 1000 && x.color === "#be6712"));
  assert.ok(strokes.some(x => x.a[1] === -100 && x.color === "#168277"));
  h.el("train-start").listeners.change();
  assert.equal(h.run("trainTrace"), null); assert.equal(h.el("train-cycle").checked, false);
});

test("switch controls send explicit choices and reject responses from old selections", async () => {
  let finish, body;
  const s = scene(tracks()); s.train_switches = [{placement: 0, default: 1,
    options: [{port: 1, name: "Left"}, {port: 2, name: "Right"}]}];
  const h = harness({state: s, events: true, overrides: {api: (_path, b) => { body = b; return new Promise(resolve => { finish = resolve; }); }}});
  h.run("renderNavigation()");
  const select = h.el("train-switches").children[0].children[0];
  assert.equal(select.value, "1"); select.value = 2; select.listeners.change();
  h.el("train-start").value = "[0,0]";
  const request = h.run("testTrain()"); assert.deepEqual(json(body.switch_states), {0: 2});
  select.value = 1; select.listeners.change();
  finish({revision: 1, steps: []}); await request;
  assert.equal(h.run("trainTrace"), null);
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

test("100 hover events cause one hit-test at the final position per frame", () => {
  const calls=[];let paints=0;
  const h=harness({events:true,schedule:true,overrides:{paint:()=>paints++,placementAt:(x,y)=>{calls.push([x,y]);return 0;}}});
  for(let i=0;i<100;i++)h.el("canvas").listeners.pointermove({pointerId:1,pointerType:"mouse",clientX:i,clientY:2});
  assert.equal(calls.length,0);assert.equal(h.frames.length,1);h.frames.shift()();
  assert.deepEqual(calls,[[99,2]]);assert.equal(paints,1);
});

for(const action of ["leave","revision","replace","drag"]) test(`queued hover is dropped on ${action}`,()=>{
  let calls=0;
  const h=harness({events:true,schedule:true,overrides:{paint(){},placementAt:()=>{calls++;return 0;}}});
  h.el("canvas").listeners.pointermove({pointerId:1,pointerType:"pen",clientX:10,clientY:2});
  if(action === "leave")h.el("canvas").listeners.pointerleave();
  if(action === "revision")h.run("S.revision++");
  if(action === "replace")h.context.S={...h.context.S,layout:{...h.context.S.layout,placements:[]}};
  if(action === "drag")h.run("pointers.set(1,{x:10,y:2})");
  h.frames.shift()();assert.equal(calls,0);
});

test("a click near a joint picks the piece painted there, without a chooser", async () => {
  // Pieces are painted with flat ends: the neighbour's hit padding past its own
  // end neither wins the tie nor makes the click ambiguous.
  const pieces = [track([[0, 0, 0], [128, 0, 0]], "A"), track([[128, 0, 0], [256, 0, 0]], "B")];
  for (const piece of pieces) piece.width = 64;
  for (const scale of [0.9, 4]) {
    const h = harness({state: scene(pieces, 5), events: true});
    h.run(`view = {x: 128, y: 0, scale: ${scale}}; canvas.clientWidth = 1000; canvas.clientHeight = 500`);
    const [jx, jy] = h.run("worldToScreen(128, 0)");
    for (const mm of [3, 8, 30]) {
      assert.equal(h.run(`placementAt(${jx - mm * scale}, ${jy})`), 0, `${mm} mm inside A at ${scale}`);
      assert.equal(h.run(`placementAt(${jx + mm * scale}, ${jy})`), 1, `${mm} mm inside B at ${scale}`);
    }
    h.run("selectTool({remove: true})");
    await h.run(`removeAt(${jx - 8 * scale}, ${jy})`);
    assert.equal(h.el("overlap-picker").hidden, true);
    assert.deepEqual(json(h.calls.at(-1)), {path: "/api/remove", body: {placement: 0}});
  }
});

test("pieces painted over one another under the pointer still offer the chooser", () => {
  const h = harness({state: scene(tracks(), 5), events: true});
  h.run("view = {x: 0, y: 0, scale: 1}; canvas.clientWidth = 1000; canvas.clientHeight = 500");
  const [x, y] = h.run("worldToScreen(0, 0)");
  assert.deepEqual(json(h.run(`placementsAt(${x}, ${y}).map(hit => hit.placement)`)), [0, 1]);
});
