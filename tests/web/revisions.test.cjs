"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const vm = require("node:vm");
const path = require("node:path");
const html = fs.readFileSync(path.join(__dirname, "../../src/duplotrain/static/editor.html"), "utf8");
const source = html.split("<script>")[1].split("// ---------- Checkpoint persistence ----------")[0];

function editor() {
  const calls = [], classes = new Set(), elements = new Map();
  let redraws = 0;
  const el = id => {
    if (!elements.has(id)) elements.set(id, {
      hidden: false, classList: {toggle() {}}, setAttribute() {},
    });
    return elements.get(id);
  };
  const context = vm.createContext({
    window: {}, document: {body: {classList: {
      add: name => classes.add(name), remove: name => classes.delete(name),
    }}, getElementById: el}, el,
    redraw: () => { redraws++; },
    fetch: async (url, options) => {
      calls.push({url, options});
      return {ok: true, json: async () => ({revision: 8})};
    },
  });
  vm.runInContext(source, context);
  vm.runInContext("S = {revision: 7};", context);
  return {context, calls, classes, el, redraws: () => redraws,
    run: code => vm.runInContext(code, context)};
}

test("every edit captures its viewed revision for HTTP and worker transports", async () => {
  const paths = ["attach", "join", "undo", "remove", "clear", "inventory", "unlimited",
                 "add_set", "stone", "solve", "apply", "import", "restore"];
  for (const transport of ["http", "worker"]) {
    const e = editor();
    if (transport === "worker") e.context.window.duplotrainApi = async (url, body) => {
      e.calls.push({url, options: {body: JSON.stringify(body)}});
      return {revision: 8};
    };
    for (const name of paths) await e.run(`api("/api/${name}", {placement: 1})`);
    assert.equal(e.calls.length, paths.length);
    for (const {options} of e.calls) assert.deepEqual(JSON.parse(options.body), {revision: 7, placement: 1});
    assert.equal(e.classes.size, 0);
  }
});

test("candidate revision is not silently replaced by the latest viewed revision", async () => {
  const e = editor();
  await e.run('api("/api/apply", {index: 0, revision: 3})');
  assert.deepEqual(JSON.parse(e.calls[0].options.body), {revision: 3, index: 0});
});

test("read-only requests do not require or inject an edit revision", async () => {
  const e = editor();
  await e.run('api("/api/state")');
  await e.run('api("/api/export", {})');
  assert.equal(e.calls[0].options.method, undefined);
  assert.equal(e.calls[1].options.body, "{}");
});

for (const transport of ["http", "worker"]) {
  test(`${transport} conflict refreshes tools and layout but never replays the action`, async () => {
    const e = editor();
    const current = {revision: 9, layout: {placements: [{piece: "curve"}, {piece: "switch"}]}};
    const data = {error: "Your action was not applied", code: "stale_revision", state: current};
    if (transport === "http") e.context.fetch = async (url, options) => {
      e.calls.push({url, options});
      return {ok: false, status: 409, json: async () => data};
    };
    else e.context.window.duplotrainApi = async (url, body) => {
      e.calls.push({url, body});
      throw Object.assign(new Error(data.error), {code: data.code, state: data.state});
    };
    e.run('deleting = true; armed = {piece:"straight"}; selectedCandidate = "old"; preview = {}; lastSolve = {};');
    await assert.rejects(e.run('api("/api/remove", {placement: 1})'), /not applied/);
    assert.equal(e.calls.length, 1);
    assert.equal(e.run("S.revision"), 9);
    assert.equal(e.run("S.layout.placements[1].piece"), "switch");
    assert.equal(e.run("deleting"), false);
    for (const name of ["armed", "armedStone", "pickMode", "selectedCandidate", "preview", "lastSolve"])
      assert.equal(e.run(name), null);
    assert.equal(e.el("expand-search").hidden, true);
    assert.equal(e.redraws(), 1);
    assert.equal(e.run("apiBusy"), false);
    assert.equal(e.classes.size, 0);
  });
}
