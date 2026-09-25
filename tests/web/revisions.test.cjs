"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {randomUUID} = require("node:crypto");
const {harness, scene} = require("./reliability-harness.cjs");

function editor() {
  const calls = [];
  let redraws = 0;
  // The editor's own api() is under test; only its transport is stubbed.
  const h = harness({state: {revision: 7}, omit: ["api"], overrides: {
    redraw: () => { redraws++; },
    fetch: async (url, options) => {
      calls.push({url, options});
      return {ok: true, json: async () => ({revision: 8})};
    },
  }});
  return {context: h.context, calls, classes: h.context.document.body.classes, el: h.el,
    redraws: () => redraws, run: h.run};
}

test("every edit captures its viewed revision for HTTP and worker transports", async () => {
  const paths = ["attach", "join", "undo", "remove", "clear", "inventory", "unlimited",
                 "add_set", "stone", "search/start", "routes/start", "apply", "import", "restore", "redo",
                 "project/open", "check", "drive"];
  for (const transport of ["http", "worker"]) {
    const e = editor();
    if (transport === "worker") e.context.window.duplotrainApi = async (url, body) => {
      e.calls.push({url, options: {body: JSON.stringify(body)}});
      return {revision: 8};
    };
    for (const name of paths) await e.run(`api("/api/${name}", {placement: 1})`);
    assert.equal(e.calls.length, paths.length);
    for (const {options} of e.calls) assert.deepEqual(JSON.parse(options.body), {revision: 7, placement: 1, preview_format: "duplotrain-preview/1"});
    assert.equal(e.classes.size, 0);
  }
});

test("candidate revision is not silently replaced by the latest viewed revision", async () => {
  const e = editor();
  await e.run('api("/api/apply", {index: 0, revision: 3})');
  assert.deepEqual(JSON.parse(e.calls[0].options.body), {revision: 3, index: 0, preview_format: "duplotrain-preview/1"});
});

test("the read-only state request does not require or inject an edit revision", async () => {
  const e = editor();
  await e.run('api("/api/state")');
  assert.equal(e.calls[0].options.method, "POST");
  assert.deepEqual(JSON.parse(e.calls[0].options.body), {preview_format: "duplotrain-preview/1"});
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
    e.run('deleting = true; armed = {piece:"straight"}; selectedCandidate = "old"; preview = {};');
    await assert.rejects(e.run('api("/api/remove", {placement: 1})'), /not applied/);
    assert.equal(e.calls.length, 1);
    assert.equal(e.run("S.revision"), 9);
    assert.equal(e.run("S.layout.placements[1].piece"), "switch");
    assert.equal(e.run("deleting"), false);
    for (const name of ["armed", "armedStone", "pickMode", "selectedCandidate", "preview"])
      assert.equal(e.run(name), null);
    assert.equal(e.redraws(), 1);  // which renders the job controls afresh
    assert.equal(e.run("apiBusy"), false);
    assert.equal(e.classes.size, 0);
  });
}

test("every edit also names the engine instance it acted on", async () => {
  const calls = [];
  const h = harness({state: {revision: 7, instance: "a1"}, omit: ["api"], overrides: {
    fetch: async (url, options) => { calls.push(JSON.parse(options.body)); return {ok: true, json: async () => ({revision: 8})}; },
  }});
  await h.run('api("/api/remove", {placement: 1})');
  await h.run('api("/api/state")');
  assert.deepEqual(calls[0], {revision: 7, instance: "a1", placement: 1, preview_format: "duplotrain-preview/1"});
  assert.deepEqual(calls[1], {preview_format: "duplotrain-preview/1"});
});

function restartedEngine(restore) {
  const confirmed = {format: "duplotrain-session/1", layout: {placements: [{piece: "curve"}]}};
  const empty = {format: "duplotrain-session/1", layout: {placements: []}};
  const calls = [];
  let redraws = 0;
  const h = harness({state: {revision: 5, instance: "old", snapshot: confirmed}, omit: ["api"], overrides: {
    redraw: () => { redraws++; },
    fetch: async (url, options) => {
      const body = JSON.parse(options.body);
      calls.push({url, body});
      const reply = url === "/api/restore" ? restore(body) :
        {status: 409, data: {error: "Your action was not applied", code: "stale_revision",
          state: {revision: 0, instance: "new", snapshot: empty}}};
      return {ok: reply.status === 200, status: reply.status, json: async () => reply.data};
    },
  }});
  return {h, calls, confirmed, redraws: () => redraws};
}

test("a restarted engine receives this tab's confirmed session instead of emptying it", async () => {
  const e = restartedEngine(body => ({status: 200, data: {revision: 1, instance: "new", snapshot: body.data}}));
  e.h.run('pickMode = {stage: "grow"}; selectedCandidate = "5:0";');
  await assert.rejects(e.h.run('api("/api/remove", {placement: 0})'), /session was restored/);
  assert.deepEqual(e.calls.map(c => c.url), ["/api/remove", "/api/restore"]);
  assert.deepEqual(e.calls[1].body, {data: e.confirmed, revision: 0, instance: "new",
    preview_format: "duplotrain-preview/1"});
  assert.equal(e.h.run("S.instance"), "new");
  assert.deepEqual(e.h.run("S.snapshot"), e.confirmed);
  assert.equal(e.h.run("pickMode"), null);
  assert.equal(e.h.run("selectedCandidate"), null);
  assert.equal(e.redraws(), 1);
  assert.equal(e.h.run("apiBusy"), false);
});

test("a failed restore keeps this tab's session rather than adopting the empty engine", async () => {
  const e = restartedEngine(() => ({status: 409, data: {error: "invalid snapshot"}}));
  await assert.rejects(e.h.run('api("/api/remove", {placement: 0})'), /restoring this tab's session failed/);
  assert.equal(e.h.run("S.instance"), "old");
  assert.deepEqual(e.h.run("S.snapshot"), e.confirmed);
  assert.equal(e.redraws(), 0);
});

test("another tab's restore into the new engine is adopted like any conflict", async () => {
  const theirs = {revision: 1, instance: "new", snapshot: {format: "duplotrain-session/1", layout: {placements: []}}};
  const e = restartedEngine(() => ({status: 409, data: {error: "stale", code: "stale_revision", state: theirs}}));
  await assert.rejects(e.h.run('api("/api/remove", {placement: 0})'), /not applied/);
  assert.equal(e.h.run("S.revision"), 1);
  assert.equal(e.h.run("S.instance"), "new");
  assert.equal(e.redraws(), 1);
});

// Tabs of one origin on one local server whose session is a list of piece ids;
// the server can restart empty, counting revisions from 0 in a new instance.
function localServerTabs() {
  const values = new Map();
  const storage = {get length() { return values.size; }, key: i => [...values.keys()][i],
    getItem: k => values.get(k) ?? null, setItem: (k, v) => values.set(k, String(v)),
    removeItem: k => values.delete(k)};
  let queue = Promise.resolve();
  const locks = {request(_name, callback) { const p = queue.then(callback); queue = p.catch(() => {}); return p; }};
  const server = {instance: "A", revision: 0, pieces: []};
  const snapshotOf = pieces => ({format: "duplotrain-session/1", inventory: {straight: 20}, stones: {},
    unlimited: false, layout: {format: "duplotrain-layout/1", placements: pieces.map(piece => ({piece}))}});
  const stateOf = () => {
    const state = scene(server.pieces.map((name, i) => ({name, width: 40, ports: [], stone_marks: [],
      lines: [[[i * 200, 0, 0], [i * 200 + 128, 0, 0]]], mid: [i * 200 + 64, 0]})), server.revision);
    return JSON.parse(JSON.stringify({...state, instance: server.instance,
      snapshot: snapshotOf(server.pieces), train_switches: []}));
  };
  const api = async (path, body) => {
    await new Promise(resolve => setImmediate(resolve));
    if (path === "/api/state") return stateOf();
    if (body.revision !== server.revision || (body.instance ?? server.instance) !== server.instance) {
      const error = new Error("The session changed in another tab. Your action was not applied.");
      error.code = "stale_revision"; error.state = stateOf(); throw error;
    }
    if (path === "/api/restore") server.pieces = body.data.layout.placements.map(p => p.piece);
    else if (path === "/api/attach") server.pieces = [...server.pieces, body.piece];
    server.revision++;
    return stateOf();
  };
  const settle = async () => { for (let i = 0; i < 20; i++) await new Promise(resolve => setImmediate(resolve)); };
  const open = async () => {
    const h = harness({state: null, events: true, omit: ["api", "saveSession"], overrides: {
      localStorage: storage, navigator: {locks}, crypto: {randomUUID},
      setTimeout: fn => { fn(); return 1; }, location: {pathname: "/"}}});
    h.context.window.duplotrainApi = api;
    await h.run("refresh()"); await settle();
    return {h, shown: () => h.context.S.layout.placements.map(p => p.name).join(","),
      async attach(piece) {
        h.context.piece = piece;
        try { await h.run("(async () => { S = await api('/api/attach', {piece, entry: 0, at: null}); redraw(); })()"); }
        catch (error) { await settle(); return error.message; }
        await settle(); return "ok";
      }};
  };
  const saved = () => JSON.parse(storage.getItem("duplotrain-session/2:/")).snapshot.layout.placements
    .map(p => p.piece).join(",");
  return {server, open, saved};
}

test("after a server restart a stale tab restores the newest autosave, not its older view", async () => {
  const {server, open, saved} = localServerTabs();
  const newer = await open();
  await newer.attach("curve");
  const stale = await open();                       // sees only the curve, then stays idle
  await newer.attach("straight"); await newer.attach("bridge");
  assert.equal(stale.shown(), "curve"); assert.equal(saved(), "curve,straight,bridge");
  // A trace the stale tab made on its revision 1 of the old engine.
  stale.h.run("trainTrace = {revision: S.revision, steps: [[0, 0, 1]], start: [0, 0], terminal: null, cycle_start: 0}");
  Object.assign(server, {instance: "B", revision: 0, pieces: []});   // the server restarts
  assert.match(await stale.attach("switch"), /another tab saved last was restored/);
  assert.equal(server.pieces.join(","), "curve,straight,bridge");
  // The restore is revision 1 of the new engine, the very number the stale tab
  // showed: only the restart itself says its selectors and trace belong elsewhere.
  assert.equal(stale.h.context.S.revision, 1);
  assert.deepEqual(stale.h.el("piece-select").children.map(o => o.textContent),
    ["#1 curve", "#2 straight", "#3 bridge"]);
  assert.equal(stale.h.run("trainTrace"), null);
  assert.match(await newer.attach("switch"), /not applied/);
  assert.equal(newer.shown(), "curve,straight,bridge");
  assert.equal(saved(), "curve,straight,bridge");
  const fresh = await open();
  assert.equal(fresh.shown(), "curve,straight,bridge"); assert.equal(saved(), "curve,straight,bridge");
});

test("after a server restart the tab that saved last restores its own session", async () => {
  const {server, open, saved} = localServerTabs();
  const tab = await open();
  await tab.attach("curve"); await tab.attach("straight");
  Object.assign(server, {instance: "B", revision: 0, pieces: []});
  assert.match(await tab.attach("bridge"), /this tab's last confirmed session was restored/);
  assert.equal(server.pieces.join(","), "curve,straight"); assert.equal(saved(), "curve,straight");
});

test("a state from another engine at the same revision number rebuilds revision-bound selectors", async () => {
  const piece = (name, x) => ({name, width: 40, lines: [[[x, 0, 0], [x + 128, 0, 0]]], mid: [x + 64, 0],
    stone_marks: [], ports: [{port: 0, name: "a", x, y: 0, deg: 180, open: true, sealed: false},
      {port: 1, name: "b", x: x + 128, y: 0, deg: 0, open: true, sealed: false}]});
  const state = (instance, names) => ({...scene(names.map((n, i) => piece(n, i * 300)), 3), instance,
    open_ends: [], train_switches: []});
  const other = state("B", ["bridge ramp", "curve", "straight"]);
  const h = harness({state: state("A", ["curve", "straight", "bridge ramp"]), events: true, omit: ["api"],
    overrides: {setTimeout: fn => { fn(); return 1; }}});
  h.context.window.duplotrainApi = async () => {
    const error = new Error("The session changed in another tab."); error.code = "stale_revision";
    error.state = other; throw error;
  };
  h.run("redraw()"); h.el("piece-select").value = "1";
  h.run("trainTrace = {revision: 3, steps: [[2, 0, 1]], start: [2, 0], terminal: null, cycle_start: 0}");
  await h.run("checkLayout()");
  assert.equal(h.context.S.instance, "B");
  assert.deepEqual(h.el("piece-select").children.map(o => o.textContent),
    ["#1 bridge ramp", "#2 curve", "#3 straight"]);
  assert.equal(h.run("trainTrace"), null);
});

test("a tab that restored another tab's newer autosave keeps autosaving its own edits", async () => {
  const {server, open, saved} = localServerTabs();
  const newer = await open();
  await newer.attach("curve");
  const stale = await open();
  await newer.attach("straight");
  Object.assign(server, {instance: "B", revision: 0, pieces: []});   // the server restarts
  assert.match(await stale.attach("switch"), /another tab saved last was restored/);
  assert.equal(await stale.attach("buffer"), "ok");
  assert.equal(stale.h.run("autosaveReady"), true);
  assert.equal(saved(), "curve,straight,buffer");
});
