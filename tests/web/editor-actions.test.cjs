"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness} = require("./reliability-harness.cjs");

function state(revision, piece = "straight", unlimited = false) {
  const layout = {format: "duplotrain-layout/1", placements: [{piece}], links: [], accessories: []};
  return {revision, snapshot: {layout}, layout: {...layout, joint_issues: []},
    palette: [], inventory: {unlimited}};
}

function editor(transport = "http") {
  const calls = [], downloads = [], messages = [];
  let current = state(7);
  const dispatch = (url, body) => {
    calls.push({url, body});
    if (body.revision !== current.revision) throw Object.assign(new Error("Your action was not applied"), {
      code: "stale_revision", state: current,
    });
    current = url === "/api/unlimited" ? state(current.revision + 1, "straight", body.on) :
      state(current.revision + 1, body.data.placements[0].piece);
    return current;
  };
  // The editor's own api() is under test; only its transport is stubbed.
  const h = harness({state: current, events: true, omit: ["api"], overrides: {
    Blob, status: message => messages.push(message),
    URL: {createObjectURL(blob) { downloads.push(blob); return "blob:layout"; }, revokeObjectURL() {}},
    fetch: async (url, options) => {
      try {
        const data = dispatch(url, options.body && JSON.parse(options.body));
        return {ok: true, json: async () => data};
      } catch (error) {
        return {ok: false, json: async () => ({...error, error: error.message})};
      }
    },
  }});
  h.context.redraw = () => h.run("renderPalette()");
  if (transport === "worker") h.context.window.duplotrainApi = async (url, body) => dispatch(url, body);
  h.run("renderPalette();");
  return {context: h.context, el: h.el, calls, downloads, messages,
    server: value => { current = value; }, run: h.run,
    import(file) { h.el("importfile").files = [file]; return h.el("importfile").fire("change"); },
  };
}

function file(piece) {
  const {promise, resolve, reject} = Promise.withResolvers();
  return {name: piece + ".json", size: 100, text: () => promise,
    finish: () => resolve(JSON.stringify(state(0, piece).snapshot.layout)), resolve, reject};
}

// Export asks no engine, whichever the transport: it writes the displayed layout.
test("export preserves the displayed layout when another tab changes the engine", async () => {
  const e = editor("http");
  const displayed = JSON.parse(e.run("JSON.stringify(S.snapshot.layout)"));
  e.server(state(8, "curve"));
  await e.el("export").fire("click");
  assert.equal(e.downloads.length, 1);
  assert.deepEqual(JSON.parse(await e.downloads[0].text()), displayed);
  assert.equal(e.calls.length, 0);
});

for (const transport of ["http", "worker"]) {
  test(`${transport} a slower earlier import cannot replace the latest file selection`, async () => {
    const e = editor(transport), first = file("straight"), latest = file("curve");
    const pending = e.import(first), chosen = e.import(latest);
    latest.finish(); await chosen;
    first.finish(); await pending;
    assert.equal(e.run("S.layout.placements[0].piece"), "curve");
    assert.equal(e.calls.length, 1);
    assert.equal(e.calls[0].body.revision, 7);
  });

  for (const location of ["this tab", "another tab"]) {
    test(`${transport} a pending import cannot overwrite edits in ${location}`, async () => {
      const e = editor(transport), incoming = file("curve"), pending = e.import(incoming);
      e.server(state(8, "switch"));
      if (location === "this tab") e.run('S.revision = 8; S.layout.placements = [{piece: "switch"}];');
      incoming.finish(); await pending;
      assert.equal(e.calls[0].body.revision, 7);
      assert.equal(e.run("S.layout.placements[0].piece"), "switch");
      assert.equal(e.run("S.revision"), 8);
      assert.match(e.messages.at(-1), /not applied/);
    });
  }

  for (const unlimited of [false, true]) {
    test(`${transport} sandbox checkbox matches refreshed state (${unlimited}) after a conflict`, async () => {
      const e = editor(transport);
      e.server(state(8, "straight", unlimited));
      e.el("unlimited").checked = true;
      await e.el("unlimited").fire("change");
      assert.equal(e.el("unlimited").checked, unlimited);
      assert.equal(e.run("S.inventory.unlimited"), unlimited);
      assert.match(e.messages.at(-1), /not applied/);
    });
  }
}

test("export still works when the backend is unavailable", async () => {
  const e = editor();
  e.context.fetch = async () => { throw new Error("offline"); };
  await e.el("export").fire("click");
  assert.equal(e.downloads.length, 1);
  assert.equal(JSON.parse(await e.downloads[0].text()).placements[0].piece, "straight");
});

test("export before state loads reports an error without downloading undefined", async () => {
  const e = editor(); e.run("S = null");
  await e.el("export").fire("click");
  assert.equal(e.downloads.length, 0);
  assert.match(e.messages.at(-1), /loading/i);
});

for (const failure of ["invalid JSON", "read error"]) {
  test(`a superseded import's ${failure} cannot replace the latest status`, async () => {
    const e = editor(), first = file("straight"), latest = file("curve");
    const pending = e.import(first), chosen = e.import(latest);
    latest.finish(); await chosen;
    const message = e.messages.at(-1);
    if (failure === "read error") first.reject(new Error("unreadable"));
    else first.resolve("{");
    await pending;
    assert.equal(e.messages.at(-1), message);
  });
}

for (const invalid of ["oversize", "invalid JSON"]) {
  test(`selecting an ${invalid} file also cancels an older pending import`, async () => {
    const e = editor(), first = file("curve"), pending = e.import(first);
    await e.import({size: invalid === "oversize" ? 3 * 1024 * 1024 : 1, text: async () => "{"});
    const message = e.messages.at(-1);
    first.finish(); await pending;
    assert.equal(e.calls.length, 0);
    assert.equal(e.run("S.revision"), 7);
    assert.equal(e.messages.at(-1), message);
  });
}

test("sandbox checkbox returns to the viewed value after a network failure", async () => {
  const e = editor();
  e.context.fetch = async () => { throw new Error("offline"); };
  e.el("unlimited").checked = true;
  await e.el("unlimited").fire("change");
  assert.equal(e.el("unlimited").checked, false);
  assert.equal(e.run("S.inventory.unlimited"), false);
  assert.equal(e.messages.at(-1), "offline");
});

test("a search re-enables redo when the server kept the redo stack", async () => {
  const {scene, track} = require("./reliability-harness.cjs");
  const before = {...scene([track([[0, 0, 0], [100, 0, 0]])], 5), can_undo: true, can_redo: true,
    open_ends: [[0, 0], [0, 1]]};
  const done = {job_id: "job", revision: 5, status: "exhausted", stage: "full inventory", searched: 12,
    found: 0, page: 0, candidates: [], complete: true, resumable: false, can_harden: false};
  const api = async path => path.endsWith("/start") ? done :
    {...before, revision: 6, search_job: {...done, revision: 6}};
  const h = harness({state: before, overrides: {api}});
  h.context.__c = h.el("canvas"); h.run("canvas = __c");
  await h.run("startInteractiveSearch(null, null)");
  assert.equal(h.el("redo").disabled, false);
  assert.equal(h.el("undo").disabled, false);
});

test("opening a project records it as opened even with invalid local search fields", async () => {
  const {scene, track} = require("./reliability-harness.cjs");
  const opened = {...scene([track([[0, 0, 0], [100, 0, 0]])], 4),
    project: {name: "Recovered session", preferences: {}}};
  const h = harness({state: scene([], 3), overrides: {api: async () => opened}});
  h.context.__c = h.el("canvas"); h.run("canvas = __c");
  h.el("max-pieces").value = "";
  const session = {format: "duplotrain-session/1", layout: {placements: []}, inventory: {}, stones: {}, unlimited: false};
  await h.run("openProject")(session);
  assert.equal(h.notices.at(-1).text, "Opened project: Recovered session");
  assert.notEqual(h.run("projectBaseline"), null);
  assert.match(h.el("project-status").textContent, /settings are invalid/);
});

test("a sideways wheel swipe does not zoom", () => {
  const e = editor();
  const before = e.run("view.scale");
  e.el("canvas").fire("wheel", {deltaX: 40, deltaY: 0, clientX: 10, clientY: 10, preventDefault() {}});
  assert.equal(e.run("view.scale"), before);
  e.el("canvas").fire("wheel", {deltaX: 0, deltaY: 40, clientX: 10, clientY: 10, preventDefault() {}});
  assert.ok(e.run("view.scale") < before);
});

test("a wheel zooms by the distance scrolled, however it is split up", () => {
  const zoom = (...events) => {
    const e = editor(), before = e.run("view.scale");
    for (const [deltaY, deltaMode = 0, ctrlKey = false] of events) e.el("canvas").fire("wheel",
      {deltaX: 0, deltaY, deltaMode, ctrlKey, clientX: 10, clientY: 10, preventDefault() {}});
    return e.run("view.scale") / before;
  };
  const same = (a, b) => assert.ok(Math.abs(a - b) < 1e-9, `${a} != ${b}`);
  same(zoom(...Array(20).fill([4])), zoom([80]));  // a trackpad's steps, one scroll
  same(zoom([100]), 1 / 1.12);  // a mouse notch
  same(zoom([3, 1]), zoom([99]));  // three lines: a notch as some browsers count it
  same(zoom([1000]), zoom([100]));  // no one event beyond a notch
  // A trackpad pinch is ctrl+wheel with deltaY = -100 ln(scale): it zooms by its scale.
  same(zoom(...Array(10).fill([-100 * Math.log(2) / 10, 0, true])), 2);
});

test("a Safari trackpad pinch zooms by its gesture scale, a touch pinch by its pointers only", () => {
  const e = editor(), before = e.run("view.scale");
  const gesture = (type, scale) => e.el("canvas").fire(type,
    {scale, clientX: 10, clientY: 10, preventDefault() {}});
  gesture("gesturestart", 1); gesture("gesturechange", 1.5); gesture("gesturechange", 2);
  assert.ok(Math.abs(e.run("view.scale") / before - 2) < 1e-9);
  e.run("pointers.set(1, {x: 0, y: 0}); pointers.set(2, {x: 50, y: 50})");
  gesture("gesturestart", 1); gesture("gesturechange", 1.5);
  assert.ok(Math.abs(e.run("view.scale") / before - 2) < 1e-9);
});

test("Fit preview without a preview says what it needs", () => {
  const e = editor();
  e.el("fit-preview").fire("click");
  assert.match(e.messages.at(-1), /Preview a suggestion first/);
});

test("fitting keeps to the zoom range, so zooming out never zooms in", () => {
  const e = editor();
  e.run("fitView([{lines: [[[0, 0], [20000, 0]]]}])");
  assert.equal(e.run("view.scale"), 0.08);
});

test("a paint keeps the canvas store at its CSS size times the pixel ratio", () => {
  const e = editor();
  e.context.devicePixelRatio = 2;
  e.run("ctx = {setTransform() {}, clearRect() {}}; S = null; canvas.width = 0; paint()");
  assert.deepEqual([e.run("canvas.width"), e.run("canvas.height")], [1000, 1000]);
  e.context.devicePixelRatio = 1.5;  // another monitor: no element resizes
  e.run("paint()");
  assert.equal(e.run("canvas.width"), 750);
});

test("a canvas resize repaints at once, not a frame later", () => {
  let observed;
  const h = harness({events: true, overrides: {devicePixelRatio: 2,
    ResizeObserver: class { constructor(callback) { observed = callback; } observe() {} },
    window: {addEventListener() {}, ResizeObserver: true}}});
  h.run("ctx = {setTransform() {}, clearRect() {}}; S = null; canvas.width = 0");
  observed();
  assert.equal(h.run("canvas.width"), 1000);
});

test("every paint starts from butt caps, whatever a highlight left behind", () => {
  const e = editor();
  e.context.devicePixelRatio = 1;
  e.run('ctx = {setTransform() {}, clearRect() {}, lineCap: "round"}; S = null; paint()');
  assert.equal(e.run("ctx.lineCap"), "butt");
});
