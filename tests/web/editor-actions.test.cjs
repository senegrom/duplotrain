"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track, paintCalls} = require("./reliability-harness.cjs");

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

test("an armed bridge arch greys the arrows of the ends it cannot join, whichever way it is armed", () => {
  // A bridge ramp alone. Climbing, the arch's foot stands only on a ramp's top;
  // descending, the arch joins by its other end, which is ordinary track.
  const ramp = track([[0, 0, 0], [320, 0, 57.6]], "Bridge ramp (lower part)");
  ramp.ports = [{port: 0, open: true, sealed: false, x: 0, y: 0, deg: 180, name: "low"},
    {port: 1, open: true, sealed: false, x: 320, y: 0, deg: 0, name: "high", kind: "ramp_top"}];
  const state = scene([ramp]);
  state.open_ends = [[0, 0], [0, 1]];
  state.palette = [{id: "span", name: "Bridge arch (upper part)", variants: [
    {entry: 0, exit: 1, label: "↑ climb 19mm", takes: ["ramp_top"]},
    {entry: 1, exit: 0, label: "↓ descend 19mm"}]}];
  state.inventory.owned.span = state.inventory.remaining.span = 1;
  const h = harness({state, events: true, overrides: {devicePixelRatio: 1}});
  h.run("view = {x: 160, y: 0, scale: 1}; renderPalette()");
  const [climb, descend] = h.run("paletteRows[0].buttons").map(row => row.button);
  // The colour of the dot each open end's arrow starts from: the ramp's foot, then its top.
  const arrows = () => {
    const dots = new Map(paintCalls(h).filter(([name]) => name === "arc")
      .map(([, fill, , x, y]) => [`${x},${y}`, fill]));
    return [[0, 0], [320, 0]].map(([x, y]) => dots.get(h.run(`worldToScreen(${x}, ${y})`).join(",")));
  };
  assert.deepEqual(arrows(), ["#d0342c", "#d0342c"]);  // nothing armed: every open end is red
  climb.click();
  assert.deepEqual(arrows(), ["#a7adb3", "#d0342c"]);
  descend.click();
  assert.deepEqual(arrows(), ["#d0342c", "#a7adb3"]);
});

test("track colours count height from the lowest track: a layout raised or lowered as a whole paints alike", () => {
  // A straight on a bridge's crest crosses one on the floor, a crest (76.8 mm) below. Begun
  // up on the crest, at the engine's height zero, the layout lies partly below zero; however
  // high it was begun, its lowest track stands on the floor.
  const painted = dz => paintCalls(harness({state: scene([track([[-64, 0, dz], [64, 0, dz]], "Straight rail"),
    track([[0, -64, dz - 76.8], [0, 64, dz - 76.8]], "Straight rail")]),
    events: true, overrides: {devicePixelRatio: 1}}));
  const begun = painted(0);
  // Painted from the floor up: the floor's grey, then a crest's amber.
  assert.deepEqual(begun.filter(([name]) => name === "fill").map(([, fill]) => fill),
    ["rgb(185,190,196)", "rgb(214,164,76)"]);
  for (const dz of [76.8, -76.8]) assert.deepEqual(painted(dz), begun);
});

test("a joint warning gives the height difference and heading error of the joint that is off", () => {
  // A bridge ramp's top linked to a straight on the floor, turned one 15° step: the
  // warning says by how much the joint is off, so it can be found and fixed.
  const state = scene([track([[0, 0, 0], [320, 0, 57.6]], "Bridge ramp (lower part)"),
    track([[320, 0, 0], [443.64, 33.13, 0]], "Straight rail")]);
  state.open_ends = [[0, 0], [1, 1]];
  state.layout.joint_issues = [{a: [0, 1], b: [1, 0], gap_mm: 0, height_mm: 57.6, heading_error_deg: 15,
    problems: ["elevation mismatch", "heading mismatch", "mismatched bridge joint"]}];
  const h = harness({state});
  h.run("refreshStatus()");
  assert.deepEqual(h.notices.at(-1), {kind: "err", text: "2 open end(s). Incompatible joints. " +
    "1 joint(s) need attention. Joint #1 ↔ #2: elevation mismatch, heading mismatch, " +
    "mismatched bridge joint; height difference 57.60 mm; heading error 15°."});
});
