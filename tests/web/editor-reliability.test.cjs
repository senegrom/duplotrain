"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const vm = require("node:vm");
const {loadEditor} = require("./editor-harness.cjs");

function scene(placements = [], revision = 1) {
  return {revision, layout: {placements, closed: false, exactly_closed: false,
    joint_issues: [], size_cm: [20, 20]}, open_ends: [], matable: [], candidates: [],
    can_undo: false, can_redo: false, sets: [], palette: [],
    inventory: {owned: {straight: 17}, remaining: {straight: 17}, unlimited: false},
    stones: {catalog: {}, owned: {stone_stop: 2}, remaining: {stone_stop: 2}},
    snapshot: {format: "duplotrain-session/1", inventory: {straight: 17},
      stones: {stone_stop: 2}, unlimited: false, layout: {format: "duplotrain-layout/1", placements: []}}};
}
function track(line, name = "track") {
  return {name, width: 40, lines: [line], ports: [], mid: line[0], stone_marks: []};
}
function harness({state = scene(), events = false, schedule = false, overrides = {}} = {}) {
  const elements = new Map(), calls = [], notices = [], windowEvents = {}, frames = [], intervals = new Map();
  const saved = new Map();
  class Element {
    constructor(tag = "div") {
      this.tag = tag; this.children = []; this.listeners = {}; this.dataset = {}; this.style = {};
      this.attributes = {}; this._value = ""; this.textContent = ""; this.disabled = false; this.hidden = false;
      this.classList = {toggle() {}, add() {}, remove() {}};
      this.clientWidth = 500; this.clientHeight = 500;
    }
    set value(v) { this._value = String(v); }
    get value() { return this._value || (this.tag === "select" ? this.children[0]?.value || "" : ""); }
    append(...children) { this.children.push(...children); }
    replaceChildren(...children) { this.children = children; this._value = ""; }
    setAttribute(k, v) { this.attributes[k] = String(v); }
    addEventListener(event, action) { this.listeners[event] = action; }
    click() { if (!this.disabled) return this.listeners.click?.({target: this}); }
    focus() { context.document.activeElement = this; }
    closest() { return null; }
    getBoundingClientRect() { return {left: 0, top: 0}; }
  }
  const el = id => {
    if (!elements.has(id)) elements.set(id, new Element(id.includes("select") || id === "train-start" || id === "project-slots" ? "select" : "div"));
    return elements.get(id);
  };
  const context = vm.createContext({
    S: state, fitted: true, pickMode: null, armed: null, preview: null, view: {x: 0, y: 0, scale: 1},
    window: {addEventListener(name, fn) { windowEvents[name] = fn; }},
    document: {getElementById: el, createElement: tag => new Element(tag),
      body: new Element("body"), addEventListener() {}},
    location: {pathname: "/test/"}, navigator: {},
    localStorage: {get length() { return saved.size; }, key(i) { return [...saved.keys()][i]; },
      getItem(k) { return saved.get(k) ?? null; }, setItem(k, v) { saved.set(k, String(v)); }},
    crypto: {randomUUID: () => `project-${saved.size + 1}`},
    status: (text, kind) => notices.push({text, kind}),
    api: async (path, body) => { calls.push({path, body}); return state; },
    requestAnimationFrame(fn) { frames.push(fn); },
    setInterval(fn) { const id = Symbol(); intervals.set(id, fn); return id; },
    clearInterval(id) { intervals.delete(id); },
    saveSession() {}, ...(schedule ? {} : {draw() {}}), ...overrides,
  });
  loadEditor(context, {events});
  const run = code => vm.runInContext(code, context);
  el("max-pieces").value = 26; el("slop").value = 0; el("reversing").checked = false;
  return {context, run, el, calls, notices, saved, intervals, frames, windowEvents, Element};
}

for (const mutation of ["import", "undo", "inventory", "restore"]) {
  test(`${mutation} revision invalidates index selections, not persistent armed tools`, () => {
    const h = harness();
    h.run('discardStaleInteraction(); selectTool({pick: {stage:"close",grow:[0,1]}}); armed = {piece:"straight"};');
    assert.equal(h.context.pickMode.revision, 1);
    h.context.S = scene([], 2); h.run("redraw()");
    assert.equal(h.context.pickMode, null);
    assert.equal(h.context.armed.piece, "straight");
    assert.equal(h.run("trainTrace"), null);
  });
}

test("stale endpoint is rejected even before the next redraw", async () => {
  const s = scene(); s.open_ends = [[0, 0], [0, 1]];
  const h = harness({state: s});
  h.run('selectTool({pick: {stage:"close",grow:[0,1]}}); S.revision++');
  await h.run("activateEnd([0,0])");
  assert.equal(h.calls.length, 0);
  assert.equal(h.context.pickMode, null);
  assert.match(h.notices.at(-1).text, /again/);
});

for (const [key, ctrl, meta, shift, path] of [
  ["z", true, false, false, "/api/undo"], ["z", true, false, true, "/api/redo"],
  ["Z", false, true, true, "/api/redo"], ["y", true, false, false, "/api/redo"],
]) test(`keyboard ${ctrl ? "ctrl" : "cmd"}+${shift ? "shift+" : ""}${key} chooses ${path}`, async () => {
  const h = harness({events: true, overrides: {redraw() {}}});
  h.windowEvents.keydown({key, ctrlKey: ctrl, metaKey: meta, shiftKey: shift,
    target: {closest: () => false}, preventDefault() {}});
  await new Promise(resolve => setImmediate(resolve));
  assert.deepEqual(h.calls.map(c => c.path), [path]);
});

test("editing a text input never invokes global history shortcuts", () => {
  const h = harness({events: true});
  h.windowEvents.keydown({key: "z", ctrlKey: true, shiftKey: true, target: {closest: () => true}});
  assert.equal(h.calls.length, 0);
});

for (const stone of [false, true]) test(`rejected ${stone ? "stone" : "track"} count rolls back, but not a newer draft`, async () => {
  let reject;
  const h = harness({overrides: {api: () => new Promise((_, r) => { reject = r; })}});
  const input = new h.Element("input"); input.value = -1;
  const id = stone ? "stone_stop" : "straight";
  const first = h.context.submitInventory(id, input, stone);
  reject(new Error("invalid")); await first;
  assert.equal(input.value, stone ? "2" : "17");
  input.value = -1;
  const second = h.context.submitInventory(id, input, stone);
  input.value = 123;
  reject(new Error("invalid")); await second;
  assert.equal(input.value, "123");
});

test("new action stone input remains stable during normal redraw", () => {
  const s = scene(); s.stones.catalog = {stone_stop: {name: "Stop stone", effect: "stop", color: "red"}};
  const h = harness({state: s}); h.run("renderStones()");
  const input = h.el("stones").children[0].children[1];
  input.value = 73; input.focus();
  h.run("renderStones()");
  assert.equal(input.value, "73"); assert.equal(h.context.document.activeElement, input);
  assert.equal(input.attributes["aria-label"], "Stop stone owned");
});

test("elevated visible track is picked first regardless of placement order", () => {
  const raised = track([[-100, 0, 120], [100, 0, 120]]);
  const ground = track([[0, -100, 0], [0, 100, 0]]);
  for (const placements of [[raised, ground], [ground, raised]]) {
    const h = harness({state: scene(placements), overrides: {worldToScreen: (x, y) => [x, y]}});
    assert.equal(h.context.placementAt(0, 0), placements.indexOf(raised));
    const segments = h.context.drawingSegments(placements);
    assert.equal(segments.at(-1).placement, placements.indexOf(raised));
  }
});

test("ramps are ordered by local segments, not whole-piece average elevation", () => {
  const ramp = track([[-100, 0, 0], [100, 0, 200]]);
  const level = track([[-150, 0, 100], [150, 0, 100]]);
  const h = harness({state: scene([ramp, level]), overrides: {worldToScreen: (x, y) => [x, y]}});
  assert.equal(h.context.placementAt(-75, 0), 1);
  assert.equal(h.context.placementAt(75, 0), 0);
});

test("same-height ties agree with painter order and segment picking works between samples", () => {
  const h = harness({state: scene([track([[-200, 0, 0], [200, 0, 0]]),
    track([[-200, 0, 0], [200, 0, 0]])]), overrides: {worldToScreen: (x, y) => [x, y]}});
  assert.equal(h.context.placementAt(0, 0), 1);
  assert.equal(h.context.placementsAt(0, 0).length, 2);
  assert.equal(h.context.placementAt(0, 100), null);
});

test("cached world-space rails survive view changes, redraws coalesce into one frame", () => {
  let paints = 0;
  const h = harness({state: scene([track([[0, 0, 0], [100, 0, 0]])]), schedule: true,
    overrides: {paint: () => { paints++; }}});
  const first = h.context.drawingSegments(h.context.S.layout.placements);
  h.context.view = {x: 10, y: 10, scale: 2};
  assert.equal(h.context.drawingSegments(h.context.S.layout.placements), first);
  h.run("draw(); draw(); draw()"); assert.equal(h.frames.length, 1); assert.equal(paints, 0);
  h.frames.shift()(); assert.equal(paints, 1);
  h.run("draw()"); assert.equal(h.frames.length, 1);
});

test("ambiguous removal waits for explicit choice and refuses stale confirmation", async () => {
  const h = harness({state: scene([track([[0, 0, 0], [100, 0, 0]], "Top"),
    track([[0, 0, 0], [100, 0, 0]], "Bottom")]), overrides: {redraw() {}}});
  h.context.showOverlapPicker([{placement: 0, z: 100}, {placement: 1, z: 0}], true);
  const box = h.el("overlap-picker"), select = box.children[1], confirm = box.children[2];
  assert.equal(h.calls.length, 0);
  select.value = 1; select.listeners.change(); await confirm.click();
  assert.equal(h.calls[0].body.placement, 1);
  h.context.showOverlapPicker([{placement: 0, z: 100}], true);
  h.context.S.revision++;
  await box.children[2].click(); assert.equal(h.calls.length, 1);
});

test("keyboard endpoint activation uses exact selected indices, never another coincident endpoint", async () => {
  const s = scene(); s.open_ends = [[0, 0], [1, 0]];
  const h = harness({state: s, overrides: {redraw() {}}});
  h.run('selectTool({piece:{piece:"straight",entry:0}})');
  await h.context.activateEnd([1, 0]);
  assert.deepEqual(JSON.parse(JSON.stringify(h.calls[0].body.at)), [1, 0]);
});

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

test("diagnostic reports use literal text and their highlights expire by revision", async () => {
  let focused = null;
  const report = {revision: 1, connector_closed: true, open_ends: [], joint_issues: [],
    overlaps: [[0, 1]], overlap_check_complete: false, missing: [{piece: "curve", name: "<b>curve</b>",
      missing: 22, used: 24, owned: 2, placements: [0]}], provisional: [], sandbox: false, model_note: "model"};
  const h = harness({overrides: {api: async () => report, focusPieces: v => { focused = v; }}});
  await h.run("checkLayout()"); const rows = h.el("diagnostics").children;
  assert.ok(rows.some(r => /incomplete|limited|first 200/i.test(r.textContent)));
  const missing = rows.find(r => r.textContent.includes("<b>curve</b>")); assert.equal(missing.tag, "button");
  await missing.click(); assert.deepEqual(JSON.parse(JSON.stringify(focused)), [0]);
  focused = null; h.context.S.revision++; await missing.click(); assert.equal(focused, null);
});

test("train trace steps, pauses and expires without claiming all starting states", async () => {
  const trace = {revision: 1, outcome: "endless", start: [0, 0], steps: [[0, 0, 1], [1, 0, 1]],
    cycle_start: 0, period: 2, reversals: 0, visited: [0, 1], complete: true};
  const h = harness({events: true, overrides: {api: async () => trace}});
  h.el("train-start").value = "[0,0]";
  await h.run("testTrain()"); assert.match(h.el("train-report").textContent, /not a claim about every start/);
  await h.el("train-step").click(); assert.equal(h.run("trainStep"), 0);
  await h.el("train-play").click(); assert.equal(h.intervals.size, 1);
  await h.el("train-pause").click(); assert.equal(h.intervals.size, 0);
  h.run("discardStaleInteraction(); S.revision++; discardStaleInteraction()");
  assert.equal(h.run("trainTrace"), null); assert.equal(h.el("train-play").disabled, true);
});

test("fit preview includes extension geometry rather than only the current base", async () => {
  let fitted;
  const h = harness({events: true, overrides: {fitView: p => { fitted = p; }}});
  h.context.preview = {placements: [track([[1000, 0, 0], [1200, 0, 0]])]};
  await h.el("fit-preview").click(); assert.equal(fitted[0].lines[0][0][0], 1000);
});

test("compact preview composition and paint batches are reused without crossing revisions", () => {
  const h = harness({state: scene([track([[0, 0, 0], [100, 0, 0]])])});
  const candidate = {format: "duplotrain-preview/1", base_revision: 1, base_count: 1,
    placements: [track([[100, 0, 0], [200, 0, 0]])]};
  const first = h.context.previewPlacements(candidate);
  assert.equal(h.context.previewPlacements(candidate), first);
  assert.equal(h.context.drawingBatches(first).length, 2);
  assert.equal(h.context.drawingBatches(first), h.context.drawingBatches(first));
  h.context.S.revision++;
  assert.equal(h.context.previewPlacements(candidate), null);
});
