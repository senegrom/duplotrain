"use strict";
// Picks, dialogs and selection: endpoint picks, the overlap chooser and diagnostic
// highlights are bound to the revision and dialog they were made in.
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track} = require("./reliability-harness.cjs");
const json = v => JSON.parse(JSON.stringify(v));
const tracks = () => [track([[-100, 0, 100], [100, 0, 100]], "Top"),
  track([[0, -100, 0], [0, 100, 0]], "Bottom"), track([[1000, 0, 0], [1100, 0, 0]], "Distant")];

test("a new revision invalidates index selections, not persistent armed tools", () => {
  const h = harness();
  h.run('discardStaleInteraction(); selectTool({pick: {stage:"close",grow:[0,1]}}); armed = {piece:"straight"};');
  assert.equal(h.context.pickMode.revision, 1);
  h.context.S = scene([], 2); h.run("redraw()");
  assert.equal(h.context.pickMode, null);
  assert.equal(h.context.armed.piece, "straight");
  assert.equal(h.run("trainTrace"), null);
});

test("stale endpoint is rejected even before the next redraw", async () => {
  const s = scene(); s.open_ends = [[0, 0], [0, 1]];
  const h = harness({state: s});
  h.run('selectTool({pick: {stage:"close",grow:[0,1]}}); S.revision++');
  await h.run("activateEnd([0,0])");
  assert.equal(h.calls.length, 0);
  assert.equal(h.context.pickMode, null);
  assert.match(h.notices.at(-1).text, /again/);
});

test("an open end clicked with no tool joins the end it meets; one meeting nothing asks for a piece", async () => {
  // Two straights whose ends meet unlinked, as where a loop comes round to its start.
  const first = track([[0, 0, 0], [128, 0, 0]], "First"), last = track([[128, 0, 0], [256, 0, 0]], "Last");
  first.ports = [{port: 0, open: true, sealed: false, x: 0, y: 0, deg: 180, name: "a"},
    {port: 1, open: true, sealed: false, x: 128, y: 0, deg: 0, name: "b"}];
  last.ports = [{port: 0, open: true, sealed: false, x: 128, y: 0, deg: 180, name: "a"},
    {port: 1, open: true, sealed: false, x: 256, y: 0, deg: 0, name: "b"}];
  const s = scene([first, last]);
  s.open_ends = [[0, 0], [0, 1], [1, 0], [1, 1]]; s.matable = [[[0, 1], [1, 0]]];
  const h = harness({state: s, events: true, overrides: {redraw() {}}});
  h.run("view = {x: 128, y: 0, scale: 1}");
  for (const x of [128, 256]) {
    const [sx, sy] = h.run(`worldToScreen(${x}, 0)`);
    await h.run(`activateAt(${sx}, ${sy})`);
  }
  assert.deepEqual(json(h.calls), [{path: "/api/join", body: {a: [0, 1], b: [1, 0]}}]);
  assert.match(h.notices.at(-1).text, /^Arm a piece/);
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

test("the overlap chooser gives each piece's height above the lowest track", async () => {
  // Begun up on a bridge's crest, a layout lies partly below zero; its lowest track still
  // stands on the floor, 0.0 mm up, whether or not it is one of the pieces clicked. Each
  // piece of tracks() is lowered as given; the click falls where Top and Bottom cross.
  const chooser = async lowered => {
    const crest = tracks().map((t, i) => ({...t,
      lines: t.lines.map(line => line.map(([x, y, z]) => [x, y, z - lowered[i]]))}));
    const h = harness({state: scene(crest), events: true});
    const [x, y] = h.run("worldToScreen(0, 0)");
    await h.run(`activateAt(${x}, ${y})`);
    return h.el("overlap-picker").children[1].children.map(option => option.textContent);
  };
  assert.deepEqual(await chooser([76.8, 76.8, 76.8]), ["#1 Top · 100.0 mm", "#2 Bottom · 0.0 mm"]);
  // With the distant piece a crest lower still, it is on the floor and the crossing a crest up.
  assert.deepEqual(await chooser([76.8, 76.8, 153.6]), ["#1 Top · 176.8 mm", "#2 Bottom · 76.8 mm"]);
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
