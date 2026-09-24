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
