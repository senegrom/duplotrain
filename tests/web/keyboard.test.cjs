"use strict";
// Keyboard: undo and redo shortcuts outside text inputs, Escape, and endpoint
// activation by the selected indices.
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track} = require("./reliability-harness.cjs");

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

test("Escape disarms whichever tool is armed and drops the selection, hover and chooser", () => {
  const h = harness({state: scene([track([[0, 0, 0], [100, 0, 0]]), track([[0, 0, 0], [100, 0, 0]])]), events: true});
  for (const tool of ['{piece: {piece: "straight", entry: 0}}', '{stone: "stone_stop"}', "{remove: true}",
    '{pick: {stage: "grow", grow: null}}']) {
    h.run(`selectTool(${tool})`);
    h.context.showOverlapPicker([{placement: 0, z: 0}, {placement: 1, z: 0}]);
    h.run("hoveredPiece = 1");
    assert.ok(h.run("armed || armedStone || pickMode || deleting"), tool);
    assert.notEqual(h.run("selectedPiece"), null);
    h.windowEvents.keydown({key: "Escape", target: {closest: () => false}, preventDefault() {}});
    for (const name of ["armed", "armedStone", "pickMode", "selectedPiece", "hoveredPiece"])
      assert.equal(h.run(name), null, `${name} after ${tool}`);
    assert.equal(h.run("deleting"), false);
    assert.equal(h.el("overlap-picker").hidden, true);
  }
});

test("keyboard endpoint activation uses exact selected indices, never another coincident endpoint", async () => {
  const s = scene(); s.open_ends = [[0, 0], [1, 0]];
  const h = harness({state: s, overrides: {redraw() {}}});
  h.run('selectTool({piece:{piece:"straight",entry:0}})');
  await h.context.activateEnd([1, 0]);
  assert.deepEqual(JSON.parse(JSON.stringify(h.calls[0].body.at)), [1, 0]);
});
