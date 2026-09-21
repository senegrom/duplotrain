"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness} = require("./reliability-harness.cjs");

function editor(marks) {
  const state = {layout: {placements: [{
    mid: [64, 0], ports: [{x: 0, y: 0}, {x: 128, y: 0}], stone_marks: marks,
  }]}};
  return harness({state, overrides: {
    worldToScreen: (x, y) => [x, y], placementAt: () => 0,
    placementsAt: () => [{placement: 0, d: 0, z: 0}], redraw() {},
  }});
}

for (const at of [null, 0, 1]) {
  test(`Remove sends the selected ${at === null ? "midpoint" : "face " + at} marker and removal intent`, async () => {
    const e = editor([null, 0, 1].map(position => ({id: "stone_lights", at: position})));
    await e.run(`const marker = stoneMarkPositions().find(m => m.at_port === ${at}); removeAt(marker.x, marker.y)`);
    assert.equal(e.calls.length, 1);
    assert.equal(e.calls[0].path, "/api/stone");
    assert.equal(e.calls[0].body.placement, 0);
    assert.equal(e.calls[0].body.id, "stone_lights");
    assert.equal(e.calls[0].body.at_port, at);
    assert.equal(e.calls[0].body.remove, true);
    assert.deepEqual(e.notices, []);
  });
}

test("Legacy midpoint markers without at send explicit null", async () => {
  const e = editor([{id: "stone_lights"}]);
  await e.run("const marker = stoneMarkPositions()[0]; removeAt(marker.x, marker.y)");
  assert.equal(e.calls[0].body.at_port, null);
  assert.equal(e.calls[0].body.remove, true);
});

for (const flag of ["apiBusy", "solving"]) {
  test(`Remove ignores clicks while ${flag}`, async () => {
    const e = editor([{id: "stone_lights", at: 0}]);
    e.run(`${flag} = true`);
    await e.run("const marker = stoneMarkPositions()[0]; removeAt(marker.x, marker.y)");
    assert.equal(e.calls.length, 0);
  });
}

test("Remove away from markers still removes the selected piece", async () => {
  const e = editor([]);
  await e.run("removeAt(64, 0)");
  assert.equal(e.calls[0].path, "/api/remove");
  assert.equal(e.calls[0].body.placement, 0);
});
