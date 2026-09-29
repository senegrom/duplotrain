"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track} = require("./reliability-harness.cjs");

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

for (const flag of ["apiBusy", "jobLoop"]) {
  test(`Remove ignores clicks while ${flag}`, async () => {
    const e = editor([{id: "stone_lights", at: 0}]);
    e.run(`${flag} = true`);
    await e.run("const marker = stoneMarkPositions()[0]; removeAt(marker.x, marker.y)");
    assert.equal(e.calls.length, 0);
  });
}

test("the stone tool clips a stone at the connector face clicked, otherwise mid-piece", async () => {
  const e = editor([]);
  e.run(`Object.assign(S.layout.placements[0], {stone_ok: true, ports: [{port: 0, x: 0, y: 0}, {port: 1, x: 128, y: 0}]});
    armedStone = "stone_stop"`);
  for (const [x, y] of [[3, 2], [125, -4], [64, 10]]) await e.run(`activateAt(${x}, ${y})`);
  assert.deepEqual(e.calls.map(c => [c.path, c.body.placement, c.body.id, c.body.at_port]), [
    ["/api/stone", 0, "stone_stop", 0], ["/api/stone", 0, "stone_stop", 1], ["/api/stone", 0, "stone_stop", null]]);
});

test("Remove away from markers still removes the selected piece", async () => {
  const e = editor([]);
  await e.run("removeAt(64, 0)");
  assert.equal(e.calls[0].path, "/api/remove");
  assert.equal(e.calls[0].body.placement, 0);
});

test("an armed stone or the Remove tool explains itself on a closed layout too", () => {
  const closed = scene([track([[0, 0, 0], [100, 0, 0]])]);
  closed.layout.exactly_closed = true;
  closed.stones.catalog = {stone_direction: {name: "Direction stone"}};
  const h = harness({state: closed});
  h.run('selectTool({stone: "stone_direction"}); refreshStatus()');
  assert.match(h.notices.at(-1).text, /Direction stone armed/);
  h.run("selectTool({remove: true}); refreshStatus()");
  assert.match(h.notices.at(-1).text, /Remove tool/);
  // A closed layout has no end to attach an armed piece to.
  h.run('selectTool({piece: {piece: "straight", pieceName: "Straight", label: "ahead"}}); refreshStatus()');
  assert.match(h.notices.at(-1).text, /Connectors closed/);
});

test("an armed piece says which ends it joins, and a joint warning waits behind the tools", () => {
  const ramp = track([[0, 0, 0], [320, 0, 57.6]], "Bridge ramp");
  ramp.ports = [{port: 0, open: true, sealed: false, x: 0, y: 0, deg: 180, name: "low"},
    {port: 1, open: true, sealed: false, x: 320, y: 0, deg: 0, name: "high", kind: "ramp_top"}];
  const h = harness({state: scene([ramp])});
  h.run('selectTool({piece: {piece: "span", pieceName: "Bridge arch", label: "climb", takes: ["ramp_top"]}})');
  h.run("refreshStatus()");
  assert.match(h.notices.at(-1).text, /Click a red arrow to attach/);
  h.context.S.layout.placements[0].ports[1].open = false;  // the ramp's top is taken
  h.run("refreshStatus()");
  assert.match(h.notices.at(-1).text, /No open end takes it: it joins only a ramp's top\./);
  h.context.S.layout.joint_issues = [{a: [0, 1], b: [1, 0], gap_mm: 0, height_mm: 0,
    heading_error_deg: 0, problems: ["mismatched bridge joint"]}];
  h.run("refreshStatus()");
  assert.match(h.notices.at(-1).text, /Bridge arch — climb armed/);
  h.run("selectTool(); refreshStatus()");
  assert.match(h.notices.at(-1).text, /Joint #1 ↔ #2: mismatched bridge joint\.$/);
});
