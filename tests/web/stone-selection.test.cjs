"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const html = fs.readFileSync(path.join(__dirname, "../../src/duplotrain/static/editor.html"), "utf8");
const positions = html.slice(html.indexOf("function stoneMarkPositions()"), html.indexOf("function placementAt("));
const removal = html.slice(html.indexOf("async function removeAt("), html.indexOf('canvas.addEventListener("contextmenu"'));

function editor(marks) {
  const requests = [], messages = [];
  const state = {layout: {placements: [{
    mid: [64, 0], ports: [{x: 0, y: 0}, {x: 128, y: 0}], stone_marks: marks,
  }]}};
  const context = vm.createContext({
    S: state, apiBusy: false, solving: false, view: {scale: 1},
    worldToScreen: (x, y) => [x, y], placementAt: () => 0,
    redraw() {}, status(message) { messages.push(message); },
    api: async (route, body) => { requests.push({route, body}); return state; },
  });
  vm.runInContext(positions + "\n" + removal, context);
  return {requests, messages, context, run: code => vm.runInContext(code, context)};
}

for (const at of [null, 0, 1]) {
  test(`Remove sends the selected ${at === null ? "midpoint" : "face " + at} marker and removal intent`, async () => {
    const e = editor([null, 0, 1].map(position => ({id: "stone_lights", at: position})));
    await e.run(`const marker = stoneMarkPositions().find(m => m.at_port === ${at}); removeAt(marker.x, marker.y)`);
    assert.equal(e.requests.length, 1);
    assert.equal(e.requests[0].route, "/api/stone");
    assert.equal(e.requests[0].body.placement, 0);
    assert.equal(e.requests[0].body.id, "stone_lights");
    assert.equal(e.requests[0].body.at_port, at);
    assert.equal(e.requests[0].body.remove, true);
    assert.deepEqual(e.messages, []);
  });
}

test("Legacy midpoint markers without at send explicit null", async () => {
  const e = editor([{id: "stone_lights"}]);
  await e.run("const marker = stoneMarkPositions()[0]; removeAt(marker.x, marker.y)");
  assert.equal(e.requests[0].body.at_port, null);
  assert.equal(e.requests[0].body.remove, true);
});

for (const flag of ["apiBusy", "solving"]) {
  test(`Remove ignores clicks while ${flag}`, async () => {
    const e = editor([{id: "stone_lights", at: 0}]);
    e.context[flag] = true;
    await e.run("const marker = stoneMarkPositions()[0]; removeAt(marker.x, marker.y)");
    assert.equal(e.requests.length, 0);
  });
}

test("Remove away from markers still removes the selected piece", async () => {
  const e = editor([]);
  await e.run("removeAt(64, 0)");
  assert.equal(e.requests[0].route, "/api/remove");
  assert.equal(e.requests[0].body.placement, 0);
});
