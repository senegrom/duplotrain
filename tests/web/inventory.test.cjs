"use strict";
// Inventory: a rejected count rolls back to the confirmed one unless a newer draft
// was typed meanwhile, and redraws keep focused inputs and their text.
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene} = require("./reliability-harness.cjs");

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
