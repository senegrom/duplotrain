"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness} = require("./reliability-harness.cjs");

function editor() {
  const calls = [];
  const h = harness({state: {revision: 0, open_ends: [[23, 1], [25, 0]]}, events: true, overrides: {
    selectTool() {}, redraw() {},
    api: async (url, body) => {
      calls.push(JSON.parse(JSON.stringify({url, body})));
      return {revision: calls.length, candidates: [], complete: false,
        open_ends: [[23, 1], [25, 0]], can_undo: true, stop_reason: "node_limit"};
    }}});
  return {el: h.el, calls, run: h.run};
}

test("deeper retries retain endpoints and increase both depth and effort", async () => {
  const e = editor();
  await e.run("runSolve([25, 0], [23, 1])");
  await e.el("expand-search").click();
  await e.el("expand-search").click();
  assert.deepEqual(e.calls.map(c => c.body.search_effort), [1, 2, 4]);
  assert.deepEqual(e.calls.map(c => c.body.max_pieces), [26, 52, 104]);
  for (const {body} of e.calls) {
    assert.deepEqual(body.grow, [25, 0]);
    assert.deepEqual(body.close, [23, 1]);
  }
});

test("at the piece ceiling retries still increase effort without sending depth 256", async () => {
  const e = editor();
  e.el("max-pieces").value = "128";
  await e.run("runSolve(null, null)");
  assert.equal(e.el("expand-search").hidden, false);
  for (let i = 0; i < 4; i++) await e.el("expand-search").click();
  assert.deepEqual(e.calls.map(c => c.body.search_effort), [1, 2, 4, 8, 16]);
  assert.ok(e.calls.every(c => c.body.max_pieces === 128));
  assert.equal(e.el("expand-search").hidden, true);
});

test("a fresh search resets effort and stale retries do not inherit a previous budget", async () => {
  const e = editor();
  await e.run("runSolve(null, null, 8)");
  await e.el("solve").click();
  assert.equal(e.calls.at(-1).body.search_effort, 1);
  await e.run("runSolve(null, null, 8)");
  e.run("S.revision += 1");
  await e.el("expand-search").click();
  assert.equal(e.calls.at(-1).body.search_effort, 1);
});

test("deeper search ignores a double click while a search is already running", async () => {
  const e = editor();
  e.run("solving = true");
  await e.el("expand-search").click();
  assert.equal(e.calls.length, 0);
  assert.equal(e.el("max-pieces").value, "26");
});

test("Close the loop safely ignores clicks before state loads and during another action", async () => {
  const e = editor();
  for (const setup of ["S = null", "S = {open_ends: []}; apiBusy = true", "apiBusy = false; solving = true"]) {
    e.run(setup);
    await e.el("solve").click();
  }
  assert.equal(e.calls.length, 0);
});

test("incomplete searches can be deepened even after suggestions are found", async () => {
  const e = editor();
  e.run(`api = async () => ({revision: 1, candidates: [{index: 0}],
    complete: false, open_ends: [[23, 1], [25, 0]], can_undo: true});`);
  await e.run("runSolve(null, null)");
  assert.equal(e.el("expand-search").hidden, false);
  e.run(`api = async () => ({revision: 2, candidates: [{index: 0}],
    complete: true, open_ends: [[23, 1], [25, 0]], can_undo: true});`);
  await e.run("runSolve(null, null)");
  assert.equal(e.el("expand-search").hidden, true);
});
