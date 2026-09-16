"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const html = fs.readFileSync(path.join(__dirname, "../../src/duplotrain/static/editor.html"), "utf8");
const source = html.slice(html.indexOf('el("solve").addEventListener'),
  html.indexOf("// Pointer events support"));

function editor() {
  const elements = new Map(), calls = [];
  const el = id => {
    if (!elements.has(id)) elements.set(id, {
      value: id === "max-pieces" ? "26" : "0", checked: false, hidden: true,
      addEventListener(_event, fn) { this.click = fn; },
    });
    return elements.get(id);
  };
  const context = vm.createContext({el, selectTool() {}, redraw() {}, status() {},
    api: async (url, body) => {
      calls.push(JSON.parse(JSON.stringify({url, body})));
      return {revision: calls.length, candidates: [], complete: false,
        open_ends: [[23, 1], [25, 0]], can_undo: true, stop_reason: "node_limit"};
    }});
  vm.runInContext(`let S = {revision: 0, open_ends: [[23, 1], [25, 0]]};
    let solving = false, apiBusy = false, lastSolve = null;
    let selectedCandidate = null, pickMode = null;\n` + source, context);
  return {el, calls, run: code => vm.runInContext(code, context)};
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
