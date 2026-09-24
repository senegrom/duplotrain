"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const vm = require("node:vm");
const {loadEditor} = require("./editor-harness.cjs");
const {harness, scene, track} = require("./reliability-harness.cjs");

function editor() {
  const context = vm.createContext({});
  loadEditor(context);
  return context;
}

const base = [{width: 64, lines: [[[0, 0, 0], [128, 0, 0]]]},
  {width: 64, lines: [[[128, 0, 0], [256, 0, 0]]]}];
const extra = {width: 64, lines: [[[256, 0, 0], [384, 0, 0]]]};
const state = {revision: 9, layout: {placements: base}};
const preview = {format: "duplotrain-preview/1", base_revision: 9, base_count: 2,
  placements: [extra]};
const plain = value => JSON.parse(JSON.stringify(value));

test("compact ghosts compose shared base and additions without mutating either", () => {
  const result = editor().previewPlacements(preview, state);
  assert.deepEqual(plain(result), [...base, extra]);
  assert.equal(result[0], base[0]);
  assert.equal(result[2], extra);
  result.pop();
  assert.equal(state.layout.placements.length, 2);
  assert.equal(preview.placements.length, 1);
});

test("legacy previews remain displayable", () => {
  const full = {placements: [...base, extra]};
  assert.equal(editor().previewPlacements(full, state), full.placements);
});

test("geometry fallback displays only the complete candidate drawing", () => {
  const fallback = {...preview, base_count: 0, placements: [extra]};
  assert.deepEqual(plain(editor().previewPlacements(fallback, state)), [extra]);
});

// A stale base revision is covered with the composition cache at the end of this file.
for (const [name, changes] of [
  ["unknown version", {format: "future"}],
  ["too many base pieces", {base_count: 3}], ["negative count", {base_count: -1}],
  ["fractional count", {base_count: 1.5}], ["boolean count", {base_count: true}],
  ["missing drawing", {placements: null}],
]) {
  test(`reject ${name} instead of compositing an incorrect ghost`, () => {
    assert.equal(editor().previewPlacements({...preview, ...changes}, state), null);
  });
}

test("null preview or absent state draws nothing", () => {
  const c = editor();
  assert.equal(c.previewPlacements(null, state), null);
  assert.equal(c.previewPlacements(preview, null), null);
});

test("independent candidates share base geometry but not each other's additions", () => {
  const c = editor();
  const a = c.previewPlacements(preview, state);
  const b = c.previewPlacements({...preview, placements: []}, state);
  assert.equal(a.length, 3);
  assert.equal(b.length, 2);
  assert.equal(a[0], b[0]);
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
