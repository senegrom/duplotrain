"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track} = require("./reliability-harness.cjs");

test("project status compares snapshot and settings without re-encoding a large string", () => {
  const h = harness();
  h.run(`S.snapshot.large = "x".repeat(200000); markProjectSaved(projectSnapshot());
    var encodedLargeStrings = 0, stringifies = 0, stringify = JSON.stringify;
    JSON.stringify = function(value, ...args) {
      stringifies++;
      if (Array.isArray(value)) encodedLargeStrings += value.filter(v => typeof v === "string" && v.length > 1000).length;
      return stringify(value, ...args);
    };
    for (let i = 0; i < 100; i++) updateProjectStatus();`);
  assert.equal(h.run("encodedLargeStrings"), 0);
  assert.equal(h.run("stringifies"), 100); // only small preference keys
  assert.match(h.el("project-status").textContent, /^Unchanged/);
  h.run("JSON.stringify = stringify");
  for (const [change, expected] of [
    ["view.x++", /^Changed/], ["view.x--", /^Unchanged/],
    ['el("project-name").value = "Other"', /^Changed/], ['el("project-name").value = ""', /^Unchanged/],
    ['S.snapshot = JSON.parse(JSON.stringify(S.snapshot))', /^Unchanged/],
    ['S.snapshot = {...S.snapshot, unlimited: true}', /^Changed/],
    ['S.snapshot = {...S.snapshot, unlimited: false}', /^Unchanged/],
    ['el("slop").value = "-1"', /invalid/], ['el("slop").value = "0"', /^Unchanged/],
  ]) {
    h.run(change + "; updateProjectStatus()");
    assert.match(h.el("project-status").textContent, expected, change);
  }
});

test("hover-only frames never recompute project status; view changes still do", () => {
  let checks = 0, paints = 0;
  const h = harness({state: scene([track([[0, 0, 0], [128, 0, 0]])]), events: true, schedule: true,
    overrides: {updateProjectStatus() { checks++; }, paint() { paints++; }}});
  const flush = () => { while (h.frames.length) h.frames.shift()(); };
  for (let i = 0; i < 100; i++) h.run(`queueHover(${260 + i / 10},250)`);
  flush();
  assert.equal(checks, 0);
  assert.equal(paints, 1);
  h.run("view.x++; draw(); queueHover(280, 250)"); flush();
  assert.equal(checks, 1);
  assert.equal(paints, 2);
});

test("one lazy geometry record owns bounds, segments, batches and piece groups", () => {
  const placements = [track([[0, 0, 0], [128, 0, 0]])];
  const h = harness({state: scene(placements), events: true});
  const record = h.context.drawingGeometry(placements);
  h.context.hitCandidates(250, 250, placements);
  assert.ok(record.bounds);
  assert.equal(record.segments, undefined); // prefilter alone does not allocate rails
  const segments = h.context.drawingSegments(placements);
  assert.equal(h.context.drawingSegments(placements), segments);
  const batches = h.context.drawingBatches(placements);
  assert.equal(h.context.drawingBatches(placements), batches);
  assert.equal(h.context.drawingGeometry(placements), record);
  assert.equal(record.byPlacement[0][0], segments[0]);
  assert.notEqual(h.context.drawingGeometry([...placements]), record);
  assert.ok(segments.every(segment => !("order" in segment)));
});

for (const z of [undefined, 0, 57.6, 120]) test(`flat chords at elevation ${z} keep original sampled edges`, () => {
  const placements = [track([[0, 0, z], [128, 0, z], [160, 40, z]])];
  const h = harness();
  const segments = h.context.drawingSegments(placements);
  assert.equal(segments.length, 2);
  assert.deepEqual(Array.from(segments[0].a), [0, 0, z || 0]);
  assert.deepEqual(Array.from(segments[0].b), [128, 0, z || 0]);
  assert.deepEqual(Array.from(segments[1].b), [160, 40, z || 0]);
});

test("climbing edges retain local height subdivision and descending paint order", () => {
  const h = harness();
  for (const [from, to] of [[0, 57.6], [57.6, 0]]) {
    const segments = h.context.drawingSegments([track([[0, 0, from], [320, 0, to]])]);
    assert.equal(segments.length, 40);
    assert.ok(segments.every(segment => Math.abs(segment.a[0] - segment.b[0]) <= 8));
    assert.ok(segments.every((segment, i) => !i || segment.z >= segments[i - 1].z));
  }
});

test("shortlisted picking does not iterate the global segment array", () => {
  const placements = [track([[-100, 0, 0], [100, 0, 0]])];
  for (let i = 0; i < 200; i++) placements.push(track([[10000 + 500*i, 0, 0], [10100 + 500*i, 0, 0]]));
  const h = harness({state: scene(placements), events: true, overrides: {worldToScreen: (x, y) => [x, y]}});
  const segments = h.context.drawingSegments(placements);
  segments[Symbol.iterator] = () => { throw new Error("walked all segments"); };
  assert.equal(h.context.placementAt(0, 0), 0);
  assert.equal(h.context.placementAt(10010, 0), 1);
});

for (const scale of [0.08, 0.9, 4]) test(`grouped shortlist picking matches an unfiltered scan at scale ${scale}`, () => {
  const placements = [track([[-100, 0, 0], [100, 0, 0]]),
    track([[0, -150, 0], [0, 150, 120]]), track([[-100, 0, 120], [100, 0, 120]])];
  const fast = harness({state: scene(placements), events: true});
  const slow = harness({state: scene(placements), events: true, overrides: {
    hitCandidates: () => new Set(placements.map((_, i) => i)),
  }});
  for (const h of [fast, slow]) h.run(`view = {x: -21.75, y: 11.5, scale: ${scale}}`);
  for (let x = 0; x <= 500; x += 10) for (let y = 0; y <= 500; y += 10) {
    const ids = h => Array.from(h.context.placementsAt(x, y), hit => hit.placement);
    assert.deepEqual(ids(fast), ids(slow), `${x}, ${y}`);
  }
});
