"use strict";
// Test train: the starts it offers, playing a trace, its terminal event, coverage
// overlays and initial switch choices, none of which outlives the revision or
// settings it was made for.
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene, track} = require("./reliability-harness.cjs");
const json = v => JSON.parse(JSON.stringify(v));
const tracks = () => [track([[-100, 0, 100], [100, 0, 100]], "Top"),
  track([[0, -100, 0], [0, 100, 0]], "Bottom"), track([[1000, 0, 0], [1100, 0, 0]], "Distant")];

test("train trace steps, pauses and expires without claiming all starting states", async () => {
  const trace = {revision: 1, outcome: "endless", start: [0, 0], steps: [[0, 0, 1], [1, 0, 1]],
    cycle_start: 0, period: 2, reversals: 0, visited_drivable: [0, 1], drivable_count: 2,
    complete: true};
  const h = harness({events: true, overrides: {api: async () => trace}});
  h.el("train-start").value = "[0,0]";
  await h.run("testTrain()"); assert.match(h.el("train-report").textContent, /not a claim about every start/);
  await h.el("train-step").click(); assert.equal(h.run("trainStep"), 0);
  await h.el("train-play").click(); assert.equal(h.intervals.size, 1);
  await h.el("train-pause").click(); assert.equal(h.intervals.size, 0);
  h.run("discardStaleInteraction(); S.revision++; discardStaleInteraction()");
  assert.equal(h.run("trainTrace"), null); assert.equal(h.el("train-play").disabled, true);
});

for (const immediate of [true, false]) test(`train ${immediate ? "immediate" : "downstream"} stop has a playable terminal event`, async () => {
  const strokes = [];
  const trace = {revision: 1, outcome: "stopped", start: [0, 0],
    steps: immediate ? [] : [[0, 0, 1]], terminal: {placement: 1, entry: 0, at_port: null, reason: "stop_stone"},
    cycle_start: null, period: null, reversals: 0, visited_drivable: [0, 1],
    drivable_count: 3, unvisited: [2], cycle_pieces: [], complete: true};
  const h = harness({state: scene(tracks()), events: true,
    overrides: {api: async () => trace, strokeSegment: (a, b) => strokes.push([a, b])}});
  h.el("train-start").value = "[0,0]"; await h.run("testTrain()");
  assert.equal(h.el("train-play").disabled, false);
  if (!immediate) await h.el("train-step").click();
  await h.el("train-step").click();
  assert.match(h.el("train-report").textContent, /Final event: #2.*midpoint — stop stone/);
  assert.match(h.el("train-report").textContent, /2 \/ 3 drivable pieces visited/);
  h.run("drawHighlights()"); assert.deepEqual(json(strokes.at(-1)), [[0, -100, 0], [0, 100, 0]]);
  assert.equal(trace.steps.length, immediate ? 0 : 1);
  assert.equal(h.el("train-step").disabled, true);
  await h.el("train-play").click();
  while (h.intervals.size) [...h.intervals.values()][0]();
  assert.equal(h.run("trainStep"), trace.steps.length);
});

test("step limit disables playback and coverage rather than highlighting supposedly unvisited track", async () => {
  const h = harness({state: scene(tracks()), events: true, overrides: {api: async () => ({
    revision: 1, outcome: "limit", limit: 3, steps: [], complete: false, terminal: null, unvisited: null,
    visited_drivable: [], drivable_count: 3,
  })}});
  h.el("train-start").value = "[0,0]"; await h.run("testTrain()");
  assert.match(h.el("train-report").textContent, /3-step limit.*no verdict or coverage claim/);
  for (const id of ["train-play", "train-step", "train-unvisited", "train-cycle"]) assert.ok(h.el(id).disabled);
});

test("coverage overlays distinguish unvisited and cycle pieces and expire with new settings", async () => {
  const strokes = [];
  const trace = {revision: 1, outcome: "endless", start: [0, 0], steps: [[0,0,1],[1,0,1]],
    cycle_start: 1, period: 1, reversals: 0, visited_drivable: [0,1],
    drivable_count: 3, unvisited: [2], cycle_pieces: [1], terminal: null, complete: true};
  const h = harness({state: scene(tracks()), events: true,
    overrides: {api: async () => trace, strokeSegment: (a, b, w, color) => strokes.push({a, b, color})}});
  h.el("train-start").value = "[0,0]"; await h.run("testTrain()");
  h.el("train-unvisited").checked = true; h.el("train-cycle").checked = true;
  h.run("drawHighlights()");
  assert.ok(strokes.some(x => x.a[0] === 1000 && x.color === "#be6712"));
  assert.ok(strokes.some(x => x.a[1] === -100 && x.color === "#168277"));
  h.el("train-start").listeners.change();
  assert.equal(h.run("trainTrace"), null); assert.equal(h.el("train-cycle").checked, false);
});

test("switch controls send explicit choices and reject responses from old selections", async () => {
  let finish, body;
  const s = scene(tracks()); s.train_switches = [{placement: 0, default: 1,
    options: [{port: 1, name: "Left"}, {port: 2, name: "Right"}]}];
  const h = harness({state: s, events: true, overrides: {api: (_path, b) => { body = b; return new Promise(resolve => { finish = resolve; }); }}});
  h.run("renderNavigation()");
  const select = h.el("train-switches").children[0].children[0];
  assert.equal(select.value, "1"); select.value = 2; select.listeners.change();
  h.el("train-start").value = "[0,0]";
  const request = h.run("testTrain()"); assert.deepEqual(json(body.switch_states), {0: 2});
  select.value = 1; select.listeners.change();
  finish({revision: 1, steps: []}); await request;
  assert.equal(h.run("trainTrace"), null);
});

test("Test train offers no start on a buffer stop or an off-ramp, though each stays a piece to pick", () => {
  // A straight between the two. Each has one real connector and no route through it:
  // no train stands on it.
  const buffer = track([[0, 0, 0], [64, 0, 0]], "Buffer stop (rail end)");
  buffer.drivable = false;
  buffer.ports = [{port: 0, open: false, sealed: false, x: 0, y: 0, deg: 180, name: "a"},
    {port: 1, open: true, sealed: true, x: 64, y: 0, deg: 0, name: "end"}];
  const straight = track([[0, 0, 0], [-128, 0, 0]], "Straight rail");
  straight.ports = [{port: 0, open: false, sealed: false, x: 0, y: 0, deg: 0, name: "a"},
    {port: 1, open: false, sealed: false, x: -128, y: 0, deg: 180, name: "b"}];
  const offramp = track([[-128, 0, 0], [-224, 0, 0]], "Off-ramp to the floor");
  offramp.drivable = false;
  offramp.ports = [{port: 0, open: false, sealed: false, x: -128, y: 0, deg: 0, name: "a"},
    {port: 1, open: true, sealed: true, x: -224, y: 0, deg: 180, name: "floor"}];
  const h = harness({state: scene([buffer, straight, offramp])});
  h.run("renderNavigation()");
  assert.deepEqual(h.el("train-start").children.map(option => [option.value, option.textContent]),
    [["[1,0]", "#2 Straight rail — enter a"], ["[1,1]", "#2 Straight rail — enter b"]]);
  assert.equal(h.el("train-start").value, "[1,0]");  // Test train starts on the straight
  assert.deepEqual(h.el("piece-select").children.map(option => option.textContent),
    ["#1 Buffer stop (rail end)", "#2 Straight rail", "#3 Off-ramp to the floor"]);
});

test("Test train and Best settings for this start wait for a piece a train can start on", () => {
  // A buffer stop alone has no route through it, so neither has a start to run from;
  // the analysis of all starts still has track to look at.
  const buffer = track([[0, 0, 0], [64, 0, 0]], "Buffer stop (rail end)");
  buffer.drivable = false;
  buffer.ports = [{port: 0, open: true, sealed: false, x: 0, y: 0, deg: 180, name: "a"},
    {port: 1, open: true, sealed: true, x: 64, y: 0, deg: 0, name: "end"}];
  const h = harness({state: scene([buffer])});
  const disabled = () => ["test-train", "route-best", "route-all"].map(id => h.el(id).disabled);
  h.run("renderNavigation()");
  assert.equal(h.el("train-start").children.length, 0);
  assert.deepEqual(disabled(), [true, true, false]);
  // A straight joined to the buffer stop offers a train its two starts.
  const straight = track([[0, 0, 0], [-128, 0, 0]], "Straight rail");
  straight.ports = [{port: 0, open: false, sealed: false, x: 0, y: 0, deg: 0, name: "a"},
    {port: 1, open: true, sealed: false, x: -128, y: 0, deg: 180, name: "b"}];
  buffer.ports[0].open = false;
  h.context.S = scene([buffer, straight], 2);
  h.run("renderNavigation()");
  assert.equal(h.el("train-start").children.length, 2);
  assert.deepEqual(disabled(), [false, false, false]);
});
