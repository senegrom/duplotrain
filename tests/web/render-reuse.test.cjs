"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness} = require("./reliability-harness.cjs");

function editor() {
  const calls = [];
  const state = {
    revision: 4,
    palette: [{id: "straight", name: "Straight", variants: [
      {entry: 0, exit: 1, label: "ahead"},
    ]}],
    inventory: {unlimited: false, owned: {straight: 8}, remaining: {straight: 7}},
    stones: {catalog: {stop: {name: "Stop stone", effect: "Stop", color: "red"}},
      remaining: {stop: 1}},
    sets: [{code: "123", name: "Box", year: 2026, pieces: {straight: 8}}],
    candidates: [],
  };
  const h = harness({state, overrides: {
    armedStone: null, selectedCandidate: null, refreshStatus() {}, redraw() {},
    api: async (route, body) => { calls.push({route, body}); return h.context.S; },
  }});
  return {context: h.context, el: h.el, calls, created: h.created, run: h.run};
}

// A retained control keeps one listener per event however often it is redrawn.
// fire() calls only the latest, so a duplicate binding must be counted instead.
function assertBoundOnce(...roots) {
  for (const stack = [...roots]; stack.length;) {
    const node = stack.pop();
    if (!node || typeof node !== "object") continue;
    for (const event of Object.keys(node.registered))
      assert.equal(node.listenerCount(event), 1, `${node.tag} has ${node.listenerCount(event)} ${event} listeners`);
    stack.push(...node.children);
  }
}

function candidate(index = 0, revision = 4) {
  return {index, revision, exact: true, gap: 0, kind: "loop", added: {curve: 10},
    size_cm: [50, 50], open_stubs: 0, preview: {placements: [index]}};
}

test("unchanged redraws allocate no controls and preserve unsubmitted input", () => {
  const e = editor();
  e.run("renderPalette(); renderSets(); renderStones(); renderCandidates()");
  const row = e.run("paletteRows[0]"), count = e.created();
  row.input.value = "123";
  // API responses are fresh JSON objects, not stable object identities.
  e.context.S = JSON.parse(JSON.stringify(e.context.S));
  e.run("renderPalette(); renderSets(); renderStones(); renderCandidates()");
  assert.equal(e.created(), count);
  assert.equal(e.run("paletteRows[0].input"), row.input);
  assert.equal(row.input.value, "123");
});

test("inventory changes update values and availability without replacing controls", () => {
  const e = editor(); e.run("renderPalette()");
  const row = e.run("paletteRows[0]"), count = e.created();
  e.context.S.inventory.owned.straight = 14;
  e.context.S.inventory.remaining.straight = 0;
  e.run("renderPalette()");
  assert.equal(row.input.value, "14");  // a DOM input's value is a string
  assert.equal(row.label.textContent, "0/");
  assert.equal(row.buttons[0].button.disabled, true);
  e.context.S.inventory.unlimited = true;
  e.run("renderPalette()");
  assert.equal(row.input.hidden, true);
  assert.equal(row.label.textContent, "∞");
  assert.equal(row.buttons[0].button.disabled, false);
  e.context.S.inventory.unlimited = false;
  e.run("renderPalette()");
  assert.equal(row.input.hidden, false);
  assert.equal(e.created(), count);
});

test("retained listeners fire once and mutually exclusive tools update styling", async () => {
  const e = editor(); e.run("renderPalette(); renderStones(); renderSets()");
  const row = e.run("paletteRows[0]"), stone = e.run("stoneRows[0].button");
  await row.buttons[0].button.fire("click");
  assert.equal(row.buttons[0].button.classList.contains("armed"), true);
  await stone.fire("click");
  assert.equal(row.buttons[0].button.classList.contains("armed"), false);
  assert.equal(stone.classList.contains("armed"), true);
  e.run("renderPalette(); renderStones(); renderSets()");
  assertBoundOnce(e.el("palette"), e.el("stones"), e.el("sets"));
  assert.equal(row.input.listenerCount("change"), 1);
  row.input.value = "17";
  await row.input.fire("change");
  assert.equal(e.calls.length, 1);
  assert.equal(e.calls[0].body.counts.straight, "17");
  await e.el("sets").children[0].fire("click");
  assert.equal(e.calls.length, 2);
  assert.equal(e.calls[1].body.code, "123");
});

test("catalogue changes invalidate the relevant controls and render names as text", () => {
  const e = editor(); e.run("renderPalette(); renderSets(); renderStones()");
  const row = e.run("paletteRows[0]"), stone = e.run("stoneRows[0].button");
  e.context.S.palette[0].name = "<b>Custom straight</b>";
  e.context.S.palette[0].variants[0].label = "custom";
  e.context.S.sets = [];
  e.context.S.stones.catalog.stop.name = "New stop stone";
  e.run("renderPalette(); renderSets(); renderStones()");
  assert.notEqual(e.run("paletteRows[0].input"), row.input);
  assert.equal(e.el("palette").children[0].children[0].children[0].textContent, "<b>Custom straight</b>");
  assert.equal(e.run("paletteRows[0].buttons[0].button.textContent"), "custom");
  assert.equal(e.el("sets").children.length, 0);
  assert.notEqual(e.run("stoneRows[0].button"), stone);
});

test("candidate selection keeps card identity and uses the latest preview object", async () => {
  const e = editor(); e.context.S.candidates = [candidate(), candidate(1)];
  e.run("renderCandidates()");
  const rows = e.run("candidateRows"), count = e.created();
  assert.equal(rows[0].apply.disabled, true);
  await rows[0].show.fire("click");
  assert.equal(rows[0].apply.disabled, false);
  assert.equal(rows[0].show.attributes["aria-pressed"], "true");
  assert.equal(e.context.preview, e.context.S.candidates[0].preview);
  await rows[1].show.fire("click");
  assert.equal(rows[0].apply.disabled, true);
  assert.equal(rows[1].apply.disabled, false);
  // Do not JSON-serialize the potentially very large preview to compare cards.
  const preview = {toJSON() { throw new Error("preview must not be serialized"); }};
  e.context.S.candidates[1].preview = preview;
  e.run("renderCandidates()");
  assert.equal(e.context.preview, preview);
  assert.equal(e.created(), count);
  assertBoundOnce(e.el("cands"));
  await rows[1].apply.fire("click");
  assert.equal(e.calls[0].route, "/api/apply");
  assert.equal(e.calls[0].body.index, 1);
  assert.equal(e.calls[0].body.revision, 4);
});

test("hovering a suggestion previews it and leaving restores the chosen one; touch never hovers", () => {
  const e = editor(); e.context.S.candidates = [candidate(), candidate(1)];
  e.run("renderCandidates()");
  const card = e.el("cands").children[1], [first, second] = e.context.S.candidates;
  card.fire("pointerenter", {pointerType: "mouse"});
  assert.equal(e.context.preview, second.preview);
  card.fire("pointerleave", {pointerType: "mouse"});
  assert.equal(e.context.preview, null);
  e.run("selectedCandidate = '4:0'; renderCandidates()");
  card.fire("pointerenter", {pointerType: "pen"});
  assert.equal(e.context.preview, second.preview);
  card.fire("pointerleave", {pointerType: "pen"});
  assert.equal(e.context.preview, first.preview);
  card.fire("pointerenter", {pointerType: "touch"});
  assert.equal(e.context.preview, first.preview);
});

test("new candidate revision clears selection; changed metadata rebuilds descriptions", () => {
  const e = editor(); e.context.S.candidates = [candidate()];
  e.context.selectedCandidate = "4:0";
  e.run("renderCandidates()");
  const first = e.el("cands").children[0];
  e.context.S.candidates = [candidate(0, 5)];
  e.run("renderCandidates()");
  assert.equal(e.context.selectedCandidate, null);
  assert.equal(e.context.preview, null);
  assert.equal(e.run("candidateRows[0].apply.disabled"), true);
  assert.notEqual(e.el("cands").children[0], first);
  const second = e.el("cands").children[0];
  e.context.S.candidates[0].gap = 2;
  e.context.S.candidates[0].exact = false;
  e.run("renderCandidates()");
  assert.notEqual(e.el("cands").children[0], second);
  e.context.S.candidates = [];
  e.run("renderCandidates()");
  assert.equal(e.el("cands").children.length, 0);
});
