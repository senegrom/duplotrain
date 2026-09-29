"use strict";
const test = require("node:test");
const assert = require("node:assert/strict");
const vm = require("node:vm");
const {loadEditor} = require("./editor-harness.cjs");

function setup() {
  const calls = [];
  const next = {revision: 8, candidates: [], search_job: {job_id: "job", revision: 8,
    found: 16, page: 1, candidates: Array.from({length: 8}, (_, i) => ({index: i + 8, revision: 8}))}};
  const context = vm.createContext({S: {revision: 7, candidates: []},
    api: async (path, body, fromJob) => {calls.push({path, body, fromJob}); return next;},
    el: () => ({value: "pieces"}), redraw() {}, renderJobControls() {},
  });
  loadEditor(context);
  const run = text => vm.runInContext(text, context);
  run(`interactiveJob = {job_id: "job", revision: 7, candidates: [{index: 9, revision: 7}]};
       selectedCandidate = "7:9"; jobSequence = 3; searchPage = 1; navigationRevision = 7;`);
  return {calls, context, run, next};
}

test("publish opts into page-only transport and keeps later-page selection", async () => {
  const h = setup();
  await h.run("publishSearch(3)");
  assert.equal(h.calls.length, 1);
  assert.equal(h.calls[0].path, "/api/search/publish");
  assert.equal(h.calls[0].body.page_only, true);
  assert.equal(h.calls[0].body.page, 1);
  assert.equal(h.calls[0].body.sort, "pieces");
  assert.equal(h.calls[0].fromJob, true);
  assert.equal(h.context.S, h.next);
  assert.equal(h.run("selectedCandidate"), "8:9");
  assert.equal(h.run("visibleCandidates().length"), 8);
  assert.equal(h.run("visibleCandidates()[1].index"), 9);
  assert.equal(h.run("navigationRevision"), 8);
});

test("an obsolete publication cannot replace a newer editor session", async () => {
  const h = setup();
  let release;
  h.context.api = () => new Promise(resolve => { release = resolve; });
  const publishing = h.run("publishSearch(3)");
  h.run("jobSequence = 4; S = {revision: 12, candidates: []}");
  release(h.next);
  await publishing;
  assert.equal(h.context.S.revision, 12);
});

test("legacy state still supplies candidates without an interactive job", () => {
  const h = setup();
  h.run("interactiveJob = null; S.candidates = [{index: 22}]");
  assert.equal(h.run("visibleCandidates()[0].index"), 22);
});
