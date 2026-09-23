"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness} = require("./reliability-harness.cjs");

function editor() {
  const calls = [];
  let redraws = 0;
  // The editor's own api() is under test; only its transport is stubbed.
  const h = harness({state: {revision: 7}, omit: ["api"], overrides: {
    redraw: () => { redraws++; },
    fetch: async (url, options) => {
      calls.push({url, options});
      return {ok: true, json: async () => ({revision: 8})};
    },
  }});
  return {context: h.context, calls, classes: h.context.document.body.classes, el: h.el,
    redraws: () => redraws, run: h.run};
}

test("every edit captures its viewed revision for HTTP and worker transports", async () => {
  const paths = ["attach", "join", "undo", "remove", "clear", "inventory", "unlimited",
                 "add_set", "stone", "solve", "apply", "import", "restore", "redo", "project/open", "check", "drive"];
  for (const transport of ["http", "worker"]) {
    const e = editor();
    if (transport === "worker") e.context.window.duplotrainApi = async (url, body) => {
      e.calls.push({url, options: {body: JSON.stringify(body)}});
      return {revision: 8};
    };
    for (const name of paths) await e.run(`api("/api/${name}", {placement: 1})`);
    assert.equal(e.calls.length, paths.length);
    for (const {options} of e.calls) assert.deepEqual(JSON.parse(options.body), {revision: 7, placement: 1, preview_format: "duplotrain-preview/1"});
    assert.equal(e.classes.size, 0);
  }
});

test("candidate revision is not silently replaced by the latest viewed revision", async () => {
  const e = editor();
  await e.run('api("/api/apply", {index: 0, revision: 3})');
  assert.deepEqual(JSON.parse(e.calls[0].options.body), {revision: 3, index: 0, preview_format: "duplotrain-preview/1"});
});

test("read-only requests do not require or inject an edit revision", async () => {
  const e = editor();
  await e.run('api("/api/state")');
  await e.run('api("/api/export", {})');
  assert.equal(e.calls[0].options.method, "POST");
  assert.deepEqual(JSON.parse(e.calls[0].options.body), {preview_format: "duplotrain-preview/1"});
  assert.equal(e.calls[1].options.body, "{}");
});

for (const transport of ["http", "worker"]) {
  test(`${transport} conflict refreshes tools and layout but never replays the action`, async () => {
    const e = editor();
    const current = {revision: 9, layout: {placements: [{piece: "curve"}, {piece: "switch"}]}};
    const data = {error: "Your action was not applied", code: "stale_revision", state: current};
    if (transport === "http") e.context.fetch = async (url, options) => {
      e.calls.push({url, options});
      return {ok: false, status: 409, json: async () => data};
    };
    else e.context.window.duplotrainApi = async (url, body) => {
      e.calls.push({url, body});
      throw Object.assign(new Error(data.error), {code: data.code, state: data.state});
    };
    e.run('deleting = true; armed = {piece:"straight"}; selectedCandidate = "old"; preview = {};');
    await assert.rejects(e.run('api("/api/remove", {placement: 1})'), /not applied/);
    assert.equal(e.calls.length, 1);
    assert.equal(e.run("S.revision"), 9);
    assert.equal(e.run("S.layout.placements[1].piece"), "switch");
    assert.equal(e.run("deleting"), false);
    for (const name of ["armed", "armedStone", "pickMode", "selectedCandidate", "preview"])
      assert.equal(e.run(name), null);
    assert.equal(e.el("expand-search").hidden, true);
    assert.equal(e.redraws(), 1);
    assert.equal(e.run("apiBusy"), false);
    assert.equal(e.classes.size, 0);
  });
}

test("every edit also names the engine instance it acted on", async () => {
  const calls = [];
  const h = harness({state: {revision: 7, instance: "a1"}, omit: ["api"], overrides: {
    fetch: async (url, options) => { calls.push(JSON.parse(options.body)); return {ok: true, json: async () => ({revision: 8})}; },
  }});
  await h.run('api("/api/remove", {placement: 1})');
  await h.run('api("/api/state")');
  assert.deepEqual(calls[0], {revision: 7, instance: "a1", placement: 1, preview_format: "duplotrain-preview/1"});
  assert.deepEqual(calls[1], {preview_format: "duplotrain-preview/1"});
});

function restartedEngine(restore) {
  const confirmed = {format: "duplotrain-session/1", layout: {placements: [{piece: "curve"}]}};
  const empty = {format: "duplotrain-session/1", layout: {placements: []}};
  const calls = [];
  let redraws = 0;
  const h = harness({state: {revision: 5, instance: "old", snapshot: confirmed}, omit: ["api"], overrides: {
    redraw: () => { redraws++; },
    fetch: async (url, options) => {
      const body = JSON.parse(options.body);
      calls.push({url, body});
      const reply = url === "/api/restore" ? restore(body) :
        {status: 409, data: {error: "Your action was not applied", code: "stale_revision",
          state: {revision: 0, instance: "new", snapshot: empty}}};
      return {ok: reply.status === 200, status: reply.status, json: async () => reply.data};
    },
  }});
  return {h, calls, confirmed, redraws: () => redraws};
}

test("a restarted engine receives this tab's confirmed session instead of emptying it", async () => {
  const e = restartedEngine(body => ({status: 200, data: {revision: 1, instance: "new", snapshot: body.data}}));
  e.h.run('pickMode = {stage: "grow"}; selectedCandidate = "5:0";');
  await assert.rejects(e.h.run('api("/api/remove", {placement: 0})'), /session was restored/);
  assert.deepEqual(e.calls.map(c => c.url), ["/api/remove", "/api/restore"]);
  assert.deepEqual(e.calls[1].body, {data: e.confirmed, revision: 0, instance: "new",
    preview_format: "duplotrain-preview/1"});
  assert.equal(e.h.run("S.instance"), "new");
  assert.deepEqual(e.h.run("S.snapshot"), e.confirmed);
  assert.equal(e.h.run("pickMode"), null);
  assert.equal(e.h.run("selectedCandidate"), null);
  assert.equal(e.redraws(), 1);
  assert.equal(e.h.run("apiBusy"), false);
});

test("a failed restore keeps this tab's session rather than adopting the empty engine", async () => {
  const e = restartedEngine(() => ({status: 409, data: {error: "invalid snapshot"}}));
  await assert.rejects(e.h.run('api("/api/remove", {placement: 0})'), /restoring this tab's session failed/);
  assert.equal(e.h.run("S.instance"), "old");
  assert.deepEqual(e.h.run("S.snapshot"), e.confirmed);
  assert.equal(e.redraws(), 0);
});

test("another tab's restore into the new engine is adopted like any conflict", async () => {
  const theirs = {revision: 1, instance: "new", snapshot: {format: "duplotrain-session/1", layout: {placements: []}}};
  const e = restartedEngine(() => ({status: 409, data: {error: "stale", code: "stale_revision", state: theirs}}));
  await assert.rejects(e.h.run('api("/api/remove", {placement: 0})'), /not applied/);
  assert.equal(e.h.run("S.revision"), 1);
  assert.equal(e.h.run("S.instance"), "new");
  assert.equal(e.redraws(), 1);
});
