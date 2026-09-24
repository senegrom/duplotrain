"use strict";
// Stored sessions: one autosave and one list of copies per app, whichever URL
// spelling opened it, and a session the engine cannot restore is kept until the
// user downloads or deliberately discards it.
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness, scene} = require("./reliability-harness.cjs");

const KEY = "duplotrain-session/2:/app/";
const INDEX_KEY = "duplotrain-session/2:/app/index.html";

function session(count) {
  return {format: "duplotrain-session/1", inventory: {straight: 20}, stones: {}, unlimited: false,
    layout: {format: "duplotrain-layout/1", placements: Array(count).fill({piece: "straight"})}};
}
function checkpoint(count) {
  return JSON.stringify({format: "duplotrain-checkpoint/1", revision: `r${count}`, snapshot: session(count)});
}
// Objects built inside the editor's context have its prototypes, not this realm's.
const plain = value => JSON.parse(JSON.stringify(value));
function tab(pathname, {restore = null, stored = {}} = {}) {
  const downloads = [];
  const state = {...scene(), revision: 0, instance: "A"};
  const h = harness({state, events: true, omit: ["saveSession"], overrides: {
    location: {pathname},
    api: async (path, body) => {
      h.calls.push({path, body});
      if (path === "/api/restore" && restore) throw restore;
      return {...state, revision: 1, snapshot: path === "/api/restore" ? body.data : state.snapshot};
    },
    Blob: class { constructor(parts, options) { this.text = parts.join(""); this.type = options.type; } },
    URL: {createObjectURL: blob => { downloads.push(blob); return "blob:kept"; }, revokeObjectURL() {}},
  }});
  for (const [key, value] of Object.entries(stored)) h.saved.set(key, value);
  for (const id of ["save-recovery", "save-discard-confirm", "save-discard-cancel"]) h.el(id).hidden = true;
  h.downloads = downloads;
  h.init = () => h.run("initializeRecovery()");
  h.restored = () => plain(h.calls.filter(call => call.path === "/api/restore").map(call => call.body.data));
  return h;
}

test("the directory and its index.html share one autosave", async () => {
  for (const pathname of ["/app/", "/app/index.html"]) {
    const h = tab(pathname, {stored: {[KEY]: checkpoint(3)}});
    assert.equal(h.run("STORAGE_KEY"), KEY);
    await h.init();
    assert.deepEqual(h.restored(), [session(3)]);
    assert.equal(h.run("autosaveReady"), true);
  }
});

test("an autosave kept under the index.html spelling moves to the app's key", async () => {
  const h = tab("/app/", {stored: {[INDEX_KEY]: checkpoint(2)}});
  await h.init();
  assert.deepEqual(h.restored(), [session(2)]);
  assert.equal(h.saved.get(KEY), checkpoint(2));
  assert.equal(h.saved.has(INDEX_KEY), false);
});

test("beside the app's own autosave, the index.html one becomes a local copy", async () => {
  const h = tab("/app/index.html", {stored: {[KEY]: checkpoint(3), [INDEX_KEY]: checkpoint(2)}});
  await h.init();
  assert.deepEqual(h.restored(), [session(3)]);
  assert.equal(h.saved.get(KEY), checkpoint(3));
  assert.equal(h.saved.has(INDEX_KEY), false);
  const copies = [...h.saved].filter(([key]) => key.startsWith("duplotrain-project/1:/app/:"));
  assert.equal(copies.length, 1);
  const copy = h.run(`readLocalProject(${JSON.stringify(copies[0][0])}, ${JSON.stringify(copies[0][1])})`);
  assert.equal(copy.name, "Autosave from index.html");
  assert.deepEqual(plain(copy.session), session(2));
  assert.deepEqual(h.el("project-slots").children.map(option => option.value), [copies[0][0]]);
  // An unreadable one is never converted, or dropped.
  const kept = tab("/app/", {stored: {[KEY]: checkpoint(3), [INDEX_KEY]: "not json"}});
  await kept.init();
  assert.equal(kept.saved.get(INDEX_KEY), "not json");
});

test("local copies saved under either spelling are listed and open", async () => {
  const old = "duplotrain-project/1:/app/index.html:abc";
  const raw = JSON.stringify({format: "duplotrain-project/1", name: "Old copy", session: session(1), preferences: {}});
  const h = tab("/app/", {stored: {[old]: raw, "duplotrain-project/1:/other/:x": raw}});
  h.run("renderProjects()");
  assert.deepEqual(h.el("project-slots").children.map(option => option.value), [old]);
  assert.equal(h.run(`readLocalProject(${JSON.stringify(old)}, ${JSON.stringify(raw)})`).name, "Old copy");
});

test("an unreadable autosave is kept until downloaded or discarded on purpose", async () => {
  const h = tab("/app/", {stored: {[KEY]: "not json"}});
  await h.init();
  assert.equal(h.run("autosaveReady"), false);
  assert.match(h.el("save-status").textContent, /Existing save kept/);
  assert.equal(h.el("save-recovery").hidden, false);
  await h.el("save-download").click();
  assert.deepEqual(h.downloads.map(blob => blob.text), ["not json"]);
  h.el("save-discard").click();
  assert.equal(h.el("save-discard-confirm").hidden, false);
  h.el("save-discard-cancel").click();
  assert.equal(h.el("save-discard-confirm").hidden, true);
  await h.run("saveSession()");
  assert.equal(h.saved.get(KEY), "not json");
  h.el("save-discard").click();
  await h.el("save-discard-confirm").click();
  const saved = JSON.parse(h.saved.get(KEY));
  assert.deepEqual(saved.snapshot, plain(h.run("S").snapshot));
  assert.equal(h.run("autosaveReady"), true);
  assert.equal(h.el("save-recovery").hidden, true);
});

test("a session the engine refuses downloads in the format Open project reads", async () => {
  const refusal = Object.assign(new Error("unknown piece id"), {refused: true});
  const h = tab("/app/", {stored: {[KEY]: checkpoint(2)}, restore: refusal});
  await h.init();
  assert.equal(h.run("autosaveReady"), false);
  await h.el("save-download").click();
  assert.deepEqual(JSON.parse(h.downloads[0].text), session(2));
  // Another tab replaced it meanwhile: discarding must not remove that one.
  h.saved.set(KEY, checkpoint(4));
  h.el("save-discard").click();
  await h.el("save-discard-confirm").click();
  assert.equal(h.saved.get(KEY), checkpoint(4));
  assert.equal(h.run("autosaveReady"), false);
  assert.match(h.el("save-status").textContent, /Another tab changed the saved session/);
});

test("losing the startup restore to another tab keeps autosave on", async () => {
  const conflict = Object.assign(new Error("stale revision"), {code: "stale_revision", refused: true,
    state: {instance: "A", revision: 1}});
  const h = tab("/app/", {stored: {[KEY]: checkpoint(2)}, restore: conflict});
  await h.init();
  assert.equal(h.run("autosaveReady"), true);
  assert.equal(h.el("save-recovery").hidden, true);
});

test("a save that failed to restore for another reason is kept without the choices", async () => {
  const restarted = Object.assign(new Error("stale revision"), {code: "stale_revision", refused: true,
    state: {instance: "B", revision: 0}});
  for (const failure of [new TypeError("Failed to fetch"), new Error("engine is not ready"), restarted]) {
    const h = tab("/app/", {stored: {[KEY]: checkpoint(2)}, restore: failure});
    await h.init();
    assert.equal(h.run("autosaveReady"), false);
    assert.equal(h.el("save-recovery").hidden, true);
    assert.match(h.el("save-status").textContent, /Existing save kept; export new work/);
    await h.run("saveSession()");
    assert.equal(h.saved.get(KEY), checkpoint(2));
  }
});

test("only the local server's answer marks a request as refused", async () => {
  const h = tab("/app/");
  h.context.fetch = async () => ({ok: false, status: 409, json: async () => ({error: "bad layout"})});
  await assert.rejects(h.run('send("/api/restore", {})'),
                       error => /bad layout/.test(error.message) && error.refused === true);
  h.context.fetch = async () => { throw new TypeError("Failed to fetch"); };
  await assert.rejects(h.run('send("/api/restore", {})'), error => !error.refused);
});
