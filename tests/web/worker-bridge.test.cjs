"use strict";
const test = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const root = path.resolve(__dirname, "../..");

function harness() {
  class Element {
    constructor(tag) { this.tag = tag; this.children = []; this.style = {}; this.isConnected = false; }
    append(...children) { children.forEach(c => { c.isConnected = true; }); this.children.push(...children); }
    remove() { this.isConnected = false; }
    querySelector(tag) { return this.children.find(c => c.tag === tag) || null; }
    addEventListener(name, callback) { this[name] = callback; }
  }
  const workers = [];
  class Worker {
    constructor(url) { this.url = url; this.sent = []; workers.push(this); }
    addEventListener(name, callback) { this[name] = callback; }
    postMessage(message) { this.sent.push(message); }
    emit(data) { this.message({data}); }
    terminate() { this.terminated = true; }
  }
  const timers = new Map(), delays = new Map();  // pending timers and their delays
  const body = new Element("body");
  const context = vm.createContext({
    window: {}, document: {body, createElement: tag => new Element(tag)}, Worker,
    location: {reload() {}}, console,
    setTimeout(fn, ms) { const id = Symbol(); timers.set(id, fn); delays.set(id, ms); return id; },
    clearTimeout(id) { timers.delete(id); delays.delete(id); },
  });
  vm.runInContext(fs.readFileSync(path.join(root, "webapp/boot.js"), "utf8"), context);
  return {window: context.window, workers, timers, delays, body};
}
async function boot(h) {
  const promise = h.window.duplotrainBoot({refresh: async () => {}, status() {}});
  h.workers[0].emit({ready: true});
  await promise;
}

test("API rejects before boot and correlates request IDs afterwards", async () => {
  const h = harness();
  await assert.rejects(h.window.duplotrainApi("/api/state"), /not ready/);
  await boot(h);
  const first = h.window.duplotrainApi("/api/clear", {});
  const second = h.window.duplotrainApi("/api/state");
  const [a, b] = h.workers[0].sent;
  assert.equal(a.body, "{}");
  // Answers arriving out of order still reach their own callers.
  h.workers[0].emit({id: b.id, res: '{"which":"second"}'});
  h.workers[0].emit({id: a.id, res: '{"which":"first"}'});
  assert.equal((await first).which, "first");
  assert.equal((await second).which, "second");
  assert.equal(h.timers.size, 0);
});

test("worker crash rejects every pending request and displays literal error text", async () => {
  const h = harness();
  await boot(h);
  const a = assert.rejects(h.window.duplotrainApi("/api/state"), /<b>crashed<\/b>/);
  const b = assert.rejects(h.window.duplotrainApi("/api/solve", {}), /<b>crashed<\/b>/);
  h.workers[0].onerror({message: "<b>crashed</b>", preventDefault() {}});
  await Promise.all([a, b]);
  assert.equal(h.workers[0].terminated, true);
  assert.ok(h.body.children[0].children[0].textContent.includes("<b>crashed</b>"));
  assert.ok(h.body.children[0].querySelector("button"));
  await assert.rejects(h.window.duplotrainApi("/api/state"), /not ready/);
});

test("boot errors and timeout both settle startup and offer recovery", async () => {
  for (const timeout of [false, true]) {
    const h = harness();
    const promise = h.window.duplotrainBoot({refresh: async () => {}, status() {}});
    if (timeout) [...h.timers.values()][0]();
    else h.workers[0].emit({bootError: "missing runtime"});
    await promise;
    assert.equal(h.workers[0].terminated, true);
    assert.equal(h.timers.size, 0);
    assert.ok(h.body.children[0].querySelector("button"));
  }
});

test("the engine gets a minute to load and a pending call two minutes of silence", async () => {
  const h = harness();
  const promise = h.window.duplotrainBoot({refresh: async () => {}, status() {}});
  assert.deepEqual([...h.delays.values()], [60000]);
  h.workers[0].emit({ready: true}); await promise;
  assert.equal(h.delays.size, 0);
  const call = h.window.duplotrainApi("/api/state");
  assert.deepEqual([...h.delays.values()], [120000]);
  h.workers[0].emit({id: h.workers[0].sent[0].id, res: "{}"}); await call;
  assert.equal(h.delays.size, 0);
});

test("adapter errors and worker message errors reject callers", async () => {
  const h = harness();
  await boot(h);
  let promise = h.window.duplotrainApi("/api/import", {});
  h.workers[0].emit({id: h.workers[0].sent[0].id, res: '{"__error":"bad layout"}'});
  await assert.rejects(promise, /bad layout/);
  promise = h.window.duplotrainApi("/api/state");
  h.workers[0].onmessageerror();
  await assert.rejects(promise, /invalid worker message/);
});

test("worker boot reports failed runtime requests instead of unpacking HTTP error pages", async () => {
  const messages = [];
  const context = vm.createContext({
    importScripts() {}, loadPyodide: async () => ({}),
    fetch: async () => ({ok: false, status: 404}),
    postMessage: message => messages.push(message), console,
    onmessage: null,
  });
  vm.runInContext(fs.readFileSync(path.join(root, "webapp/worker.js"), "utf8"), context);
  await new Promise(resolve => setImmediate(resolve));
  assert.equal(messages.length, 1);
  assert.match(messages[0].bootError, /HTTP 404/);
});

test("adapter conflicts preserve their code and current state through the worker bridge", async () => {
  const h = harness();
  await boot(h);
  const promise = h.window.duplotrainApi("/api/remove", {placement: 1, revision: 3});
  h.workers[0].emit({id: h.workers[0].sent[0].id, res: JSON.stringify({
    __error: "Your action was not applied", code: "stale_revision", state: {revision: 4},
  })});
  await assert.rejects(promise, error => {
    assert.equal(error.code, "stale_revision");
    assert.equal(error.state.revision, 4);
    assert.match(error.message, /not applied/);
    return true;
  });
});

async function recoverableBoot(h, extra = {}) {
  const snapshot = {format: "duplotrain-session/1", layout: {format: "duplotrain-layout/1", placements: [{piece: "curve"}]},
    inventory: {curve: 17}, stones: {stone_stop: 2}, unlimited: false};
  const restored = [], downloads = [], notices = [];
  const promise = h.window.duplotrainBoot({refresh: async () => {}, status: v => notices.push(v),
    checkpoint: () => snapshot, downloadLayout: () => downloads.push(snapshot.layout),
    downloadSession: () => downloads.push(snapshot), restored: v => restored.push(v), ...extra});
  h.workers[0].emit({ready: true}); await promise;
  return {snapshot, restored, downloads, notices};
}

test("failure overlay exports the last confirmed layout and session without the worker", async () => {
  const h = harness(), r = await recoverableBoot(h);
  h.workers[0].onerror({message: "offline", preventDefault() {}});
  const actions = h.body.children[0].children.filter(c => c.tag === "button");
  assert.equal(actions.length, 4);
  actions.find(b => b.textContent === "Download last confirmed layout").click();
  actions.find(b => b.textContent === "Download last confirmed session").click();
  assert.deepEqual(r.downloads, [r.snapshot.layout, r.snapshot]);
  assert.equal(h.workers[0].sent.length, 0);
});

// The failure overlay's restart button is the only way the page restarts the engine.
function crash(h) {
  h.workers.at(-1).onerror({message: "engine crashed", preventDefault() {}});
  return () => h.body.children[0].children.find(
    c => c.textContent === "Restart engine and restore last confirmed session");
}
const turns = async (n = 3) => { for (let i = 0; i < n; i++) await new Promise(r => setImmediate(r)); };

test("restart restores an isolated copy of this tab's snapshot and ignores late responses", async () => {
  const h = harness(), r = await recoverableBoot(h);
  const original = structuredClone(r.snapshot);
  const pending = assert.rejects(h.window.duplotrainApi("/api/search/tick", {}), /engine crashed/);
  const first = h.workers[0], ticking = first.sent[0];
  const restart = crash(h); await pending;
  restart().click();
  assert.equal(first.terminated, true);
  r.snapshot.inventory.curve = 999; // no alias into the captured recovery payload
  // Late messages from the old engine, even a failure, never touch the new one.
  first.emit({id: ticking.id, res: '{"revision":999}'});
  first.emit({bootError: "late failure from the old engine"});
  const second = h.workers[1]; assert.equal(second.terminated, undefined);
  second.emit({ready: true});
  await turns(1);
  const restore = second.sent[0];
  assert.equal(restore.path, "/api/restore");
  assert.deepEqual(JSON.parse(restore.body).data, original);
  assert.equal(JSON.parse(restore.body).revision, 0);
  second.emit({id: restore.id, res: '{"revision":1,"restored":true}'});
  await turns();
  assert.equal(r.restored.length, 1); assert.equal(r.restored[0].revision, 1);
  assert.match(r.notices.at(-1), /history and suggestions were reset/);
  assert.equal(h.timers.size, 0);
});

test("progress renews the inactivity watchdog, silence rejects pending operations", async () => {
  const h = harness(); await recoverableBoot(h);
  const pending = assert.rejects(h.window.duplotrainApi("/api/solve", {}), /No engine response or progress/);
  const old = [...h.timers.keys()][0];
  h.workers[0].emit(5000);
  assert.equal(h.timers.has(old), false); assert.equal(h.timers.size, 1);
  [...h.timers.values()][0]();
  await pending;
  assert.equal(h.workers[0].terminated, true); assert.equal(h.timers.size, 0);
});

test("failed recovery keeps emergency downloads available and never publishes restored state", async () => {
  const h = harness(), r = await recoverableBoot(h);
  crash(h)().click();
  h.workers[1].emit({ready: true}); await turns(1);
  const restore = h.workers[1].sent[0];
  h.workers[1].emit({id: restore.id, res: '{"__error":"restore failed"}'});
  await turns();
  assert.equal(r.restored.length, 0);
  const overlay = h.body.children[0];
  assert.match(overlay.children[0].textContent, /restore failed/);
  overlay.children.find(c => c.textContent === "Download last confirmed session").click();
  assert.deepEqual(r.downloads, [r.snapshot]);
});

test("repeated restart clicks create only one replacement worker", async () => {
  const h = harness(); await recoverableBoot(h);
  const restart = crash(h);
  restart().click(); restart().click();
  assert.equal(h.workers.length, 2);
  h.workers[1].emit({ready: true}); await turns(1);
  const restore = h.workers[1].sent[0]; h.workers[1].emit({id: restore.id, res: '{"revision":1}'});
  await turns();
  assert.equal(h.workers.length, 2);
});

test("a worker dying during the startup restore keeps the recovery overlay", async () => {
  const h = harness();
  const statuses = [];
  const promise = h.window.duplotrainBoot({
    status: text => statuses.push(text),
    // Like editor.js, refresh swallows a failed restore of the autosave.
    refresh: async () => {
      const restore = h.window.duplotrainApi("/api/restore", {data: {}});
      h.workers[0].onerror({message: "out of memory", preventDefault() {}});
      await restore.catch(() => {});
    },
  });
  h.workers[0].emit({ready: true});
  await promise;
  assert.equal(h.workers[0].terminated, true);
  assert.equal(h.body.children[0].isConnected, true);
  assert.ok(h.body.children[0].children[0].textContent.includes("out of memory"));
  assert.ok(!statuses.some(text => text.includes("Engine ready")));
  await assert.rejects(h.window.duplotrainApi("/api/state"), /not ready/);
});

test("a fatal engine error makes the page restart the engine rather than reuse it", async () => {
  const h = harness();
  await boot(h);
  const pending = h.window.duplotrainApi("/api/import", {});
  h.workers[0].emit({id: h.workers[0].sent[0].id, fatal: "RangeError: Maximum call stack size exceeded"});
  await assert.rejects(pending, /must restart/);
  assert.equal(h.workers[0].terminated, true);
  assert.ok(h.body.children[0].querySelector("button"));
  await assert.rejects(h.window.duplotrainApi("/api/state"), /not ready/);
});

test("the worker reports Pyodide's fatal errors apart from ordinary request errors", async () => {
  const messages = [];
  const failures = {"/fatal": () => { const error = new RangeError("Maximum call stack size exceeded");
    error.pyodide_fatal_error = true; throw error; }, "/ordinary": () => { throw new Error("bad input"); }};
  const pyodide = {FS: {mkdirTree() {}, writeFile() {}}, unpackArchive() {}, runPython() {},
    pyimport: () => ({dispatch: path => failures[path]()})};
  const context = vm.createContext({
    importScripts() {}, loadPyodide: async () => pyodide, console,
    fetch: async () => ({ok: true, arrayBuffer: async () => new ArrayBuffer(0), text: async () => ""}),
    postMessage: message => messages.push(message), onmessage: null,
  });
  vm.runInContext(fs.readFileSync(path.join(root, "webapp/worker.js"), "utf8"), context);
  await context.onmessage({data: {id: 1, path: "/fatal", body: "{}"}});
  await context.onmessage({data: {id: 2, path: "/ordinary", body: "{}"}});
  assert.deepEqual(messages.slice(1).map(m => [m.id, Boolean(m.fatal), Boolean(m.err)]), [[1, true, false], [2, false, true]]);
});
