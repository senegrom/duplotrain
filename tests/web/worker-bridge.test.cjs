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
  const timers = new Map();
  const body = new Element("body");
  const context = vm.createContext({
    window: {}, document: {body, createElement: tag => new Element(tag)}, Worker,
    location: {reload() {}}, console,
    setTimeout(fn) { const id = Symbol(); timers.set(id, fn); return id; },
    clearTimeout(id) { timers.delete(id); },
  });
  vm.runInContext(fs.readFileSync(path.join(root, "webapp/boot.js"), "utf8"), context);
  return {window: context.window, workers, timers, body};
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
  const result = h.window.duplotrainApi("/api/clear", {});
  const message = h.workers[0].sent[0];
  assert.equal(message.body, "{}");
  h.workers[0].emit({id: message.id, res: '{"ok":true}'});
  assert.equal((await result).ok, true);
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
