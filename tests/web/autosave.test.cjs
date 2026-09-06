"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const vm = require("node:vm");
const {randomUUID} = require("node:crypto");
const path = require("node:path");
const html = fs.readFileSync(path.join(__dirname, "../../src/duplotrain/static/editor.html"), "utf8");
const source = html.split("// ---------- Checkpoint persistence ----------")[1]
  .split("// ---------- End checkpoint persistence ----------")[0];
const KEY = "duplotrain-session/2:/";
const LEGACY = "duplotrain-session/1:/";

function snapshot(count = 0) {
  return {format: "duplotrain-session/1", layout: {placements: Array(count).fill({piece: "straight"})},
          inventory: {straight: 20}, stones: {}, unlimited: false};
}
function shared() {
  const values = new Map(), writes = [];
  let queue = Promise.resolve();
  return {
    storage: {
      getItem: key => values.get(key) ?? null,
      setItem: (key, value) => { values.set(key, value); writes.push([key, value]); },
      removeItem: key => values.delete(key),
    },
    locks: {request: (_key, callback) => {
      const pending = queue.then(callback);
      queue = pending.catch(() => {});
      return pending;
    }}, writes,
  };
}
function tab(store) {
  const events = {}, notice = {};
  const context = vm.createContext({
    S: {revision: 0, snapshot: snapshot()}, autosaveReady: false,
    location: {pathname: "/"}, localStorage: store.storage,
    navigator: {locks: store.locks}, crypto: {randomUUID},
    window: {addEventListener: (name, fn) => { events[name] = fn; }},
    document: {getElementById: () => notice,
               addEventListener: (name, fn) => { events[name] = fn; }},
  });
  context.api = async (endpoint, body) => {
    assert.equal(endpoint, "/api/restore");
    return {revision: 1, snapshot: body.data};
  };
  vm.runInContext(source, context);
  return {context, notice, events,
    init: () => vm.runInContext("initializeRecovery()", context),
    save: () => vm.runInContext("saveSession()", context),
    edit: count => { context.S = {revision: count + 1, snapshot: snapshot(count)}; },
  };
}
function saved(store) { return JSON.parse(store.storage.getItem(KEY)); }


test("unchanged redraws and closing an old tab cannot roll back newer work", async () => {
  const store = shared(), first = tab(store);
  await first.init(); await first.save();
  const stale = tab(store); await stale.init();
  first.edit(2); await first.save();
  const checkpoint = store.storage.getItem(KEY), count = store.writes.length;
  assert.equal(stale.events.pagehide, undefined);
  await stale.save();  // even an explicit final save checks its baseline
  await first.save();
  assert.equal(store.storage.getItem(KEY), checkpoint);
  assert.equal(store.writes.length, count);
  assert.equal(stale.context.autosaveReady, false);
  assert.match(stale.notice.textContent, /Another tab/);
});

test("concurrent writers from the same revision are serialized, without storage events", async () => {
  const store = shared(), seed = tab(store);
  await seed.init(); await seed.save();
  const a = tab(store), b = tab(store);
  await Promise.all([a.init(), b.init()]);
  a.edit(1); b.edit(2);
  await Promise.all([a.save(), b.save()]);
  assert.equal(saved(store).snapshot.layout.placements.length, 1);
  assert.equal(b.context.autosaveReady, false);
  assert.equal(store.writes.length, 2);  // seed plus winner, never the loser
});

test("checkpoint identity prevents ABA after another tab edits then undoes", async () => {
  const store = shared(), a = tab(store);
  await a.init(); await a.save();
  const b = tab(store); await b.init();
  const oldRevision = saved(store).revision;
  a.edit(1); await a.save();
  a.edit(0); await a.save();
  assert.notEqual(saved(store).revision, oldRevision);
  b.edit(3); await b.save();
  assert.equal(saved(store).snapshot.layout.placements.length, 0);
  assert.equal(b.context.autosaveReady, false);
});

test("an existing checkpoint is not rewritten just by opening another tab", async () => {
  const store = shared(), a = tab(store);
  await a.init(); a.edit(2); await a.save();
  const b = tab(store); await b.init(); await b.save();
  assert.equal(JSON.stringify(b.context.S.snapshot), JSON.stringify(snapshot(2)));
  assert.equal(store.writes.length, 1);
});

test("queued saves use the newest state when the lock becomes available", async () => {
  const store = shared(), a = tab(store);
  await a.init(); await a.save();
  let release;
  const held = store.locks.request(KEY, () => new Promise(resolve => { release = resolve; }));
  await Promise.resolve();
  a.edit(1); const one = a.save();
  a.edit(2); const two = a.save();
  release(); await Promise.all([held, one, two]);
  assert.equal(saved(store).snapshot.layout.placements.length, 2);
  assert.equal(store.writes.length, 2);
});

test("storage notifications pause stale tabs but ignore old delayed events", async () => {
  const store = shared(), a = tab(store);
  await a.init(); await a.save();
  const b = tab(store); await b.init();
  a.edit(1); await a.save();
  b.events.storage({key: KEY});
  assert.equal(b.context.autosaveReady, false);
  a.events.storage({key: KEY, newValue: "old delayed event"});
  assert.equal(a.context.autosaveReady, true);
});

test("clearing storage is a conflict, not permission to recreate a stale save", async () => {
  const store = shared(), a = tab(store);
  await a.init(); await a.save();
  store.storage.removeItem(KEY);
  a.events.storage({key: null});
  a.edit(1); await a.save();
  assert.equal(store.storage.getItem(KEY), null);
});

test("legacy migration isolates new saves from tabs still running the old writer", async () => {
  const store = shared();
  store.storage.setItem(LEGACY, JSON.stringify(snapshot(2)));
  const a = tab(store); await a.init(); await a.save();
  assert.equal(saved(store).snapshot.layout.placements.length, 2);
  store.storage.setItem(LEGACY, JSON.stringify(snapshot(1)));
  const b = tab(store); await b.init(); await b.save();
  assert.equal(b.context.S.snapshot.layout.placements.length, 2);
});

test("bad new checkpoints are preserved, never replaced by legacy or edited work", async () => {
  for (const raw of ["not json", "null", '{}', JSON.stringify({format: "future-format"})]) {
    const store = shared();
    store.storage.setItem(KEY, raw);
    store.storage.setItem(LEGACY, JSON.stringify(snapshot(2)));
    const a = tab(store); await a.init(); a.edit(3); await a.save();
    assert.equal(store.storage.getItem(KEY), raw);
    assert.match(a.notice.textContent, /Existing save kept/);
  }
});

test("storage changed during recovery is detected before the first write", async () => {
  const store = shared(), seed = tab(store);
  await seed.init(); await seed.save();
  const a = tab(store);
  a.context.api = async () => {
    seed.edit(2); await seed.save();
    return {revision: 1, snapshot: snapshot()};
  };
  await a.init(); a.edit(3); await a.save();
  assert.equal(saved(store).snapshot.layout.placements.length, 2);
  assert.equal(a.context.autosaveReady, false);
});

test("unsafe fallback is disabled when locks or storage are unavailable", async () => {
  const store = shared(), a = tab(store);
  await a.init(); delete a.context.navigator.locks;
  a.edit(1); await a.save();
  assert.equal(store.writes.length, 0);
  assert.match(a.notice.textContent, /Safe autosave unavailable/);
  const b = tab(store); await b.init();
  store.storage.setItem = () => { throw new Error("quota exceeded"); };
  b.edit(2); await b.save();
  assert.equal(store.storage.getItem(KEY), null);
  assert.equal(b.context.autosaveReady, false);
  assert.match(b.notice.textContent, /export JSON/);
});

test("unload warns about unsaved edits, but never performs a write", async () => {
  const store = shared(), a = tab(store);
  await a.init(); await a.save();
  let prevented = false;
  const event = {preventDefault: () => { prevented = true; }};
  a.events.beforeunload(event);
  assert.equal(prevented, false);
  a.edit(1); a.events.beforeunload(event);
  assert.equal(prevented, true);
  assert.equal(saved(store).snapshot.layout.placements.length, 0);
});
