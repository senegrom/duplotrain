"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness} = require("./reliability-harness.cjs");
function client({confirm = true, ready = true, waiting = false, fail = false, existing = false} = {}) {
  let reloads = 0, registrations = 0, confirmations = 0;
  const messages = [];
  const worker = {state: "activated"};
  const registration = {scope: "https://example.test/train/", active: waiting ? null : worker,
    waiting: waiting ? worker : null, addEventListener() {}, async update() {}};
  const h = harness({overrides: {isSecureContext: true, URL,
    location: {href: "https://example.test/train/index.html", pathname: "/train/index.html"},
    window: {duplotrainBuild: "test-build", addEventListener() {},
      confirm() { confirmations++; return confirm; }, location: {reload() { reloads++; }}},
    navigator: {serviceWorker: {async getRegistration() { return existing ? registration : null; },
      async register() { registrations++; return registration; }}},
    offlineMessage: async (_worker, type) => {
      messages.push(type);
      if (fail) throw new Error("Download failed; previous cache retained");
      return {ready, build: "test-build"};
    }}});
  h.context.registration = registration;
  return {...h, messages, counts: () => ({reloads, registrations, confirmations})};
}

test("offline startup without a registration installs nothing", async () => {
  const h = client(); h.run("bindOfflineEvents()");
  await new Promise(resolve => setImmediate(resolve));
  assert.deepEqual(h.counts(), {reloads: 0, registrations: 0, confirmations: 0});
  assert.match(h.el("offline-status").textContent, /opt-in/);
});

test("offline startup adopts an existing registration without installing or reloading", async () => {
  const h = client({existing: true}); h.run("bindOfflineEvents()");
  await new Promise(resolve => setImmediate(resolve));
  assert.deepEqual(h.counts(), {reloads: 0, registrations: 0, confirmations: 0});
  assert.equal(h.run("offlineRegistration"), h.context.registration);
  assert.deepEqual(h.messages, ["STATUS"]);
  assert.match(h.el("offline-status").textContent, /Offline ready/);
});

test("declining an offline update never activates or reloads", async () => {
  const h = client({confirm: false, waiting: true});
  h.run("offlineRegistration = registration");
  await h.run("applyOfflineUpdate()");
  assert.deepEqual(h.messages, []); assert.equal(h.counts().reloads, 0);
});

for (const waiting of [false, true]) {
  test(`incomplete ${waiting ? "waiting" : "active"} offline version cannot reload`, async () => {
    const h = client({ready: false, waiting}); h.run("offlineRegistration = registration");
    await h.run("applyOfflineUpdate()");
    assert.deepEqual(h.messages, ["STATUS"]); assert.equal(h.counts().reloads, 0);
    assert.match(h.el("offline-status").textContent, /incomplete/);
    assert.equal(h.run("offlineWorking"), false);
  });
}

test("a ready waiting version activates only after confirmation and then reloads", async () => {
  const h = client({waiting: true}); h.run("offlineRegistration = registration");
  await h.run("applyOfflineUpdate()");
  assert.deepEqual(h.messages, ["STATUS", "ACTIVATE"]);
  assert.equal(h.counts().confirmations, 1); assert.equal(h.counts().reloads, 1);
});

test("failed offline installation keeps the editor and portable download route", async () => {
  const h = client({fail: true}); const before = JSON.stringify(h.context.S);
  await h.run("installOffline()");
  assert.equal(h.counts().reloads, 0); assert.equal(JSON.stringify(h.context.S), before);
  assert.match(h.el("offline-status").textContent, /previous cache retained/);
  assert.match(h.el("offline-status").textContent, /Portable project downloads/);
});

test("busy search prevents update confirmation, activation and reload", async () => {
  const h = client({waiting: true}); h.run("offlineRegistration = registration; solving = true");
  await h.run("applyOfflineUpdate()");
  assert.deepEqual(h.messages, []);
  assert.deepEqual(h.counts(), {reloads: 0, registrations: 0, confirmations: 0});
});
