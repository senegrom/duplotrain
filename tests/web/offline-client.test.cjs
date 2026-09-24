"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness} = require("./reliability-harness.cjs");
// A service worker whose state changes the test announces with emit().
function serviceWorker(state) {
  const listeners = new Set();
  return {state, addEventListener(_name, fn) { listeners.add(fn); },
    removeEventListener(_name, fn) { listeners.delete(fn); }, emit() { for (const fn of [...listeners]) fn(); }};
}
function client({confirm = true, ready = true, waiting = false, fail = false, existing = false,
  activeBuild = "test-build", workerState = "activated"} = {}) {
  let reloads = 0, registrations = 0, confirmations = 0, updates = 0;
  const messages = [], registrationListeners = {};
  const worker = serviceWorker(workerState);
  const registration = {scope: "https://example.test/train/", active: waiting ? null : worker,
    waiting: waiting ? worker : null, installing: null,
    addEventListener(name, fn) { registrationListeners[name] = fn; }, async update() { updates++; }};
  const h = harness({overrides: {isSecureContext: true, URL, clearTimeout() {},
    location: {href: "https://example.test/train/index.html", pathname: "/train/index.html"},
    window: {duplotrainBuild: "test-build", addEventListener() {},
      confirm() { confirmations++; return confirm; }, location: {reload() { reloads++; }}},
    navigator: {serviceWorker: {async getRegistration() { return existing ? registration : null; },
      async register() { registrations++; return registration; }}},
    offlineMessage: async (_worker, type) => {
      messages.push(type);
      if (fail) throw new Error("Download failed; previous cache retained");
      return {ready, build: activeBuild};
    }}});
  h.context.registration = registration;
  return {...h, messages, worker, registrationEvent: name => registrationListeners[name](),
    counts: () => ({reloads, registrations, confirmations}), updates: () => updates};
}
const turn = () => new Promise(resolve => setImmediate(resolve));

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

test("another active offline build without a waiting update offers no update to apply", async () => {
  // Reloading would open the active build, which may be older than this page.
  const h = client({existing: true, activeBuild: "other-build"}); h.run("bindOfflineEvents()");
  await new Promise(resolve => setImmediate(resolve));
  assert.match(h.el("offline-status").textContent, /Offline build other-build is ready/);
  assert.equal(h.el("offline-update").hidden, true);
});

test("an applied update reloads only once the waiting version has activated", async () => {
  const h = client({waiting: true, workerState: "installed"}); h.run("offlineRegistration = registration");
  const applying = h.run("applyOfflineUpdate()");
  await turn();
  assert.deepEqual(h.messages, ["STATUS", "ACTIVATE"]);
  h.worker.state = "activating"; h.worker.emit();
  await turn();
  assert.equal(h.counts().reloads, 0);
  h.worker.state = "activated"; h.worker.emit();
  await applying;
  assert.equal(h.counts().reloads, 1);
});

for (const flag of ["apiBusy", "offlineWorking"]) {
  test(`${flag} prevents update confirmation, activation and reload`, async () => {
    const h = client({waiting: true}); h.run(`offlineRegistration = registration; ${flag} = true`);
    await h.run("applyOfflineUpdate()");
    assert.deepEqual(h.messages, []);
    assert.deepEqual(h.counts(), {reloads: 0, registrations: 0, confirmations: 0});
    assert.match(h.el("offline-status").textContent, /Finish or pause the current operation/);
  });
}

test("startup with a verified waiting update offers Apply update but applies nothing", async () => {
  const h = client({existing: true, waiting: true, activeBuild: "next-build"});
  h.el("offline-update").hidden = true; h.run("bindOfflineEvents()");
  await turn();
  assert.equal(h.el("offline-update").hidden, false);
  assert.deepEqual(h.messages, ["STATUS"]);
  assert.deepEqual(h.counts(), {reloads: 0, registrations: 0, confirmations: 0});
});

test("checking for an update reports it but never reloads or activates", async () => {
  const h = client({existing: true, waiting: true});
  h.run("offlineRegistration = registration"); h.el("offline-update").hidden = true;
  await h.run("checkOfflineUpdate()");
  assert.equal(h.updates(), 1);
  assert.deepEqual(h.messages, ["STATUS"]);
  assert.deepEqual(h.counts(), {reloads: 0, registrations: 0, confirmations: 0});
  assert.equal(h.el("offline-update").hidden, false);
});

for (const outcome of ["installed", "redundant"]) {
  test(`a background update that ends ${outcome} is reported and never reloads`, async () => {
    const h = client({existing: true}); h.run("bindOfflineEvents()");
    await turn();
    h.el("offline-update").hidden = true;
    const next = serviceWorker("installing");
    h.context.registration.installing = next; h.registrationEvent("updatefound");
    Object.assign(h.context.registration, {installing: null, waiting: outcome === "installed" ? next : null});
    next.state = outcome; next.emit();
    assert.equal(h.el("offline-update").hidden, outcome !== "installed");
    assert.match(h.el("offline-status").textContent, outcome === "installed" ?
      /Update available and verified/ : /Update failed; existing version kept/);
    assert.equal(h.counts().reloads, 0);
  });
}

test("an installation whose worker turns redundant is reported as failed, never as installed", async () => {
  const h = client(); const next = serviceWorker("installing");
  Object.assign(h.context.registration, {installing: next, active: null});
  const installing = h.run("installOffline()");
  await turn();
  next.state = "redundant"; next.emit();
  await installing;
  assert.deepEqual(h.messages, []);  // the failed worker is never asked to install
  assert.match(h.el("offline-status").textContent, /installation failed.*Previous version kept/);
});

test("offline installation outside a secure context registers nothing", async () => {
  const h = client(); h.context.isSecureContext = false;
  await h.run("installOffline()");
  assert.equal(h.counts().registrations, 0);
  assert.match(h.el("offline-status").textContent, /HTTPS or localhost/);
});

test("startup ignores an offline registration made for another scope", async () => {
  const h = client({existing: true}); h.context.registration.scope = "https://example.test/";
  h.run("bindOfflineEvents()");
  await turn();
  assert.equal(h.run("offlineRegistration"), null);
  assert.deepEqual(h.messages, []);
});
