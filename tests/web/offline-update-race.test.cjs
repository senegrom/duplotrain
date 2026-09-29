"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const {harness} = require("./reliability-harness.cjs");
const turn = () => new Promise(resolve => setImmediate(resolve));
function deferred() {
  let resolve, reject;
  const promise = new Promise((yes, no) => { resolve = yes; reject = no; });
  return {promise, resolve, reject};
}
function client({events = false} = {}) {
  const checking = deferred(), activating = deferred(), installing = deferred();
  const calls = [], messages = [], downloads = [];
  let reloads = 0, confirmations = 0;
  const worker = {state: "activated", addEventListener() {}, removeEventListener() {}};
  const registration = {waiting: worker, active: {}, scope: "https://example.test/train/",
    addEventListener() {}};
  const h = harness({events, omit: ["api"], overrides: {
    URL, isSecureContext: true, clearTimeout() {},
    window: {duplotrainBuild: "test-build", addEventListener() {},
      confirm() { confirmations++; return true; }, location: {reload() { reloads++; }}},
    navigator: {serviceWorker: {async register() { return registration; }}},
    send: async (path, body) => { calls.push({path, body}); return h.context.S; },
    downloadJSON(data, filename) { downloads.push({data, filename}); },
    offlineMessage: async (_worker, type) => {
      messages.push(type);
      return {STATUS: checking, ACTIVATE: activating, INSTALL: installing}[type].promise;
    },
  }});
  h.context.registration = registration; h.run("offlineRegistration = registration");
  return {...h, checking, activating, installing, calls, messages, downloads, worker,
    counts: () => ({reloads, confirmations})};
}
const paths = ["/api/attach", "/api/remove", "/api/import", "/api/project/open",
  "/api/undo", "/api/restore", "/api/search/start", "/api/routes/start"];
for (const phase of ["verification", "activation"]) {
  test(`update ${phase} excludes edits, imports and jobs at the real API guard`, async () => {
    const h = client(), before = JSON.stringify(h.context.S);
    const update = h.run("applyOfflineUpdate()");
    if (phase === "activation") { h.checking.resolve({ready: true}); await turn(); }
    assert.equal(h.run("apiBusy"), true);
    assert.equal(h.context.document.body.classList.contains("busy"), true);
    for (const path of paths) await assert.rejects(h.run(`api(${JSON.stringify(path)}, {})`), /action is still running/);
    assert.equal(h.calls.length, 0);
    assert.equal(JSON.stringify(h.context.S), before);
    assert.equal(h.counts().reloads, 0);
    h.checking.resolve({ready: true}); h.activating.resolve({activated: true});
    await update;
    assert.equal(h.counts().reloads, 1);
    assert.equal(h.calls.length, 0);
  });
}

test("an already-reading import cannot mutate the editor during update verification", async () => {
  const h = client({events: true}), file = deferred();
  const importing = h.el("importfile").fire("change", {target: {value: "track.json",
    files: [{size: 100, text: () => file.promise}]}});
  const update = h.run("applyOfflineUpdate()");
  file.resolve(JSON.stringify({format: "duplotrain-layout/1", placements: [], links: []}));
  await importing;
  assert.equal(h.calls.length, 0);
  assert.match(h.notices.at(-1).text, /action is still running/);
  h.checking.resolve({ready: true}); h.activating.resolve({activated: true});
  await update;
  assert.equal(h.counts().reloads, 1);
});

test("portable layout and project downloads remain available while applying", async () => {
  const h = client({events: true}); h.run("bindExtraEvents()");
  const update = h.run("applyOfflineUpdate()");
  h.el("export").click(); h.el("save-project").click();
  assert.deepEqual(h.downloads.map(d => d.filename), ["layout.json", "project.json"]);
  assert.equal(h.calls.length, 0);
  h.checking.reject(new Error("verification failed")); await update;
});

for (const failure of ["verification", "incomplete", "activation", "redundant"]) {
  test(`failed ${failure} releases the update exclusion and editing works again`, async () => {
    const h = client(), update = h.run("applyOfflineUpdate()");
    if (failure === "verification") h.checking.reject(new Error("verification failed"));
    else if (failure === "incomplete") h.checking.resolve({ready: false});
    else {
      h.checking.resolve({ready: true}); await turn();
      if (failure === "activation") h.activating.reject(new Error("activation failed"));
      else { h.worker.state = "redundant"; h.activating.resolve({activated: true}); }
    }
    await update;
    assert.equal(h.counts().reloads, 0);
    assert.equal(h.run("apiBusy || offlineWorking"), false);
    assert.equal(h.context.document.body.classList.contains("busy"), false);
    await h.run('api("/api/attach", {piece: "straight", entry: 0, at: null})');
    assert.equal(h.calls.length, 1);
  });
}

for (const phase of ["verification", "activation"]) {
  test(`a changed confirmed session during ${phase} is never reloaded`, async () => {
    const h = client(), update = h.run("applyOfflineUpdate()");
    if (phase === "activation") { h.checking.resolve({ready: true}); await turn(); }
    // Models a separately completing recovery/state publication, not a permitted edit.
    h.run("S = {...S, revision: S.revision + 1}");
    h.checking.resolve({ready: true}); h.activating.resolve({activated: true});
    await update;
    assert.equal(h.counts().reloads, 0);
    assert.match(h.el("offline-status").textContent, /editor changed/);
    assert.equal(h.run("apiBusy"), false);
    if (phase === "verification") assert.deepEqual(h.messages, ["STATUS"]);
  });
}

test("a waiting worker replaced during verification is not activated without its own check", async () => {
  const h = client(), update = h.run("applyOfflineUpdate()");
  h.context.registration.waiting = {};
  h.checking.resolve({ready: true}); await update;
  assert.deepEqual(h.messages, ["STATUS"]); assert.equal(h.counts().reloads, 0);
  assert.match(h.el("offline-status").textContent, /replaced/);
});

test("repeated Apply update clicks share neither a second confirmation nor a second reload", async () => {
  const h = client(), update = h.run("applyOfflineUpdate()");
  await h.run("applyOfflineUpdate()");
  assert.equal(h.counts().confirmations, 1);
  h.checking.resolve({ready: true}); h.activating.resolve({activated: true}); await update;
  assert.equal(h.counts().reloads, 1);
});

test("offline downloads remain nonblocking for normal editor requests", async () => {
  const h = client(), download = h.run("installOffline()");
  await turn();
  assert.equal(h.run("offlineWorking"), true);
  assert.equal(h.run("apiBusy"), false);
  await h.run('api("/api/attach", {piece: "straight", entry: 0, at: null})');
  assert.equal(h.calls.length, 1);
  h.installing.reject(new Error("test ends download")); await download;
  assert.equal(h.counts().reloads, 0);
});
