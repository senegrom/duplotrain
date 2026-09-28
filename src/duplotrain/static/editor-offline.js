"use strict";
// Offline caches contain application code only. Project storage remains separate.
let offlineRegistration = null, offlineWorking = false;
// Error texts may or may not end their sentence; a notice goes on after them.
const sentence = text => /[.!?]$/.test(text) ? text : `${text}.`;
const UPDATE_READY = "Update available and verified. Save a project before applying it; no automatic reload.";
const INSTALLED = ["installed", "activating", "activated"];
function offlineNotice(message) {
  el("offline-status").textContent = `Build ${window.duplotrainBuild || "local server"}. ${message}`;
}
function offlineMessage(worker, type) {
  return new Promise((resolve, reject) => {
    if (!worker) { reject(new Error("Offline worker is not ready.")); return; }
    const channel = new MessageChannel();
    let timer;
    // A service worker still working says so every 20 seconds, however long a
    // download takes: only a silent minute means it stopped.
    const wait = () => {
      clearTimeout(timer);
      timer = setTimeout(() => { channel.port1.close(); reject(new Error("The offline worker stopped responding.")); }, 60000);
    };
    channel.port1.onmessage = event => {
      if (event.data.working) { wait(); return; }
      clearTimeout(timer); channel.port1.close();
      if (event.data.error) reject(new Error(event.data.error)); else resolve(event.data);
    };
    wait();
    worker.postMessage({type}, [channel.port2]);
  });
}
// Settle once *worker* reaches one of *states*. A worker that turns redundant, or
// that has not got there within *ms* when a limit is given, fails with *failure*.
function untilState(worker, states, failure, ms = 0) {
  return new Promise((resolve, reject) => {
    let timer = null;
    const settle = done => { worker.removeEventListener("statechange", change); clearTimeout(timer); done(); };
    const change = () => {
      if (states.includes(worker.state)) settle(() => resolve(worker));
      else if (worker.state === "redundant") settle(() => reject(new Error(failure)));
    };
    if (ms) timer = setTimeout(() => settle(() => reject(new Error(failure))), ms);
    worker.addEventListener("statechange", change); change();
  });
}
// Workers this page asked to install: that request reports how they end.
const requestedWorkers = new WeakSet();
// A worker answers INSTALL once its download is verified, or says why it failed.
// One that fails before it reads the request turns redundant all the same.
async function installVerified(worker, failure) {
  requestedWorkers.add(worker);
  const reply = offlineMessage(worker, "INSTALL");
  if (INSTALLED.includes(worker.state)) return reply;  // repairs a verified version
  // WebKit may report the worker redundant just before its reply says why: a
  // redundant worker fails the installation once its reply has had a second.
  const settled = untilState(worker, INSTALLED, failure).catch(error =>
    Promise.race([reply, new Promise(resolve => setTimeout(resolve, 1000))])
      .then(() => { throw error; }));
  reply.catch(() => {}); settled.catch(() => {});  // whichever fails first explains it
  await Promise.race([reply, settled]);
  return settled;
}
async function showOfflineStatus(note = "") {
  const r = offlineRegistration;
  if (!r) { offlineNotice("Not installed for offline use."); return; }
  const result = await offlineMessage(r.active || r.waiting, "STATUS");
  // Only a version waiting behind an active one is an update: reloading otherwise
  // opens the active offline build, which may be older than this page.
  const update = !!(r.waiting && r.active);
  offlineNotice(update ? UPDATE_READY : note + (!result.ready ?
    "Offline files are missing or incomplete. Reinstall while online." :
    result.build === window.duplotrainBuild ? "Offline ready (verified complete app)." :
    `Offline build ${result.build} is ready. Save your project before reloading it.`));
  el("offline-update").hidden = !update;
}
// Read the registration without registering or installing anything: another tab
// may have installed offline access since this one started.
async function findRegistration() {
  const scope = new URL("./", location.href).href;
  const r = await navigator.serviceWorker.getRegistration(scope);
  if (!r || r.scope !== scope) return null;
  offlineRegistration = r; watchOfflineUpdates(r);
  return r;
}
// The browser hands back the same registration each time: listen to it once, and
// to each installing worker once, including one already under way at startup.
const watchedRegistrations = new WeakSet(), watchedWorkers = new WeakSet();
function watchOfflineUpdates(r) {
  if (watchedRegistrations.has(r)) return;
  watchedRegistrations.add(r);
  r.addEventListener("updatefound", () => watchInstalling(r, r.installing));
  watchInstalling(r, r.installing);
}
function watchInstalling(r, installing) {
  if (!installing || watchedWorkers.has(installing)) return;
  watchedWorkers.add(installing);
  // Without an active version this is a first installation, which activates by
  // itself (browsers list it as waiting for a moment all the same). A version
  // that installed and is later replaced turns redundant too: that is no failure.
  const update = !!r.active;
  let installed = false;
  installing.addEventListener("statechange", () => {
    const state = installing.state;
    installed ||= state === "installed";
    // An installation this page asked for, or an update it applies, reports itself.
    if (offlineWorking || requestedWorkers.has(installing)) return;
    if (state === "installed" && update) {
      el("offline-update").hidden = false;
      offlineNotice(UPDATE_READY);
    } else if (state === "activated" && !update) {
      showOfflineStatus().catch(error => offlineNotice(sentence(error.message)));
    } else if (state === "redundant" && !installed) {
      offlineNotice(update ? "Update failed; the existing version was kept. Retry online." :
        "Offline installation failed. Retry online.");
    }
  });
}
async function installOffline() {
  if (offlineWorking) return;
  offlineWorking = true;
  try {
    if (!window.duplotrainBuild || !navigator.serviceWorker || !globalThis.isSecureContext)
      throw new Error("Offline installation needs the browser-engine app on HTTPS or localhost.");
    offlineNotice("Downloading and verifying the complete application…");
    const r = await navigator.serviceWorker.register("./service-worker.js", {scope: "./", updateViaCache: "none"});
    offlineRegistration = r; watchOfflineUpdates(r);
    const worker = r.installing || r.waiting || r.active;
    if (!worker) throw new Error("Offline worker was not created.");
    await installVerified(worker, r.active ?
      "Offline installation failed; the existing version was kept. Retry online." :
      "Offline installation failed. Retry online.");
    await showOfflineStatus();
  } catch (error) { offlineNotice(`${sentence(error.message)} Portable project downloads remain available.`); }
  finally { offlineWorking = false; }
}
// A check does not hold offlineWorking: an update the browser found by itself may
// already be offered, and applying it must not wait for the check.
async function checkOfflineUpdate() {
  if (offlineWorking) return;
  try {
    const r = offlineRegistration || await findRegistration();
    if (!r) { offlineNotice("Install offline access first. The normal online app revalidates on reload."); return; }
    offlineNotice("Checking for an update…");
    await r.update();
    const found = r.installing;
    if (found) {
      offlineNotice("Downloading and verifying the update…");
      await installVerified(found, "The update did not install; the existing version was kept. Retry online.");
    }
    await showOfflineStatus(found ? "" : "No newer version found. ");
  } catch (error) { offlineNotice(`Update check failed: ${sentence(error.message)}`); }
}
async function applyOfflineUpdate() {
  if (offlineWorking || jobLoop || apiBusy) { offlineNotice("Finish or pause the current operation before updating."); return; }
  if (!window.confirm("Reload the app with the verified offline version? Download a project first. In-memory undo and search progress will be reset.")) return;
  // Own the existing API exclusion before the first await: pending imports and
  // new edits/jobs must not run between update verification and reload. Background
  // installation does not take this lock; portable downloads do not need it.
  offlineWorking = apiBusy = true; refreshBusy();
  const confirmedState = S;
  const checkIdle = () => {
    if (!apiBusy || jobLoop || S !== confirmedState)
      throw new Error("The editor changed while applying the update; no reload performed. Try again.");
  };
  try {
    const r = offlineRegistration || await findRegistration();
    if (!r) throw new Error("No offline version is installed");
    const worker = r.waiting || r.active, waiting = worker === r.waiting;
    if (!(await offlineMessage(worker, "STATUS")).ready)
      throw new Error("Offline version is incomplete; reinstall online before reloading.");
    checkIdle();
    if (waiting) {
      if (r.waiting !== worker && r.active !== worker)
        throw new Error("The offline update was replaced; check for an update again.");
      await offlineMessage(worker, "ACTIVATE");
      await untilState(worker, ["activated"], "Update did not activate; no reload performed", 15000);
    }
    checkIdle();
    window.location.reload();
  } catch (error) { offlineNotice(sentence(error.message)); }
  finally { offlineWorking = apiBusy = false; refreshBusy(); }
}
function bindOfflineEvents() {
  on("offline-install", installOffline); on("offline-check", checkOfflineUpdate); on("offline-update", applyOfflineUpdate);
  offlineNotice(window.duplotrainBuild ? "Offline access is opt-in." : "Offline installation is available in the browser-engine app.");
  if (!window.duplotrainBuild || !navigator.serviceWorker || !globalThis.isSecureContext) {
    for (const id of ["offline-install", "offline-check"]) el(id).disabled = true;
    return;
  }
  findRegistration().then(r => { if (r && (r.active || r.waiting)) return showOfflineStatus(); })
    .catch(error => offlineNotice(sentence(error.message)));
}
