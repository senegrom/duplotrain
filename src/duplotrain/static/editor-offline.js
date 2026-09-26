"use strict";
// Offline caches contain application code only. Project storage remains separate.
let offlineRegistration = null, offlineWorking = false;
// Error texts may or may not end their sentence; a notice goes on after them.
const sentence = text => /[.!?]$/.test(text) ? text : `${text}.`;
const UPDATE_READY = "Update available and verified. Save a project before applying it; no automatic reload.";
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
// The browser settles every installation, as installed or as redundant.
function awaitOfflineWorker(registration) {
  const worker = registration.installing || registration.waiting || registration.active;
  if (!worker) return Promise.reject(new Error("Offline worker was not created."));
  if (["installed", "activating", "activated"].includes(worker.state)) return Promise.resolve(worker);
  return new Promise((resolve, reject) => {
    const change = () => {
      if (!["installed", "activating", "activated", "redundant"].includes(worker.state)) return;
      worker.removeEventListener("statechange", change);
      if (worker.state !== "redundant") resolve(worker);
      else reject(new Error(registration.active ? "Offline installation failed; the existing version was kept. Retry online." :
        "Offline installation failed. Retry online."));
    };
    worker.addEventListener("statechange", change); change();
  });
}
async function showOfflineStatus() {
  const r = offlineRegistration;
  if (!r) { offlineNotice("Not installed for offline use."); return; }
  const result = await offlineMessage(r.active || r.waiting, "STATUS");
  // Only a version waiting behind an active one is an update: reloading otherwise
  // opens the active offline build, which may be older than this page.
  const update = !!(r.waiting && r.active);
  offlineNotice(update ? UPDATE_READY : !result.ready ?
    "Offline files are missing or incomplete. Reinstall while online." :
    result.build === window.duplotrainBuild ? "Offline ready (verified complete app)." :
    `Offline build ${result.build} is ready. Save your project before reloading it.`);
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
// The browser hands back the same registration each time: listen to it once.
const watchedRegistrations = new WeakSet();
function watchOfflineUpdates(r) {
  if (watchedRegistrations.has(r)) return;
  watchedRegistrations.add(r);
  r.addEventListener("updatefound", () => {
    // Without an active version this is a first installation, which activates by
    // itself (browsers list it as waiting for a moment all the same). A version
    // that installed and is later replaced turns redundant too: that is no failure.
    const installing = r.installing, update = !!r.active;
    let installed = false;
    installing?.addEventListener("statechange", () => {
      const state = installing.state;
      installed ||= state === "installed";
      if (offlineWorking) return;  // an installation or an update applied reports itself
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
    await offlineMessage(await awaitOfflineWorker(r), "INSTALL");
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
    await r.update();
    if (r.installing) await awaitOfflineWorker(r);
    await showOfflineStatus();
  } catch (error) { offlineNotice(`Update check failed: ${sentence(error.message)}`); }
}
async function applyOfflineUpdate() {
  if (offlineWorking || jobLoop || apiBusy) { offlineNotice("Finish or pause the current operation before updating."); return; }
  if (!window.confirm("Reload the app with the verified offline version? Download a project first. In-memory undo and search progress will be reset.")) return;
  offlineWorking = true;
  try {
    const r = offlineRegistration || await findRegistration();
    if (!r) throw new Error("No offline version is installed");
    if (!(await offlineMessage(r.waiting || r.active, "STATUS")).ready)
      throw new Error("Offline version is incomplete; reinstall online before reloading.");
    if (r.waiting) {
      const worker = r.waiting;
      await offlineMessage(worker, "ACTIVATE");
      await new Promise((resolve, reject) => {
        if (worker.state === "activated") { resolve(); return; }
        const timer = setTimeout(() => reject(new Error("Update did not activate; no reload performed")), 15000);
        const change = () => { if (worker.state === "activated") { clearTimeout(timer); worker.removeEventListener("statechange", change); resolve(); } };
        worker.addEventListener("statechange", change); change();
      });
    }
    window.location.reload();
  } catch (error) { offlineNotice(sentence(error.message)); }
  finally { offlineWorking = false; }
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
