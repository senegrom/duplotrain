"use strict";
// Offline caches contain application code only. Project storage remains separate.
let offlineRegistration = null, offlineWorking = false;
// Error texts may or may not end their sentence; a notice goes on after them.
const sentence = text => /[.!?]$/.test(text) ? text : `${text}.`;
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
  const same = result.build === window.duplotrainBuild;
  offlineNotice(result.ready ? (same ? "Offline ready (verified complete app)." :
    `Offline build ${result.build} is ready. Save your project before reloading it.`) :
    "Offline files are missing or incomplete. Reinstall while online.");
  // Only a waiting version is an update: reloading otherwise opens the active
  // offline build, which may be older than this page.
  el("offline-update").hidden = !r.waiting;
}
// The browser hands back the same registration each time: listen to it once.
const watchedRegistrations = new WeakSet();
function watchOfflineUpdates(r) {
  if (watchedRegistrations.has(r)) return;
  watchedRegistrations.add(r);
  r.addEventListener("updatefound", () => {
    // Without an active version this is a first installation, which activates by
    // itself (browsers list it as waiting for a moment all the same).
    const installing = r.installing, update = !!r.active;
    installing?.addEventListener("statechange", () => {
      if (installing.state === "installed" && update) {
        el("offline-update").hidden = false;
        offlineNotice("Update available and verified. Save a project before applying it; no automatic reload.");
      } else if (installing.state === "activated" && !update) {
        showOfflineStatus().catch(error => offlineNotice(sentence(error.message)));
      } else if (installing.state === "redundant") {
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
    const worker = await awaitOfflineWorker(r);
    const result = await offlineMessage(worker, "INSTALL");
    offlineNotice(result.ready && result.build === window.duplotrainBuild ? "Offline ready (complete version verified)." :
      `Build ${result.build} is ready offline. Save your project before switching versions.`);
    el("offline-update").hidden = !r.waiting;
  } catch (error) { offlineNotice(`${sentence(error.message)} Portable project downloads remain available.`); }
  finally { offlineWorking = false; }
}
async function checkOfflineUpdate() {
  if (offlineWorking) return;
  try {
    if (!offlineRegistration) { offlineNotice("Install offline access first. The normal online app revalidates on reload."); return; }
    await offlineRegistration.update();
    if (offlineRegistration.installing) await awaitOfflineWorker(offlineRegistration);
    await showOfflineStatus();
  } catch (error) { offlineNotice(`Update check failed: ${sentence(error.message)} Existing offline version kept.`); }
}
async function applyOfflineUpdate() {
  if (offlineWorking || jobLoop || apiBusy) { offlineNotice("Finish or pause the current operation before updating."); return; }
  if (!window.confirm("Reload the app with the verified offline version? Download a project first. In-memory undo and search progress will be reset.")) return;
  offlineWorking = true;
  try {
    const r = offlineRegistration;
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
  // Read existing registrations without registering/installing anything silently.
  navigator.serviceWorker.getRegistration(new URL("./", location.href).href).then(r => {
    const scope = new URL("./", location.href).href;
    if (!r || r.scope !== scope) return;
    offlineRegistration = r; watchOfflineUpdates(r);
    if (r.active || r.waiting) return showOfflineStatus();
  }).catch(error => offlineNotice(sentence(error.message)));
}
