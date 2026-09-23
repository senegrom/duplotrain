"use strict";
// Offline caches contain application code only. Project storage remains separate.
let offlineRegistration = null, offlineWorking = false;
function offlineNotice(message) {
  if (el("offline-status")) el("offline-status").textContent =
    `Build ${window.duplotrainBuild || "local server"}. ${message}`;
}
function offlineMessage(worker, type) {
  return new Promise((resolve, reject) => {
    if (!worker) { reject(new Error("Offline worker is not ready")); return; }
    const channel = new MessageChannel();
    const timer = setTimeout(() => { channel.port1.close(); reject(new Error("Offline operation timed out; the existing version was kept")); }, 180000);
    channel.port1.onmessage = event => {
      clearTimeout(timer); channel.port1.close();
      if (event.data.error) reject(new Error(event.data.error)); else resolve(event.data);
    };
    worker.postMessage({type}, [channel.port2]);
  });
}
function awaitOfflineWorker(registration) {
  const worker = registration.installing || registration.waiting || registration.active;
  if (!worker) return Promise.reject(new Error("Offline worker was not created"));
  if (["installed", "activating", "activated"].includes(worker.state)) return Promise.resolve(worker);
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => { worker.removeEventListener("statechange", change); reject(new Error("Offline installation timed out")); }, 180000);
    const change = () => {
      if (["installed", "activating", "activated", "redundant"].includes(worker.state)) {
        clearTimeout(timer); worker.removeEventListener("statechange", change);
        if (worker.state === "redundant") reject(new Error("Offline installation failed; retry online. Previous version kept.")); else resolve(worker);
      }
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
  if (el("offline-update")) el("offline-update").hidden = !r.waiting && same;
}
function watchOfflineUpdates(r) {
  r.addEventListener("updatefound", () => {
    const installing = r.installing;
    installing?.addEventListener("statechange", () => {
      if (installing.state === "installed") {
        if (r.waiting) {
          el("offline-update").hidden = false;
          offlineNotice("Update available and verified. Save a project before applying it; no automatic reload.");
        } else showOfflineStatus().catch(error => offlineNotice(error.message));
      }
      if (installing.state === "redundant") offlineNotice("Update failed; existing version kept. Retry online.");
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
    el("offline-update").hidden = !r.waiting && result.build === window.duplotrainBuild;
  } catch (error) { offlineNotice(`${error.message} Portable project downloads remain available.`); }
  finally { offlineWorking = false; }
}
async function checkOfflineUpdate() {
  if (offlineWorking) return;
  try {
    if (!offlineRegistration) { offlineNotice("Install offline access first. The normal online app revalidates on reload."); return; }
    await offlineRegistration.update();
    if (offlineRegistration.installing) await awaitOfflineWorker(offlineRegistration);
    await showOfflineStatus();
  } catch (error) { offlineNotice(`Update check failed: ${error.message}. Existing offline version kept.`); }
}
async function applyOfflineUpdate() {
  if (offlineWorking || solving || apiBusy) { offlineNotice("Finish or pause the current operation before updating."); return; }
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
  } catch (error) { offlineNotice(error.message); }
  finally { offlineWorking = false; }
}
function bindOfflineEvents() {
  const on = (id, fn) => el(id)?.addEventListener("click", fn);
  on("offline-install", installOffline); on("offline-check", checkOfflineUpdate); on("offline-update", applyOfflineUpdate);
  offlineNotice(window.duplotrainBuild ? "Offline access is opt-in." : "Offline installation is available in the browser-engine app.");
  if (!window.duplotrainBuild || !navigator.serviceWorker || !globalThis.isSecureContext) {
    for (const id of ["offline-install", "offline-check"]) if (el(id)) el(id).disabled = true;
    return;
  }
  // Read existing registrations without registering/installing anything silently.
  navigator.serviceWorker.getRegistration(new URL("./", location.href).href).then(r => {
    const scope = new URL("./", location.href).href;
    if (!r || r.scope !== scope) return;
    offlineRegistration = r; watchOfflineUpdates(r);
    if (r.active || r.waiting) return showOfflineStatus();
  }).catch(error => offlineNotice(error.message));
}
