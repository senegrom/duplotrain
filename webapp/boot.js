/* Bridge the editor to the worker. __BUILD__ is replaced by webapp/build.py. */
"use strict";
window.duplotrainBuild = "__BUILD__";

(function () {
  let worker = null, ready = false, seq = 0;
  let options, overlay, msg, rejectReady, bootTimer, idleTimer;
  let recoveryButtons = false, restarting = false;
  const pending = new Map();

  function clearTimers() { clearTimeout(bootTimer); clearTimeout(idleTimer); }
  function stop(error) {
    clearTimers(); ready = false;
    if (worker) worker.terminate();
    worker = null;
    if (rejectReady) { rejectReady(error); rejectReady = null; }
    for (const call of pending.values()) call.reject(error);
    pending.clear();
  }
  function button(text, callback) {
    const b = document.createElement("button"); b.textContent = text;
    b.addEventListener("click", () => {
      try { const result = callback(); if (result?.catch) result.catch(fail); }
      catch (error) { msg.textContent = error.message; }
    });
    overlay.append(b);
  }
  function fail(error) {
    const err = error instanceof Error ? error : new Error(String(error));
    stop(err);
    msg.textContent = "Track engine unavailable: " + err.message.slice(0, 300);
    if (!overlay.isConnected) document.body.append(overlay);
    if (!recoveryButtons) {
      recoveryButtons = true;
      if (options.checkpoint?.()) {
        button("Download last confirmed layout", options.downloadLayout);
        button("Download last confirmed session", options.downloadSession);
        button("Restart engine and restore last confirmed session", restart);
      }
      button("Reload and recover autosave", () => location.reload());
    }
  }
  function heartbeat() {
    clearTimeout(idleTimer);
    // Every request is short, a search tick included: a silent engine is stuck.
    if (pending.size) idleTimer = setTimeout(() => fail(new Error(
      "No engine response for two minutes. The last confirmed session can be downloaded."
    )), 120000);
  }
  window.duplotrainApi = (path, body) => new Promise((resolve, reject) => {
    if (!worker || !ready) return reject(new Error("engine is not ready"));
    const id = ++seq;
    try {
      const encoded = body === undefined ? null : JSON.stringify(body);
      pending.set(id, {resolve, reject});
      worker.postMessage({id, path, body: encoded}); heartbeat();
    } catch (error) { pending.delete(id); heartbeat(); reject(error); }
  }).then(res => {
    const data = JSON.parse(res);
    if (data.__error) {
      const error = new Error(data.__error); error.code = data.code; error.state = data.state;
      error.refused = true;  // the engine answered and turned the request down
      throw error;
    }
    return data;
  });

  async function start(snapshot = null) {
    msg.textContent = snapshot ? "Restarting the track engine; restoring the last confirmed session…" :
      "Loading the track engine… (cached on this device for later visits)";
    if (!overlay.isConnected) document.body.append(overlay);
    try {
      await new Promise((resolve, reject) => {
        rejectReady = reject;
        const current = new Worker("./worker.js?v=__BUILD__");
        worker = current;
        current.onerror = event => {
          event.preventDefault();
          if (worker === current) fail(new Error(event.message || "worker error"));
        };
        current.onmessageerror = () => { if (worker === current) fail(new Error("invalid worker message")); };
        current.addEventListener("message", ({data}) => {
          // Late responses from an old generation must never restore old state.
          if (worker !== current) return;
          if (data && data.bootError) { fail(new Error(data.bootError)); return; }
          if (data && data.ready) {
            ready = true; clearTimeout(bootTimer); rejectReady = null; resolve(); return;
          }
          if (data?.fatal) { fail(new Error(`The engine failed and must restart (${data.fatal})`)); return; }
          const {id, res, err} = data || {}, call = pending.get(id);
          if (!call) return;
          pending.delete(id); heartbeat();
          if (err) call.reject(new Error(err)); else call.resolve(res);
        });
        bootTimer = setTimeout(() => fail(new Error("engine loading timed out")), 60000);
      });
      if (snapshot) {
        const state = await window.duplotrainApi("/api/restore", {
          data: snapshot, revision: 0, preview_format: "duplotrain-preview/1",
        });
        await options.restored(state);
      } else await options.refresh();
      // The editor tolerates a failed startup restore; a worker that died during
      // it has already put up the recovery overlay, which must stay.
      if (!ready) return;
      overlay.remove();
      (options.readyStatus || options.status)(snapshot ?
        "Engine restarted; last confirmed session restored. Previous undo history and suggestions were reset." :
        "Engine ready — runs in your browser · build __BUILD__");
    } catch (error) { fail(error); }
  }
  async function restart() {
    if (restarting) return;
    restarting = true;
    try {
      // Only the failure overlay offers a restart: fail() has stopped the old
      // engine already. Copy the snapshot; recovery never falls back to a
      // different tab's save.
      const snapshot = options.checkpoint?.();
      const saved = snapshot ? JSON.parse(JSON.stringify(snapshot)) : null;
      await start(saved);
    } finally { restarting = false; }
  }
  window.duplotrainBoot = async supplied => {
    options = supplied;
    overlay = document.createElement("div");
    overlay.style.cssText =
      "position:fixed;inset:0;background:rgba(244,242,238,.96);z-index:50;" +
      "display:flex;flex-direction:column;gap:12px;align-items:center;justify-content:center;" +
      "font:15px/1.6 system-ui;color:#2b2f33;text-align:center;padding:20px";
    msg = document.createElement("div"); overlay.append(msg); document.body.append(overlay);
    await start();
  };
})();
