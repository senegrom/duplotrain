/* Bridge the editor to the worker. __BUILD__ is replaced by webapp/build.py. */
"use strict";

(function () {
  let worker = null;
  let ready = false;
  let seq = 0;
  const pending = new Map();

  window.duplotrainApi = (path, body) => new Promise((resolve, reject) => {
    if (!worker || !ready) return reject(new Error("engine is not ready"));
    const id = ++seq;
    try {
      const encoded = body === undefined ? null : JSON.stringify(body);
      pending.set(id, {resolve, reject});
      worker.postMessage({id, path, body: encoded});
    } catch (error) {
      pending.delete(id);
      reject(error);
    }
  }).then((res) => {
    const data = JSON.parse(res);
    if (data.__error) throw new Error(data.__error);
    return data;
  });

  window.duplotrainBoot = async ({refresh, status, readyStatus = status}) => {
    const overlay = document.createElement("div");
    overlay.style.cssText =
      "position:fixed;inset:0;background:rgba(244,242,238,.96);z-index:50;" +
      "display:flex;flex-direction:column;align-items:center;justify-content:center;" +
      "font:15px/1.6 system-ui;color:#2b2f33;text-align:center;padding:20px";
    const msg = document.createElement("div");
    msg.textContent = "Loading the track engine… (cached on this device for later visits)";
    overlay.append(msg);
    document.body.append(overlay);
    let rejectReady;
    let timer;
    const fail = (error) => {
      clearTimeout(timer);
      ready = false;
      if (worker) worker.terminate();
      worker = null;
      const err = error instanceof Error ? error : new Error(String(error));
      if (rejectReady) rejectReady(err);
      for (const call of pending.values()) call.reject(err);
      pending.clear();
      // Error text is untrusted; never insert it as HTML.
      msg.textContent = "Track engine unavailable: " + err.message.slice(0, 300);
      if (!overlay.isConnected) document.body.append(overlay);
      if (!overlay.querySelector("button")) {
        const retry = document.createElement("button");
        retry.textContent = "Reload and recover autosave";
        retry.addEventListener("click", () => location.reload());
        overlay.append(retry);
      }
    };
    try {
      const booted = new Promise((resolve, reject) => {
        rejectReady = reject;
        worker = new Worker("./worker.js?v=__BUILD__");
        worker.onerror = (event) => {
          event.preventDefault();
          fail(new Error(event.message || "worker error"));
        };
        worker.onmessageerror = () => fail(new Error("invalid worker message"));
        worker.addEventListener("message", ({data}) => {
          if (data && data.bootError) { fail(new Error(data.bootError)); return; }
          if (data && data.ready) {
            ready = true;
            clearTimeout(timer);
            resolve();
            return;
          }
          if (typeof data === "number") {
            if (pending.size) status(`searching… ${data.toLocaleString()} states explored`);
            return;
          }
          const {id, res, err} = data || {};
          const call = pending.get(id);
          if (!call) return;
          pending.delete(id);
          if (err) call.reject(new Error(err));
          else call.resolve(res);
        });
        timer = setTimeout(() => fail(new Error("engine loading timed out")), 60000);
      });
      await booted;
      rejectReady = null;
      await refresh();
      overlay.remove();
      readyStatus("Engine ready — runs in your browser · build __BUILD__");
    } catch (error) { fail(error); }
  };
})();
