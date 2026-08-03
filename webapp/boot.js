/* duplotrain web boot: bridge the editor to the Python engine running in a
 * Web Worker (see worker.js), so solving never freezes the page.
 *
 * Installs window.duplotrainApi + window.duplotrainBoot before the editor's own
 * script (app.js) runs; the editor calls duplotrainBoot({refresh, status})
 * instead of its first refresh. */
"use strict";

(function () {
  let worker = null;
  let seq = 0;
  const pending = new Map();

  window.duplotrainApi = (path, body) =>
    new Promise((resolve, reject) => {
      if (!worker) return reject(new Error("engine still loading"));
      const id = ++seq;
      pending.set(id, { resolve, reject });
      worker.postMessage({
        id,
        path,
        body: body === undefined ? null : JSON.stringify(body),
      });
    }).then((res) => {
      const data = JSON.parse(res);
      if (data.__error) throw new Error(data.__error);
      return data;
    });

  window.duplotrainBoot = async ({ refresh, status }) => {
    const overlay = document.createElement("div");
    overlay.style.cssText =
      "position:fixed;inset:0;background:rgba(244,242,238,.94);z-index:50;" +
      "display:flex;flex-direction:column;align-items:center;justify-content:center;" +
      "font:15px/1.6 system-ui;color:#2b2f33;text-align:center;padding:20px";
    overlay.innerHTML =
      "<div style='font-size:34px'>🚂</div>" +
      "<div id='bootmsg'>Loading the track engine…<br>" +
      "<span style='color:#7a828a;font-size:13px'>(~12 MB once; cached for next time)</span></div>";
    document.body.append(overlay);
    const msg = overlay.querySelector("#bootmsg");
    const fail = (detail) => {
      msg.innerHTML = "Could not start the engine: <b>" +
        String(detail).slice(0, 300) + "</b>";
    };

    try {
      worker = new Worker("./worker.js");
      worker.onerror = (e) => fail(e.message || "worker error");
      const ready = new Promise((resolve, reject) => {
        worker.addEventListener("message", function onMsg(event) {
          if (event.data && event.data.ready) {
            worker.removeEventListener("message", onMsg);
            resolve();
          } else if (event.data && event.data.bootError) {
            reject(new Error(event.data.bootError));
          }
        });
      });
      worker.addEventListener("message", (event) => {
        const { id, res, err } = event.data || {};
        const call = pending.get(id);
        if (!call) return;
        pending.delete(id);
        if (err) call.reject(new Error(err));
        else call.resolve(res);
      });

      await ready;
      overlay.remove();
      await refresh();
      status("Engine ready — runs in your browser.");
    } catch (err) {
      fail(err);
      console.error(err);
    }
  };
})();
