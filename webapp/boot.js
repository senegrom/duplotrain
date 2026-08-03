/* duplotrain web boot: run the Python engine in-browser via (self-hosted) Pyodide.
 *
 * Installs window.duplotrainApi + window.duplotrainBoot before the editor's own
 * script runs; the editor calls duplotrainBoot({refresh, status}) instead of its
 * first refresh, and every api() call is answered by the Python dispatcher. */
"use strict";

(function () {
  let dispatch = null; // Python callable once booted

  window.duplotrainApi = async (path, body) => {
    if (!dispatch) throw new Error("engine still loading");
    const res = dispatch(path, body === undefined ? null : JSON.stringify(body));
    const data = JSON.parse(res);
    if (data.__error) throw new Error(data.__error);
    return data;
  };

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

    try {
      msg.firstChild.textContent = "Loading Python runtime…";
      const { loadPyodide } = await import("./pyodide/pyodide.mjs");
      const pyodide = await loadPyodide({ indexURL: "./pyodide/" });

      msg.firstChild.textContent = "Loading duplotrain…";
      const zipBuf = await (await fetch("./duplotrain-src.zip")).arrayBuffer();
      pyodide.FS.mkdirTree("/app");
      pyodide.unpackArchive(zipBuf, "zip", { extractDir: "/app" });
      pyodide.runPython("import sys; sys.path.insert(0, '/app')");

      const adapterSrc = await (await fetch("./adapter.py")).text();
      pyodide.FS.writeFile("/app/adapter.py", adapterSrc);
      dispatch = pyodide.pyimport("adapter").dispatch;

      overlay.remove();
      await refresh();
      status(
        "Engine ready — everything runs in your browser. " +
        "Solving may pause the page for a few seconds."
      );
    } catch (err) {
      msg.innerHTML =
        "Could not start the engine: <b>" + String(err).slice(0, 300) + "</b>";
      console.error(err);
    }
  };
})();
