/* duplotrain engine worker: Pyodide + the Python package, off the UI thread.
 * Messages in:  {id, path, body}  (body: JSON string or null)
 * Messages out: {ready: true} once booted, then {id, res} / {id, err} per call. */
"use strict";

importScripts("./pyodide/pyodide.js");

let dispatch = null;

const booted = (async () => {
  const pyodide = await loadPyodide({ indexURL: "./pyodide/" });
  const zipBuf = await (await fetch("./duplotrain-src.zip")).arrayBuffer();
  pyodide.FS.mkdirTree("/app");
  pyodide.unpackArchive(zipBuf, "zip", { extractDir: "/app" });
  pyodide.runPython("import sys; sys.path.insert(0, '/app')");
  const adapterSrc = await (await fetch("./adapter.py")).text();
  pyodide.FS.writeFile("/app/adapter.py", adapterSrc);
  dispatch = pyodide.pyimport("adapter").dispatch;
  postMessage({ ready: true });
})();

booted.catch((err) => postMessage({ bootError: String(err) }));

onmessage = async (event) => {
  const { id, path, body } = event.data;
  try {
    await booted;
    postMessage({ id, res: dispatch(path, body) });
  } catch (err) {
    postMessage({ id, err: String(err) });
  }
};
