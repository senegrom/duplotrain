/* duplotrain engine worker: Pyodide + the Python package, off the UI thread.
 * Messages in:  {id, path, body}  (body: JSON string or null)
 * Messages out: {ready: true} once booted, then {id, res} / {id, err} per call. */
"use strict";

/* __PYODIDE_DIR__ and __ENGINE_ZIP__ are stamped by webapp/build.py: versioned
 * URLs so browsers can cache the big runtime forever yet always pick up a new
 * engine (the old flat names were served immutable and pinned stale engines). */
importScripts("__PYODIDE_DIR__/pyodide.js");

let dispatch = null;

const booted = (async () => {
  const pyodide = await loadPyodide({ indexURL: "__PYODIDE_DIR__/" });
  const zipBuf = await (await fetch("__ENGINE_ZIP__")).arrayBuffer();
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
