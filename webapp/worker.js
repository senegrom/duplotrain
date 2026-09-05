/* Isolated Pyodide engine; all versioned paths are stamped by build.py. */
"use strict";

let dispatch = null;
async function checkedFetch(url) {
  const response = await fetch(url);
  if (!response.ok) throw new Error(`Could not load ${url}: HTTP ${response.status}`);
  return response;
}
const booted = (async () => {
  importScripts("__PYODIDE_DIR__/pyodide.js");
  const pyodide = await loadPyodide({indexURL: "__PYODIDE_DIR__/"});
  const zipBuf = await (await checkedFetch("__ENGINE_ZIP__")).arrayBuffer();
  pyodide.FS.mkdirTree("/app");
  pyodide.unpackArchive(zipBuf, "zip", {extractDir: "/app"});
  pyodide.runPython("import sys; sys.path.insert(0, '/app')");
  const adapterSrc = await (await checkedFetch("__ADAPTER__")).text();
  pyodide.FS.writeFile("/app/adapter.py", adapterSrc);
  dispatch = pyodide.pyimport("adapter").dispatch;
  postMessage({ready: true});
})();
booted.catch(error => postMessage({bootError: String(error)}));
onmessage = async ({data: {id, path, body}}) => {
  try {
    await booted;
    postMessage({id, res: dispatch(path, body)});
  } catch (error) { postMessage({id, err: String(error)}); }
};
