/* Isolated Pyodide engine; all versioned paths are stamped by build.py. */
"use strict";

let dispatch = null;
// The page shows these texts: an error's message, not its "Error: " name.
const errorText = error => error?.message || String(error);
// Every chunk the runtime and engine downloads bring, at most once a second, tells
// the page that loading still makes progress.
let reported = 0;
const rawFetch = globalThis.fetch.bind(globalThis);
// A lost or refused download names its file. While the engine starts, the page hears
// of it at once: Pyodide only logs a failed runtime download and would wait forever.
let bootFailed = false;
function downloadFailed(url, error) {
  const failure = new Error(`Could not load ${url}: ${errorText(error)}`);
  if (!dispatch && !bootFailed) {
    bootFailed = true;
    postMessage({bootError: failure.message});
  }
  return failure;
}
// A strict worker must assign through globalThis: Chromium refuses a bare "fetch =".
globalThis.fetch = async (...args) => {
  const url = args[0]?.url ?? String(args[0]);
  let response;
  try { response = await rawFetch(...args); } catch (error) { throw downloadFailed(url, error); }
  if (!response.ok) downloadFailed(url, `HTTP ${response.status}`);
  if (!response.body) return response;
  const reader = response.body.getReader();
  const body = new ReadableStream({
    async pull(controller) {
      let chunk;
      try { chunk = await reader.read(); } catch (error) { throw downloadFailed(url, error); }
      if (chunk.done) { controller.close(); return; }
      if (Date.now() - reported >= 1000) { reported = Date.now(); postMessage({loading: true}); }
      controller.enqueue(chunk.value);
    },
    cancel(reason) { return reader.cancel(reason); },
  });
  return new Response(body, {status: response.status, statusText: response.statusText, headers: response.headers});
};
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
booted.catch(error => { if (!bootFailed) postMessage({bootError: errorText(error)}); });
onmessage = async ({data: {id, path, body}}) => {
  try {
    await booted;
    postMessage({id, res: dispatch(path, body)});
  } catch (error) {
    // After a fatal error Pyodide "can no longer be used": the page must restart
    // the engine rather than keep sending requests to this runtime.
    postMessage(error?.pyodide_fatal_error ? {id, fatal: errorText(error)} : {id, err: errorText(error)});
  }
};
