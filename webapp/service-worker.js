/* Opt-in, complete-version offline installation. Stamped by build.py. */
"use strict";
const BUILD = "__BUILD__";
const ASSETS = __ASSETS__;
const SCOPE = self.registration.scope;
const PREFIX = "duplotrain-offline/1:" + encodeURIComponent(SCOPE) + ":";
const CACHE = PREFIX + BUILD;
const MARKER = new URL(".offline-complete-" + BUILD, SCOPE).href;
const INDEX = new URL("index.html", SCOPE).href;
let installing = null;
const absolute = path => new URL(path, SCOPE).href;
const hex = bytes => [...new Uint8Array(bytes)].map(v => v.toString(16).padStart(2, "0")).join("");

async function offlineStatus() {
  if (!(await caches.keys()).includes(CACHE)) return {build: BUILD, ready: false};
  const cache = await caches.open(CACHE);
  if (!(await cache.match(MARKER))) return {build: BUILD, ready: false};
  for (const asset of ASSETS) if (!(await cache.match(absolute(asset.url)))) return {build: BUILD, ready: false};
  return {build: BUILD, ready: true, assets: ASSETS.length};
}
async function installVersion() {
  if (installing) return installing;
  installing = (async () => {
    if ((await offlineStatus()).ready) return offlineStatus();
    const cache = await caches.open(CACHE);
    // A missing marker makes a partial version unusable for offline navigation.
    await cache.delete(MARKER);
    try {
      for (const asset of ASSETS) {
        const url = absolute(asset.url);
        if (new URL(url).origin !== new URL(SCOPE).origin || !url.startsWith(SCOPE))
          throw new Error("Offline asset outside application scope");
        const controller = new AbortController();
        const timeout = setTimeout(() => controller.abort(), 60000);
        let response, data;
        try {
          response = await fetch(url, {cache: "no-store", credentials: "same-origin", redirect: "error", signal: controller.signal});
          if (!response.ok || response.type === "opaque") throw new Error(`Offline download failed: ${asset.url}`);
          data = await response.arrayBuffer();
        } finally { clearTimeout(timeout); }
        if (data.byteLength !== asset.bytes || hex(await crypto.subtle.digest("SHA-256", data)) !== asset.sha256)
          throw new Error(`Offline version verification failed: ${asset.url}`);
        // Reconstruct with original headers, preserving MIME and CSP. Avoid a
        // stale Content-Encoding/Length after fetch has decoded the response.
        const headers = new Headers(response.headers);
        headers.delete("Content-Encoding"); headers.set("Content-Length", String(data.byteLength));
        await cache.put(url, new Response(data, {status: 200, headers}));
      }
      // The marker also records when this version completed, for pruning.
      await cache.put(MARKER, new Response(BUILD, {headers: {"Content-Type": "text/plain",
        "X-Installed": String(Date.now())}}));
      return offlineStatus();
    } catch (error) {
      // Delete ONLY this incomplete version. Previously verified versions and
      // other applications' caches/projects are never touched.
      await caches.delete(CACHE);
      throw error;
    }
  })();
  try { return await installing; } finally { installing = null; }
}
// Keep this version and the newest older complete one, which tabs opened before
// the update still run; older versions only take space. A cache without its
// marker may be a newer version still installing, so it is left alone.
async function pruneOlderVersions() {
  const complete = [];
  for (const name of await caches.keys()) {
    if (!name.startsWith(PREFIX) || name === CACHE) continue;
    const marker = await (await caches.open(name)).match(absolute(".offline-complete-" + name.slice(PREFIX.length)));
    if (marker) complete.push({name, installed: Number(marker.headers.get("X-Installed")) || 0});
  }
  complete.sort((a, b) => b.installed - a.installed);
  for (const {name} of complete.slice(1)) await caches.delete(name);
}
self.addEventListener("install", event => event.waitUntil(installVersion()));
self.addEventListener("activate", event => event.waitUntil(
  pruneOlderVersions().then(() => self.clients.claim())));
// Do not skipWaiting automatically: changing versions must not reload or
// replace an unsaved editor. Already-open clients keep their exact asset URLs.
self.addEventListener("message", event => {
  const reply = event.ports?.[0];
  if (!reply || !["STATUS", "INSTALL", "ACTIVATE"].includes(event.data?.type)) return;
  event.waitUntil((async () => {
    try {
      if (event.data.type === "ACTIVATE") {
        if (!(await offlineStatus()).ready) throw new Error("New offline version is incomplete");
        await self.skipWaiting(); reply.postMessage({build: BUILD, activated: true});
      } else reply.postMessage(event.data.type === "INSTALL" ? await installVersion() : await offlineStatus());
    } catch (error) { reply.postMessage({error: String(error), build: BUILD, ready: false}); }
  })());
});
async function serve(request) {
  const cache = await caches.open(CACHE);
  if (request.mode === "navigate") {
    const pathname = new URL(request.url).pathname;
    if (pathname !== new URL(SCOPE).pathname && pathname !== new URL(INDEX).pathname) return fetch(request);
    // The verified index and its content-stamped resources form one unit.
    if ((await offlineStatus()).ready) return cache.match(INDEX);
    return fetch(request);
  }
  const own = await cache.match(request);
  if (own && await cache.match(MARKER)) return own;
  // Keep exact old URLs available during an explicit update in another tab.
  // Never ignore query strings or use another application's cache.
  for (const name of await caches.keys()) if (name.startsWith(PREFIX) && name !== CACHE) {
    const older = await caches.open(name);
    const marker = absolute(".offline-complete-" + name.slice(PREFIX.length));
    if (!(await older.match(marker))) continue;
    const hit = await older.match(request);
    if (hit) return hit;
  }
  return fetch(request);  // no runtime caching of arbitrary data or API responses
}
self.addEventListener("fetch", event => {
  const request = event.request, url = new URL(request.url);
  if (request.method !== "GET" || url.origin !== new URL(SCOPE).origin ||
      !url.href.startsWith(SCOPE) || url.pathname.includes("/api/") ||
      url.pathname.endsWith("/service-worker.js")) return;
  event.respondWith(serve(request));
});
