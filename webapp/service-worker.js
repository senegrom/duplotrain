/* Opt-in, complete-version offline installation. Stamped by build.py. */
"use strict";
const BUILD = "__BUILD__";
// A version is named by a digest of what its manifest serves (the engine zip by
// its entries, whose compression differs between build hosts), so any changed
// content installs as a new version, even one the build stamp does not cover.
const VERSION = "__VERSION__";
const ASSETS = __ASSETS__;
const SCOPE = self.registration.scope;
const PREFIX = "duplotrain-offline/1:" + encodeURIComponent(SCOPE) + ":";
const CACHE = PREFIX + VERSION;
const MARKER = new URL(".offline-complete-" + VERSION, SCOPE).href;
const INDEX = new URL("index.html", SCOPE).href;
// An unfinished installation of another version that has made no progress for
// this long no longer runs: the next activation reclaims its space.
const ABANDONED_MS = 3600000;
let installing = null;
const absolute = path => new URL(path, SCOPE).href;
const progressOf = version => absolute(".offline-progress-" + version);
const hex = bytes => [...new Uint8Array(bytes)].map(v => v.toString(16).padStart(2, "0")).join("");

async function offlineStatus() {
  if (!(await caches.has(CACHE))) return {build: BUILD, ready: false};
  const cache = await caches.open(CACHE);
  if (!(await cache.match(MARKER))) return {build: BUILD, ready: false};
  for (const asset of ASSETS) if (!(await cache.match(absolute(asset.url)))) return {build: BUILD, ready: false};
  return {build: BUILD, ready: true, assets: ASSETS.length};
}
// One verified asset. The download fails once no bytes arrive for a minute,
// however long a slow but steady link needs for the largest runtime file.
async function download(asset) {
  const url = absolute(asset.url);
  if (!url.startsWith(SCOPE)) throw new Error("Offline asset outside application scope");
  const controller = new AbortController();
  let timer;
  const alive = () => { clearTimeout(timer); timer = setTimeout(() => controller.abort(), 60000); };
  alive();
  try {
    const response = await fetch(url, {cache: "no-store", credentials: "same-origin", redirect: "error", signal: controller.signal});
    if (!response.ok || response.type === "opaque") throw new Error(`Offline download failed: ${asset.url}`);
    const data = new Uint8Array(asset.bytes), reader = response.body.getReader();
    let size = 0;
    for (;;) {
      const {done, value} = await reader.read();
      if (done) break;
      alive();
      if (size + value.byteLength > data.byteLength) throw new Error(`Offline version verification failed: ${asset.url}`);
      data.set(value, size); size += value.byteLength;
    }
    if (size !== data.byteLength || hex(await crypto.subtle.digest("SHA-256", data)) !== asset.sha256)
      throw new Error(`Offline version verification failed: ${asset.url}`);
    return {response, data};
  } catch (error) { controller.abort(); throw error; }
  finally { clearTimeout(timer); }
}
// Each attempt keeps the assets it verified, so an installation cut short, by a
// lost connection or the browser's time limit for one event, resumes where it
// stopped. Only verified bytes are ever stored under this version's name.
async function installVersion() {
  if (installing) return installing;
  installing = (async () => {
    const status = await offlineStatus();
    if (status.ready) return status;
    const cache = await caches.open(CACHE);
    try {
      // A missing marker makes a partial version unusable for offline navigation.
      await cache.delete(MARKER);
      const progress = () => cache.put(progressOf(VERSION),
        new Response("", {headers: {"X-Progress": String(Date.now())}}));
      await progress();
      for (const asset of ASSETS) {
        const url = absolute(asset.url);
        if (await cache.match(url)) continue;
        const {response, data} = await download(asset);
        // Reconstruct with original headers, preserving MIME and CSP. Avoid a
        // stale Content-Encoding/Length after fetch has decoded the response.
        const headers = new Headers(response.headers);
        headers.delete("Content-Encoding"); headers.set("Content-Length", String(data.byteLength));
        await cache.put(url, new Response(data, {status: 200, headers}));
        await progress();
      }
      // The marker also records when this version completed, for pruning.
      await cache.put(MARKER, new Response(BUILD, {headers: {"Content-Type": "text/plain",
        "X-Installed": String(Date.now())}}));
      await cache.delete(progressOf(VERSION));
    } catch (error) {
      // Out of space, a version that cannot finish gives its space back. Other
      // verified versions and other applications' caches are never touched.
      if (error?.name === "QuotaExceededError") await caches.delete(CACHE);
      throw error;
    }
    const done = await offlineStatus();
    if (!done.ready) throw new Error("Offline version is incomplete after installation");
    return done;
  })();
  try { return await installing; } finally { installing = null; }
}
// A fresh handshake on each activation survives service-worker restarts. Older
// pages without this protocol, suspended tabs and failed enumeration conservatively
// pin ALL old versions. Cache space must not trump a live editor's recovery path.
async function liveClientBuilds() {
  const scopedClients = async () => (await self.clients.matchAll({
    type: "window", includeUncontrolled: true
  })).filter(client => client.url.startsWith(SCOPE));
  const ask = client => new Promise(resolve => {
    const channel = new MessageChannel();
    let finished = false;
    const finish = build => {
      if (finished) return;
      finished = true; clearTimeout(timer);
      channel.port1.close(); channel.port2.close(); resolve(build);
    };
    const timer = setTimeout(() => finish(null), 1500);
    channel.port1.onmessage = event => {
      const build = event.data?.build;
      finish(event.data?.type === "DUPLOTRAIN_CLIENT_BUILD" &&
        typeof build === "string" && /^[a-f0-9]{1,64}$/.test(build) ? build : null);
    };
    channel.port1.onmessageerror = () => finish(null);
    try { client.postMessage({type: "DUPLOTRAIN_CLIENT_BUILD"}, [channel.port2]); }
    catch (_) { finish(null); }
  });
  try {
    const before = await scopedClients();
    const answers = new Map(await Promise.all(before.map(async client => [client.id, await ask(client)])));
    // A tab which closed meanwhile no longer pins a version. A newly opened tab
    // or an unanswered live client makes pruning unsafe for this activation.
    const after = await scopedClients();
    if (after.some(client => !answers.get(client.id))) return null;
    return new Set(after.map(client => answers.get(client.id)));
  } catch (_) { return null; }
}
// Keep this version, the newest previous active version, and every live tab's
// build. Multiple content versions can share a build stamp: retain all matches.
// Another version's unfinished installation keeps its verified files for its
// next attempt until it has made no progress for ABANDONED_MS.
async function activateVersion() {
  const cache = await caches.open(CACHE), marker = await cache.match(MARKER);
  if (marker) {
    const headers = new Headers(marker.headers);
    headers.set("X-Activated", String(Date.now()));
    await cache.put(MARKER, new Response(await marker.text(), {headers}));
  }
  const complete = [];
  for (const name of await caches.keys()) {
    if (!name.startsWith(PREFIX) || name === CACHE) continue;
    const version = name.slice(PREFIX.length), other = await caches.open(name);
    const older = await other.match(absolute(".offline-complete-" + version));
    if (older) complete.push({name, build: await older.text(), activated: Number(older.headers.get("X-Activated")) || 0,
      installed: Number(older.headers.get("X-Installed")) || 0});
    else {
      const progress = await other.match(progressOf(version));
      if (Date.now() - (Number(progress?.headers.get("X-Progress")) || 0) > ABANDONED_MS) await caches.delete(name);
    }
  }
  complete.sort((a, b) => b.activated - a.activated || b.installed - a.installed);
  const live = await liveClientBuilds();
  if (live === null) return;
  // A reported build without a complete cache is also ambiguous; retain backups.
  const known = new Set([BUILD, ...complete.map(version => version.build)]);
  if ([...live].some(build => !known.has(build))) return;
  for (const {name, build} of complete.slice(1)) {
    if (!live.has(build)) await caches.delete(name);
  }
}
self.addEventListener("install", event => event.waitUntil(installVersion()));
self.addEventListener("activate", event => event.waitUntil(
  activateVersion().then(() => self.clients.claim())));
// Do not skipWaiting automatically: changing versions must not reload or
// replace an unsaved editor. Already-open clients keep their exact asset URLs.
self.addEventListener("message", event => {
  const reply = event.ports?.[0];
  if (!reply || !["STATUS", "INSTALL", "ACTIVATE"].includes(event.data?.type)) return;
  event.waitUntil((async () => {
    // The page waits as long as this worker still works on its request.
    const beat = setInterval(() => reply.postMessage({working: true}), 20000);
    try {
      if (event.data.type === "ACTIVATE") {
        if (!(await offlineStatus()).ready) throw new Error("New offline version is incomplete");
        await self.skipWaiting(); reply.postMessage({build: BUILD, activated: true});
      } else reply.postMessage(event.data.type === "INSTALL" ? await installVersion() : await offlineStatus());
    } catch (error) { reply.postMessage({error: String(error), build: BUILD, ready: false}); }
    finally { clearInterval(beat); }
  })());
});
// Assets are stored under bare URLs; a host's Vary header must not hide them.
const stored = {ignoreVary: true};
async function serve(request) {
  const cache = await caches.open(CACHE);
  if (request.mode === "navigate") {
    const pathname = new URL(request.url).pathname;
    if (pathname !== new URL(SCOPE).pathname && pathname !== new URL(INDEX).pathname) return fetch(request);
    // The verified index and its content-stamped resources form one unit.
    if ((await offlineStatus()).ready) return cache.match(INDEX);
    return fetch(request);
  }
  const own = await cache.match(request, stored);
  if (own && await cache.match(MARKER)) return own;
  // Keep exact old URLs available during an explicit update in another tab.
  // Never ignore query strings or use another application's cache.
  for (const name of await caches.keys()) if (name.startsWith(PREFIX) && name !== CACHE) {
    const older = await caches.open(name);
    const marker = absolute(".offline-complete-" + name.slice(PREFIX.length));
    if (!(await older.match(marker))) continue;
    const hit = await older.match(request, stored);
    if (hit) return hit;
  }
  return fetch(request);  // no runtime caching of arbitrary data or API responses
}
self.addEventListener("fetch", event => {
  const request = event.request, url = new URL(request.url);
  if (request.method !== "GET" || !url.href.startsWith(SCOPE) || url.pathname.includes("/api/") ||
      url.pathname.endsWith("/service-worker.js")) return;
  event.respondWith(serve(request));
});
