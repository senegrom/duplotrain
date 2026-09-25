"""A live editor survives two offline updates, then restarts its real engine."""

import hashlib
import json
import mimetypes
import os
import re
import socket
import threading
from contextlib import nullcontext
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import pytest

from tests.browser.tls import localhost_tls, runner_test_ca

pytestmark = pytest.mark.browser
ROOT = Path(__file__).resolve().parents[2]


def _versions(dist):
    """Use the same built engine, with three real content-stamped resource sets."""
    source = (dist / "service-worker.js").read_text()
    original = re.search(r'const BUILD = "([a-f0-9]+)";', source).group(1)
    assets = json.loads(re.search(r"const ASSETS = (\[.*\]);", source).group(1))
    template = (ROOT / "webapp/service-worker.js").read_text()
    versions = []
    for build in ("ab000001", "ab000002", "ab000003"):
        resources, manifest = {}, []
        for asset in assets:
            path = asset["url"].split("?", 1)[0]
            data = (dist / path).read_bytes()
            # Only application text contains the build stamp. Runtime and ZIP
            # bytes stay untouched; each manifest verifies the exact served bytes.
            if ("/" not in path
                    and Path(path).suffix in {".js", ".html", ".css", ".py", ".webmanifest"}):
                data = data.replace(original.encode(), build.encode())
            url = asset["url"].replace(original, build)
            resources["/" + url] = data
            manifest.append({"url": url, "bytes": len(data),
                             "sha256": hashlib.sha256(data).hexdigest()})
        version = hashlib.sha256(json.dumps(manifest).encode()).hexdigest()[:16]
        resources["/service-worker.js"] = (template.replace("__BUILD__", build)
            .replace("__VERSION__", version)
            .replace("__ASSETS__", json.dumps(manifest))).encode()
        resources["/"] = resources["/index.html"]
        versions.append(resources)
    return versions


_UPDATE = """async () => {
  const reg = await navigator.serviceWorker.getRegistration();
  if (!reg) throw new Error('offline worker not registered');
  await reg.update();
  const worker = reg.installing || reg.waiting;
  if (!worker) throw new Error('new version did not install');
  const state = wanted => new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      cleanup(); reject(new Error('worker did not become ' + wanted));
    }, 90000);
    const cleanup = () => {
      clearTimeout(timer); worker.removeEventListener('statechange', check);
    };
    const check = () => {
      if (worker.state === wanted) { cleanup(); resolve(); }
      else if (worker.state === 'redundant') {
        cleanup(); reject(new Error('worker became redundant'));
      }
    };
    worker.addEventListener('statechange', check); check();
  });
  if (worker.state !== 'installed') await state('installed');
  const activated = state('activated');
  await new Promise((resolve, reject) => {
    const channel = new MessageChannel();
    const timer = setTimeout(() => {
      cleanup(); reject(new Error('activation reply timed out'));
    }, 90000);
    const cleanup = () => { clearTimeout(timer); channel.port1.close(); channel.port2.close(); };
    channel.port1.onmessage = event => {
      cleanup();
      if (event.data?.activated) resolve();
      else reject(new Error(event.data?.error || 'activation refused'));
    };
    worker.postMessage({type: 'ACTIVATE'}, [channel.port2]);
  });
  await activated;
}"""


def test_old_tab_restarts_real_engine_after_two_offline_updates(browser, tmp_path):
    from playwright.sync_api import expect

    directory = os.environ.get("DUPLOTRAIN_STATIC_DIST")
    if not directory:
        pytest.skip("set DUPLOTRAIN_STATIC_DIST to a built webapp/dist directory")
    dist = Path(directory)
    policy = re.search(r'Content-Security-Policy "([^"\n]+)"',
                       (dist / ".htaccess").read_text()).group(1)
    versions = _versions(dist)
    selected = [0]
    errors = []

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            data = versions[selected[0]].get(self.path)
            if data is None:
                self.send_error(404)
                return
            path = self.path.split("?", 1)[0]
            content_type = "text/html" if path == "/" else mimetypes.guess_type(path)[0]
            self.send_response(200)
            self.send_header("Content-Type", content_type or "application/octet-stream")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Content-Security-Policy", policy)
            # An HTTP cache cannot conceal deletion of a version's offline cache.
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)

        def log_message(self, *args):
            pass

    browser_type = browser.browser_type
    options = {"headless": True, "viewport": {"width": 390, "height": 844}, "has_touch": True}
    if os.environ.get("DUPLOTRAIN_BROWSER_PATH"):
        options["executable_path"] = os.environ["DUPLOTRAIN_BROWSER_PATH"]
    trust, scheme, tls = nullcontext(), "http", None
    if browser_type.name == "webkit":
        tls, ca = localhost_tls(tmp_path)
        trust, scheme = runner_test_ca(ca), "https"
    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    if tls is not None:
        server.socket = tls.wrap_socket(server.socket, server_side=True)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    port = server.server_port
    stopped = False

    def stop_server():
        nonlocal stopped
        if not stopped:
            server.shutdown()
            thread.join(timeout=3)
            server.server_close()
            stopped = True

    try:
        with trust:
            context = browser_type.launch_persistent_context(str(tmp_path / "profile"), **options)
            try:
                context.add_init_script("""
                  const NativeWorker = window.Worker;
                  window.Worker = class extends NativeWorker {
                    constructor(...args) { super(...args); window.__testWorker = this; }
                  };
                """)
                page = context.pages[0] if context.pages else context.new_page()
                page.on("pageerror", lambda error: errors.append(str(error)))
                url = f"{scheme}://localhost:{port}/"
                page.goto(url)
                expect(page.locator("#status")).to_contain_text("Engine ready", timeout=90000)
                assert page.evaluate("window.duplotrainBuild") == "ab000001"
                page.locator('[data-piece-id="straight"]').get_by_role("button", name="ahead").tap()
                bounds = page.locator("#canvas").bounding_box()
                page.touchscreen.tap(bounds["x"] + bounds["width"] / 2,
                                     bounds["y"] + bounds["height"] / 2)
                expect(page.locator("#undo")).to_be_enabled()
                confirmed = page.evaluate("S.snapshot")
                assert len(confirmed["layout"]["placements"]) == 1
                page.get_by_text("Version and offline access", exact=True).click()
                page.locator("#offline-install").click()
                expect(page.locator("#offline-status")).to_contain_text(
                    "Offline ready", timeout=180000,
                )
                await_control = """async () => {
                  await navigator.serviceWorker.ready;
                  if (!navigator.serviceWorker.controller) await new Promise(resolve =>
                    navigator.serviceWorker.addEventListener(
                      'controllerchange', resolve, {once: true}));
                }"""
                page.evaluate(await_control)
                update_tab = context.new_page()
                update_tab.on("pageerror", lambda error: errors.append(str(error)))
                update_tab.goto(url)
                expect(update_tab.locator("#status")).to_contain_text("Engine ready", timeout=90000)
                for index, build in ((1, "ab000002"), (2, "ab000003")):
                    selected[0] = index
                    update_tab.evaluate(_UPDATE)
                    update_tab.reload()
                    expect(update_tab.locator("#status")).to_contain_text(
                        "Engine ready", timeout=90000,
                    )
                    assert update_tab.evaluate("window.duplotrainBuild") == build
                    assert page.evaluate("window.duplotrainBuild") == "ab000001"
                    assert page.evaluate("S.snapshot") == confirmed
                # With C controlling the origin, A must still have its old worker.
                stop_server()
                with pytest.raises(OSError):
                    socket.create_connection(("127.0.0.1", port), timeout=1)
                if browser_type.name == "chromium":
                    context.set_offline(True)
                assert page.evaluate("""async () => {
                  const r = await fetch('./worker.js?v=ab000001', {cache: 'no-store'});
                  return r.ok && (await r.text()).includes('ab000001');
                }""")
                page.evaluate("""() => window.__testWorker.dispatchEvent(new ErrorEvent('error', {
                  message: 'test old engine failure', cancelable: true
                }))""")
                page.get_by_role(
                    "button", name="Restart engine and restore last confirmed session", exact=True,
                ).tap()
                expect(page.locator("#status")).to_contain_text("Engine restarted", timeout=90000)
                assert page.evaluate("S.snapshot") == confirmed
                assert page.evaluate("window.duplotrainBuild") == "ab000001"
                assert not errors
            finally:
                context.close()
    finally:
        stop_server()
