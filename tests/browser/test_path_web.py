"""New job, viewport and offline workflows against real browser engines."""
import hashlib
import json
import mimetypes
import os
import re
import socket
import tempfile
import threading
from contextlib import contextmanager, nullcontext
from http.server import BaseHTTPRequestHandler, SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.layout import build_chain, layout_to_dict
from tests.browser import test_editor as editor_tests
from tests.browser.conftest import required_browser
from tests.browser.tls import localhost_tls, runner_test_ca

editor = editor_tests.editor
load = editor_tests.load

pytestmark = pytest.mark.browser


def exercise_interactive_features(page):
    """Run identically under local HTTP and the production-CSP Pyodide host."""
    from playwright.sync_api import expect

    fixtures = Path(__file__).parents[1] / "fixtures"
    page.locator("#unlimited").check()
    expect(page.locator('[data-piece-id="curve"] .count')).to_have_text("∞")
    page.locator("#reversing").uncheck()
    page.locator("#reversing").dispatch_event("change")
    page.locator("#slop").fill("0")
    page.locator("#max-pieces").fill("26")
    page.locator("#importfile").set_input_files(str(fixtures / "bridge-gap.json"))
    expect(page.locator("#status")).to_contain_text("imported 59 pieces.")
    expect(page.locator("#end-select option")).to_have_count(2)
    original = page.evaluate("S.snapshot.layout")
    page.locator("#solve").click()
    expect(page.locator("#status")).to_contain_text("8 alternative(s) found", timeout=90000)
    assert page.evaluate("interactiveJob.searched") == 1878
    page.locator("#find-more").click()
    expect(page.locator("#status")).to_contain_text("16 alternative(s) found", timeout=90000)
    assert page.evaluate("interactiveJob.searched") == 1961
    expect(page.locator(".cand")).to_have_count(8)
    page.locator("#candidate-next").click()
    expect(page.locator("#candidate-page")).to_have_text("Page 2 / 2")
    assert page.locator(".cand").first.get_attribute("data-candidate-index") == "8"
    first = page.locator(".cand").first
    first.get_by_role("button", name="Preview", exact=True).click()
    expect(first.get_by_role("button", name="Apply")).to_be_enabled()
    first.get_by_role("button", name="Apply").click()
    expect(page.locator("#status")).to_contain_text("83 pieces")
    assert page.evaluate("S.snapshot.layout.placements.slice(0,59)") == original["placements"]
    page.locator("#undo").click()
    expect(page.locator("#status")).to_contain_text("59 pieces")
    assert page.evaluate("S.snapshot.layout") == original

    # The multi-gap plan is published whole and undone in one step.
    c = default_catalog()
    ring = build_chain([(c["curve"], 0, 1)] * 12).join((0, 0), (11, 1))
    from duplotrain.editor import Session

    s = Session(history=[ring], inventory={"curve": 12})
    s.remove_piece(7)
    s.remove_piece(2)
    gap = layout_to_dict(s.layout)
    page.locator("#importfile").set_input_files({
        "name": "two-gap.json", "mimeType": "application/json",
        "buffer": json.dumps(gap).encode(),
    })
    expect(page.locator("#status")).to_contain_text("imported 10 pieces.")
    expect(page.locator("#end-select option")).to_have_count(4)
    page.locator("#max-pieces").fill("2")
    # Close all gaps plans exact, non-reversing joins, whatever Close the loop's
    # slop and reversing settings are.
    page.locator("#reversing").check()
    page.locator("#slop").fill("5")
    page.locator("#close-all").click()
    expect(page.locator("#status")).to_contain_text("alternative(s) found", timeout=90000)
    first = page.locator(".cand").first
    first.get_by_role("button", name="Preview", exact=True).click()
    first.get_by_role("button", name="Apply").click()
    expect(page.locator("#status")).to_contain_text("12 pieces")
    assert page.evaluate("S.open_ends.length") == 0
    page.locator("#undo").click()
    expect(page.locator("#status")).to_contain_text("4 open end(s)")
    assert page.evaluate("S.snapshot.layout") == gap

    # The actual bridge's best witness fills the existing start/switch selectors.
    page.locator("#importfile").set_input_files(str(fixtures / "bridge-completed.json"))
    expect(page.locator("#status")).to_contain_text("83 pieces")
    for label in ("Test train", "Find and analyse train routes"):
        summary = page.locator("summary", has_text=re.compile("^" + re.escape(label) + "$"))
        if summary.locator("..").get_attribute("open") is None:
            summary.click()
    page.locator("#train-start").select_option("[0,0]")
    page.locator("#route-best").click()
    expect(page.locator("#route-report")).to_contain_text("64 / 64 runs", timeout=90000)
    expect(page.locator("#route-report")).to_contain_text("57 / 83 pieces ever visited")
    expect(page.locator("#route-report")).to_contain_text("26 visited in the repeating cycle")
    page.locator("#route-witness").click()
    expect(page.locator("#train-report")).to_contain_text("57 / 83 drivable pieces visited")


def exercise_cached_canvas(page):
    """Compare cached/direct pixels and restore temporary view/state afterwards."""
    result = page.evaluate("""() => {
      const saved = view, placements = S.layout.placements;
      const points = [[10,10], [canvas.clientWidth/2,canvas.clientHeight/2],
        [canvas.clientWidth-10,canvas.clientHeight-10]];
      const pixels = () => points.map(([x,y]) => {
        const d = window.devicePixelRatio || 1;
        return Array.from(ctx.getImageData(Math.floor(x*d),Math.floor(y*d),1,1).data);
      });
      try {
        ctx.clearRect(0,0,canvas.width,canvas.height); drawLayout({placements},false);
        const direct=pixels();
        ctx.clearRect(0,0,canvas.width,canvas.height); drawBaseTrack({placements});
        const cached=pixels();
        const first=baseRaster;
        drawBaseTrack({placements}); const reused=first===baseRaster;
        view={...view,x:view.x+64};drawBaseTrack({placements});
        return {direct,cached,reused,invalidated:first!==baseRaster};
      } finally {view=saved;draw();}
    }""")
    assert result["direct"] == result["cached"]
    assert result["reused"] and result["invalidated"]


def _built_app(browser_type):
    """The built web app and its production CSP, or a skip where it cannot run."""
    if not os.environ.get("DUPLOTRAIN_STATIC_DIST"):
        # A lost variable must not turn the built-app tests green on CI.
        (pytest.fail if required_browser() else pytest.skip)(
            "set DUPLOTRAIN_STATIC_DIST to a built webapp/dist directory")
    if browser_type.name == "webkit" and os.environ.get("DUPLOTRAIN_TEST_SYSTEM_CA") != "1":
        pytest.skip("WebKit offline tests need the opted-in disposable CI runner "
                    "(DUPLOTRAIN_TEST_SYSTEM_CA=1, see tests/browser/tls.py)")
    dist = Path(os.environ["DUPLOTRAIN_STATIC_DIST"])
    policy = re.search(r'Content-Security-Policy "([^"\n]+)"',
                       (dist / ".htaccess").read_text()).group(1)
    return dist, policy


@contextmanager
def _offline_profile(browser_type, root, handler):
    """Serve *handler* on localhost and open a fresh browser profile on it.

    WebKit upgrades localhost HTTP subresources under the production CSP. Use
    HTTPS and an ephemeral CA installed only in the explicitly opted-in disposable
    CI runner. Certificate errors and hostname validation remain enabled. The CA
    is removed after the fresh browser closes, including on failure. Chromium
    retains its working potentially trustworthy HTTP-loopback profile. Yields the
    context, the site's URL and a function that stops the server for good.
    """
    options = {"headless": True, "viewport": {"width": 390, "height": 844},
               "has_touch": True}
    if os.environ.get("DUPLOTRAIN_BROWSER_PATH"):
        options["executable_path"] = os.environ["DUPLOTRAIN_BROWSER_PATH"]
    trust, scheme, tls = nullcontext(), "http", None
    if browser_type.name == "webkit":
        tls, ca = localhost_tls(root)
        trust, scheme = runner_test_ca(ca), "https"
    server = ThreadingHTTPServer(("127.0.0.1", 0), handler)
    try:
        if tls is not None:
            server.socket = tls.wrap_socket(server.socket, server_side=True)
    except BaseException:
        server.server_close()
        raise
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
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
            context = browser_type.launch_persistent_context(str(root / "profile"), **options)
            try:
                yield context, f"{scheme}://localhost:{server.server_port}/", stop_server
            finally:
                context.close()
    finally:
        stop_server()


def exercise_offline_reload(browser_type, confirmed):
    """Boot the unchanged offline build with genuine transport/certificate trust."""
    from playwright.sync_api import expect

    dist, policy = _built_app(browser_type)

    class Handler(SimpleHTTPRequestHandler):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, directory=str(dist), **kwargs)

        def end_headers(self):
            self.send_header("Content-Security-Policy", policy)
            super().end_headers()

    errors, failed_requests = [], []
    with tempfile.TemporaryDirectory(prefix="duplotrain-offline-test-") as directory:
        try:
            with _offline_profile(browser_type, Path(directory), Handler) as (
                    context, url, stop_server):
                offline_page = context.pages[0] if context.pages else context.new_page()
                offline_page.on("pageerror", lambda error: errors.append(str(error)))
                offline_page.on("requestfailed", lambda request: failed_requests.append(
                    f"{request.url}: {request.failure}"))
                offline_page.goto(url)
                assert offline_page.evaluate("window.isSecureContext")
                expect(offline_page.locator("#status")).to_contain_text(
                    "Engine ready", timeout=90000,
                )
                offline_page.locator("#projectfile").set_input_files({
                    "name": "confirmed-session.json", "mimeType": "application/json",
                    "buffer": json.dumps(confirmed).encode(),
                })
                expect(offline_page.locator("#status")).to_contain_text("Opened project:")
                assert offline_page.evaluate("S.snapshot") == confirmed
                _exercise_offline_reload(offline_page, stop_server)
                assert offline_page.evaluate("S.snapshot") == confirmed
                assert not errors
        except Exception:
            print("Offline page errors:", errors)
            print("Offline failed requests:", failed_requests)
            raise


def _exercise_offline_reload(page, stop_server):
    """Reload the real worker after its resource server has physically stopped."""
    from playwright.sync_api import expect

    _open_offline_panel(page)
    page.locator("#offline-install").click()
    # Fail promptly with the UI's actual reason rather than waiting three minutes
    # after a rejected registration or integrity check.
    expect(page.locator("#offline-status")).to_contain_text(
        re.compile(r"Offline ready|Portable project downloads remain available"), timeout=180000,
    )
    expect(page.locator("#offline-status")).to_contain_text("Offline ready")
    # Inspect native lifecycle state before removing the network. A ready cache
    # and an activated controller are distinct prerequisites for navigation.
    lifecycle = page.evaluate("""async () => {
      const r = await navigator.serviceWorker.getRegistration();
      return {controller: navigator.serviceWorker.controller?.state || null,
        active: r?.active?.state || null, waiting: r?.waiting?.state || null,
        installing: r?.installing?.state || null, caches: await caches.keys()};
    }""")
    assert lifecycle["controller"] == lifecycle["active"] == "activated", lifecycle
    page.evaluate("saveSession()")
    before = page.evaluate("S.snapshot")
    stop_server()  # a cache miss cannot succeed even if offline emulation is imperfect
    # Prove real origin loss outside the browser. A deliberately failing fetch
    # through respondWith emits WebKit pageerror events even when fetch is caught;
    # keep the strict no-pageerrors assertion instead of hiding those events.
    origin = urlsplit(page.url)
    assert origin.hostname == "localhost" and origin.port is not None
    with pytest.raises(ConnectionRefusedError):
        with socket.create_connection(("127.0.0.1", origin.port), timeout=5):
            pass
    cached = page.evaluate("""async () => {
      const index = await fetch("./index.html", {cache: "no-store"});
      return index.ok && (await index.text()).includes("duplotrain");
    }""")
    assert cached
    emulate_offline = page.context.browser.browser_type.name != "webkit"
    try:
        # WebKit's emulated-offline protocol aborts this service-worker navigation.
        # Real origin loss is verified above; Chromium also uses the emulation flag.
        if emulate_offline:
            page.context.set_offline(True)
        page.reload()
        expect(page.locator("#status")).to_contain_text("Engine ready", timeout=90000)
        assert page.evaluate("S.snapshot") == before
        page.get_by_text("Version and offline access", exact=True).click()
        expect(page.locator("#offline-status")).to_contain_text("Offline ready", timeout=30000)
    finally:
        if emulate_offline:
            page.context.set_offline(False)


def _open_offline_panel(page):
    summary = page.locator("summary", has_text="Version and offline access")
    if summary.locator("..").get_attribute("open") is None:
        summary.click()


def test_built_app_reloads_offline(browser):
    from duplotrain.editor import Session

    session = Session()
    session.attach("straight", 0, None)
    exercise_offline_reload(browser.browser_type, session.snapshot())


def _builds(dist, count):
    """The built app under *count* build stamps: real, content-stamped versions.

    Per version, what the server answers for each path (the bytes and their type),
    and the offline version names.
    """
    source = (dist / "service-worker.js").read_text()
    original = re.search(r'const BUILD = "([a-f0-9]+)";', source).group(1)
    assets = json.loads(re.search(r"const ASSETS = (\[.*\]);", source).group(1))
    template = (Path(__file__).parents[2] / "webapp/service-worker.js").read_text()
    versions, names = [], []
    for build in (f"ab{n:06d}" for n in range(1, count + 1)):
        served, manifest = {}, []
        for asset in assets:
            path = asset["url"].split("?", 1)[0]
            data = (dist / path).read_bytes()
            # Only application text carries the stamp; runtime and archive bytes stay.
            if "/" not in path and Path(path).suffix in {".js", ".html", ".css", ".py",
                                                         ".webmanifest"}:
                data = data.replace(original.encode(), build.encode())
            url = asset["url"].replace(original, build)
            served["/" + url] = (data, mimetypes.guess_type(path)[0] or "application/octet-stream")
            manifest.append({"url": url, "bytes": len(data),
                             "sha256": hashlib.sha256(data).hexdigest()})
        version = hashlib.sha256(json.dumps(manifest).encode()).hexdigest()[:16]
        worker = (template.replace("__BUILD__", build).replace("__VERSION__", version)
                  .replace("__ASSETS__", json.dumps(manifest)))
        served["/service-worker.js"] = (worker.encode(), "text/javascript")
        served["/"] = served["/index.html"]
        versions.append(served)
        names.append(version)
    return versions, names


def test_a_tab_left_open_across_three_updates_restarts_its_engine_offline(browser, tmp_path):
    from playwright.sync_api import expect

    dist, policy = _built_app(browser.browser_type)
    (versions, names), current = _builds(dist, 4), [0]

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            entry = versions[current[0]].get(self.path)
            if entry is None:
                self.send_error(404)
                return
            data, kind = entry  # the headers come from this server's own table
            self.send_response(200)
            self.send_header("Content-Type", kind)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Content-Security-Policy", policy)
            # No HTTP cache may stand in for a deleted offline version.
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(data)

        def log_message(self, *args):
            pass

    errors = []
    with _offline_profile(browser.browser_type, tmp_path, Handler) as (context, url, stop_server):
        # Keep hold of each page's engine worker, to fail it on demand.
        context.add_init_script("""
          const NativeWorker = window.Worker;
          window.Worker = class extends NativeWorker {
            constructor(...args) { super(...args); window.__testWorker = this; }
          };""")
        old_tab = context.pages[0] if context.pages else context.new_page()
        old_tab.on("pageerror", lambda error: errors.append(str(error)))
        old_tab.goto(url)
        expect(old_tab.locator("#status")).to_contain_text("Engine ready", timeout=90000)
        old_tab.locator('[data-piece-id="straight"]').get_by_role("button", name="ahead").tap()
        bounds = old_tab.locator("#canvas").bounding_box()
        old_tab.touchscreen.tap(bounds["x"] + bounds["width"] / 2,
                                bounds["y"] + bounds["height"] / 2)
        expect(old_tab.locator("#undo")).to_be_enabled()
        confirmed = old_tab.evaluate("S.snapshot")
        _open_offline_panel(old_tab)
        old_tab.locator("#offline-install").click()
        expect(old_tab.locator("#offline-status")).to_contain_text("Offline ready",
                                                                  timeout=180000)
        old_tab.evaluate("""async () => {
          await navigator.serviceWorker.ready;
          if (!navigator.serviceWorker.controller) await new Promise(resolve =>
            navigator.serviceWorker.addEventListener("controllerchange", resolve, {once: true}));
        }""")
        # Another tab installs and applies three updates, as a user would.
        new_tab = context.new_page()
        new_tab.on("pageerror", lambda error: errors.append(str(error)))
        new_tab.on("dialog", lambda dialog: dialog.accept())
        new_tab.goto(url)
        for index, build in ((1, "ab000002"), (2, "ab000003"), (3, "ab000004")):
            current[0] = index
            expect(new_tab.locator("#status")).to_contain_text("Engine ready", timeout=90000)
            _open_offline_panel(new_tab)
            new_tab.locator("#offline-check").click()
            expect(new_tab.locator("#offline-update")).to_be_visible(timeout=180000)
            with new_tab.expect_navigation(timeout=90000):
                new_tab.locator("#offline-update").click()
            expect(new_tab.locator("#status")).to_contain_text("Engine ready", timeout=90000)
            assert new_tab.evaluate("window.duplotrainBuild") == build
            assert old_tab.evaluate("window.duplotrainBuild") == "ab000001"
            assert old_tab.evaluate("S.snapshot") == confirmed
        # Both tabs answered the last activation's handshake: it kept the version
        # active before it (ab000003) and the old tab's (ab000001), and deleted
        # ab000002.
        kept = new_tab.evaluate("caches.keys()")
        assert [any(name.endswith(":" + version) for name in kept) for version in names] == [
            True, False, True, True]
        # With the network gone, the old tab still has its own version's files.
        stop_server()
        with pytest.raises(OSError):
            socket.create_connection(("127.0.0.1", urlsplit(url).port), timeout=1)
        if browser.browser_type.name == "chromium":
            context.set_offline(True)
        assert old_tab.evaluate("""async () => {
          const r = await fetch("./worker.js?v=ab000001", {cache: "no-store"});
          return r.ok && (await r.text()).includes("ab000001");
        }""")
        old_tab.evaluate("""() => window.__testWorker.dispatchEvent(new ErrorEvent("error", {
          message: "test old engine failure", cancelable: true}))""")
        old_tab.get_by_role(
            "button", name="Restart engine and restore last confirmed session", exact=True,
        ).tap()
        expect(old_tab.locator("#status")).to_contain_text("Engine restarted", timeout=90000)
        assert old_tab.evaluate("S.snapshot") == confirmed
        assert old_tab.evaluate("window.duplotrainBuild") == "ab000001"
        assert not errors


def test_interactive_search_more_multi_gap_and_route_witness(editor):
    page, _session, url, errors = editor
    load(page, url)
    exercise_interactive_features(page)
    exercise_cached_canvas(page)
    assert not errors
