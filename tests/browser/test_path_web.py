"""New job, viewport and offline workflows against real browser engines."""
import json
import os
import re
import socket
import tempfile
import threading
from contextlib import nullcontext
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.layout import build_chain, layout_to_dict
from tests.browser import test_editor as editor_tests
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


def exercise_offline_reload(page):
    """Boot the unchanged offline build with genuine transport/certificate trust.

    WebKit upgrades localhost HTTP subresources under the production CSP. Use
    HTTPS and an ephemeral CA installed only in the explicitly opted-in disposable
    CI runner. Certificate errors and hostname validation remain enabled. The CA
    is removed after the fresh browser closes, including on failure. Chromium
    retains its working potentially trustworthy HTTP-loopback profile.
    """
    from playwright.sync_api import expect

    dist = Path(os.environ["DUPLOTRAIN_STATIC_DIST"])
    policy = re.search(r'Content-Security-Policy "([^"\n]+)"',
                       (dist / ".htaccess").read_text()).group(1)
    confirmed = page.evaluate("S.snapshot")
    browser_type = page.context.browser.browser_type

    class Handler(SimpleHTTPRequestHandler):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, directory=str(dist), **kwargs)

        def end_headers(self):
            self.send_header("Content-Security-Policy", policy)
            super().end_headers()

    with tempfile.TemporaryDirectory(prefix="duplotrain-offline-test-") as directory:
        root = Path(directory)
        options = {"headless": True, "viewport": {"width": 390, "height": 844},
                   "has_touch": True}
        scheme = "http"
        tls = None
        trust = nullcontext()
        if browser_type.name == "webkit":
            tls, ca = localhost_tls(root)
            trust = runner_test_ca(ca)
            scheme = "https"
        if os.environ.get("DUPLOTRAIN_BROWSER_PATH"):
            options["executable_path"] = os.environ["DUPLOTRAIN_BROWSER_PATH"]
        server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
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

        context = None
        errors, failed_requests = [], []
        try:
            with trust:
                try:
                    context = browser_type.launch_persistent_context(
                        str(root / "profile"), **options,
                    )
                    offline_page = context.pages[0] if context.pages else context.new_page()
                    offline_page.on("pageerror", lambda error: errors.append(str(error)))
                    offline_page.on("requestfailed", lambda request: failed_requests.append(
                        f"{request.url}: {request.failure}"))
                    offline_page.goto(f"{scheme}://localhost:{server.server_port}/")
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
                finally:
                    if context is not None:
                        context.close()
        except Exception:
            print("Offline page errors:", errors)
            print("Offline failed requests:", failed_requests)
            raise
        finally:
            stop_server()


def _exercise_offline_reload(page, stop_server):
    """Reload the real worker after its resource server has physically stopped."""
    from playwright.sync_api import expect

    summary = page.locator("summary", has_text="Version and offline access")
    if summary.locator("..").get_attribute("open") is None:
        summary.click()
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


def test_interactive_search_more_multi_gap_and_route_witness(editor):
    page, _session, url, errors = editor
    load(page, url)
    exercise_interactive_features(page)
    exercise_cached_canvas(page)
    assert not errors
