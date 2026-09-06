"""Real Chromium/WebKit tests for the local editor and shared application API."""

import os
import threading

import pytest

from duplotrain.gui import Session, make_server
from duplotrain.layout import Layout, build_chain

pytestmark = pytest.mark.browser


@pytest.fixture()
def editor(browser):
    session = Session()
    server = make_server(session, port=0)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    context = browser.new_context(
        viewport={"width": 390, "height": 844}, has_touch=True, is_mobile=True,
    )
    page = context.new_page()
    errors = []
    page.on("pageerror", lambda error: errors.append(str(error)))
    url = f"http://127.0.0.1:{server.server_port}/"
    yield page, session, url, errors
    context.close()
    server.shutdown()
    server.server_close()
    thread.join()


def load(page, url):
    page.goto(url)
    page.wait_for_function("S !== null && !apiBusy && recoveryAttempted")
    page.evaluate("saveSession()")


def wait_count(page, count):
    # S is null until the first refresh resolves, and playwright treats a thrown
    # predicate as a hard error rather than "not ready yet", so guard the reload race.
    page.wait_for_function(
        "count => S !== null && S.layout.placements.length === count && !apiBusy",
        arg=count,
    )


def place_straight(page):
    page.locator('[data-piece-id="straight"]').get_by_role("button", name="ahead").tap()
    bounds = page.locator("#canvas").bounding_box()
    page.touchscreen.tap(bounds["x"] + bounds["width"] / 2, bounds["y"] + bounds["height"] / 2)
    wait_count(page, 1)


def test_clear_undo_and_mobile_controls(editor):
    page, session, url, errors = editor
    load(page, url)
    assert page.locator("#canvas").bounding_box()["width"] <= 390
    assert page.locator("#canvas").bounding_box()["height"] >= 220
    place_straight(page)
    page.locator("#clear").tap()
    wait_count(page, 0)
    assert page.locator("#undo").is_enabled()
    page.locator("#undo").tap()
    wait_count(page, 1)
    old_scale = page.evaluate("view.scale")
    page.locator("#zoom-in").tap()
    assert page.evaluate("view.scale") > old_scale
    page.locator("#fit").tap()
    page.locator("#delete-tool").tap()
    point = page.evaluate("worldToScreen(...S.layout.placements[0].mid)")
    bounds = page.locator("#canvas").bounding_box()
    page.touchscreen.tap(bounds["x"] + point[0], bounds["y"] + point[1])
    wait_count(page, 0)
    assert not errors


def test_reload_recovers_into_a_fresh_engine(editor):
    page, session, url, errors = editor
    load(page, url)
    place_straight(page)
    count = page.locator('[data-piece-id="straight"] input')
    count.fill("17")
    count.press("Tab")
    page.wait_for_function("S.inventory.owned.straight === 17 && !apiBusy")
    page.locator("#unlimited").check()
    page.wait_for_function("S.inventory.unlimited && !apiBusy")
    page.evaluate("saveSession()")
    saved = page.evaluate("JSON.parse(localStorage.getItem(STORAGE_KEY)).snapshot")
    assert saved["inventory"]["straight"] == 17
    # Simulate a newly created worker/session, leaving browser storage untouched.
    with session.lock:
        session.history = [Layout()]
        session.inventory = dict(Session().inventory)
        session.stones = dict(Session().stones)
        session.unlimited = False
        session.revision = 0
    page.reload()
    wait_count(page, 1)
    page.wait_for_function("S.inventory.unlimited && S.inventory.owned.straight === 17")
    assert page.evaluate("S.snapshot") == saved
    assert not errors


def test_existing_server_session_is_not_overwritten_by_stale_autosave(editor):
    page, session, url, errors = editor
    load(page, url)
    place_straight(page)
    session.attach("curve", 0, (0, 1))
    page.reload()
    wait_count(page, 2)
    assert not errors


def test_stone_tool_cannot_intercept_solve_endpoint_selection(editor):
    page, session, url, errors = editor
    session.attach("switch", 0, None)
    load(page, url)
    page.locator("#stones button").filter(has_text="Direction").tap()
    assert page.evaluate("armedStone !== null")
    page.locator("#solve").tap()
    assert page.evaluate("armedStone === null && pickMode.stage === 'grow'")
    point = page.evaluate("openEndScreenPos()[0]")
    bounds = page.locator("#canvas").bounding_box()
    page.touchscreen.tap(bounds["x"] + point["x"], bounds["y"] + point["y"])
    page.wait_for_function("pickMode.stage === 'close'")
    assert not session.layout.accessories
    assert not errors


def test_right_click_does_not_place_and_cancelled_drag_does_not_place(editor):
    page, session, url, errors = editor
    load(page, url)
    page.locator('[data-piece-id="straight"]').get_by_role("button", name="ahead").tap()
    page.locator("#canvas").click(button="right")
    assert len(session.layout) == 0
    bounds = page.locator("#canvas").bounding_box()
    page.mouse.move(bounds["x"] + 100, bounds["y"] + 150)
    page.mouse.down()
    page.evaluate("Array.from(pointers.keys()).forEach(id => canvas.dispatchEvent("
                  "new PointerEvent('pointercancel', {pointerId: id})))")
    page.mouse.up()
    assert len(session.layout) == 0
    assert not errors


def test_preview_is_required_before_applying_a_candidate(editor):
    page, session, url, errors = editor
    session.inventory = {"curve": 12}
    session.history = [build_chain([(session.catalog["curve"], 0, 1)] * 6)]
    load(page, url)
    page.locator("#reversing").uncheck()
    page.locator("#solve").tap()
    page.wait_for_selector(".cand")
    candidate = page.locator(".cand").first
    assert candidate.get_by_role("button", name="Apply").is_disabled()
    candidate.get_by_role("button", name="Preview", exact=True).tap()
    assert page.evaluate("preview !== null")
    candidate.get_by_role("button", name="Apply").tap()
    wait_count(page, 12)
    assert session.layout.is_closed
    assert not errors


def test_inventory_change_removes_suggestions(editor):
    page, session, url, errors = editor
    session.inventory = {"curve": 12}
    session.history = [build_chain([(session.catalog["curve"], 0, 1)] * 6)]
    load(page, url)
    page.locator("#reversing").uncheck()
    page.locator("#solve").tap()
    page.wait_for_selector(".cand")
    count = page.locator('[data-piece-id="curve"] input')
    count.fill("6")
    count.press("Tab")
    page.wait_for_function("S.inventory.owned.curve === 6 && !apiBusy")
    assert page.locator(".cand").count() == 0
    assert not errors


def test_search_limit_message_and_deeper_search(editor):
    page, session, url, errors = editor
    session.inventory = {"straight": 34}
    layout = build_chain([(session.catalog["straight"], 0, 1)] * 34)
    for index in range(32, 0, -1):
        layout = layout.remove(index)
    session.history = [layout]
    load(page, url)
    page.locator("#reversing").uncheck()
    # Same entry point as two selected arrows, with exact endpoint IDs.
    page.evaluate("runSolve([0, 1], [1, 0])")
    assert "may still exist" in page.locator("#status").inner_text()
    assert page.locator("#expand-search").is_visible()
    page.locator("#expand-search").tap()
    page.wait_for_selector(".cand")
    assert len(session.candidates[0].layout) == 34
    assert not errors


def test_pinch_zooms_without_placing_a_piece(editor):
    if os.environ.get("DUPLOTRAIN_BROWSER", "chromium") != "chromium":
        pytest.skip("CDP touch injection is Chromium-specific")
    page, session, url, errors = editor
    load(page, url)
    page.locator('[data-piece-id="straight"]').get_by_role("button", name="ahead").tap()
    old_scale = page.evaluate("view.scale")
    cdp = page.context.new_cdp_session(page)
    for kind, points in [
        ("touchStart", [{"x": 130, "y": 200}, {"x": 230, "y": 200}]),
        ("touchMove", [{"x": 90, "y": 200}, {"x": 270, "y": 200}]),
        ("touchEnd", []),
    ]:
        cdp.send("Input.dispatchTouchEvent", {"type": kind, "touchPoints": points})
    assert page.evaluate("view.scale") > old_scale
    assert len(session.layout) == 0
    assert not errors


def test_corrupt_recovery_is_not_overwritten(editor):
    page, session, url, errors = editor
    load(page, url)
    page.evaluate("autosaveReady = false; localStorage.setItem(STORAGE_KEY, 'not json')")
    page.reload()
    page.wait_for_function("recoveryAttempted && !apiBusy")
    assert "Existing save kept" in page.locator("#save-status").inner_text()
    assert page.evaluate("localStorage.getItem(STORAGE_KEY)") == "not json"
    place_straight(page)
    assert page.evaluate("localStorage.getItem(STORAGE_KEY)") == "not json"
    assert not errors


def test_built_pyodide_app_boots_and_recovers(browser, tmp_path):
    """Exercise WASM over HTTPS under production CSP, using only visible controls.

    Playwright's wait_for_function uses string evaluation that the production CSP
    correctly forbids. Locator assertions avoid needing unsafe-eval or bypass_csp.
    HTTPS also preserves upgrade-insecure-requests in WebKit, as on the real site.
    """
    import json
    import re
    import ssl
    import subprocess
    from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
    from pathlib import Path

    dist = os.environ.get("DUPLOTRAIN_STATIC_DIST")
    if not dist:
        pytest.skip("set DUPLOTRAIN_STATIC_DIST to a built webapp/dist directory")
    policy = re.search(
        r'Content-Security-Policy "([^"\n]+)"',
        (Path(dist) / ".htaccess").read_text(),
    ).group(1)
    cert, key = tmp_path / "cert.pem", tmp_path / "key.pem"
    subprocess.run([
        "openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes",
        "-keyout", str(key), "-out", str(cert), "-days", "1",
        "-subj", "/CN=localhost", "-addext", "subjectAltName=IP:127.0.0.1,DNS:localhost",
    ], check=True, capture_output=True)

    class Handler(SimpleHTTPRequestHandler):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, directory=dist, **kwargs)

        def end_headers(self):
            self.send_header("Content-Security-Policy", policy)
            super().end_headers()

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    tls = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    tls.minimum_version = ssl.TLSVersion.TLSv1_2
    tls.load_cert_chain(cert, key)
    server.socket = tls.wrap_socket(server.socket, server_side=True)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    # Trust only this test's self-signed certificate; keep the actual CSP intact.
    context = browser.new_context(
        viewport={"width": 390, "height": 844}, has_touch=True, ignore_https_errors=True,
    )
    page = context.new_page()
    errors = []
    page.on("pageerror", lambda error: errors.append(str(error)))
    from playwright.sync_api import expect

    def export_layout():
        with page.expect_download() as info:
            page.locator("#export").tap()
        return json.loads(Path(info.value.path()).read_text())

    try:
        page.goto(f"https://127.0.0.1:{server.server_port}/")
        expect(page.locator("#status")).to_contain_text("Engine ready", timeout=90000)
        page.locator('[data-piece-id="straight"]').get_by_role("button", name="ahead").tap()
        bounds = page.locator("#canvas").bounding_box()
        page.touchscreen.tap(bounds["x"] + bounds["width"] / 2,
                             bounds["y"] + bounds["height"] / 2)
        expect(page.locator("#undo")).to_be_enabled()
        owned = page.locator('[data-piece-id="straight"] input')
        owned.fill("17")
        owned.press("Tab")
        expect(page.locator('[data-piece-id="straight"] .count')).to_have_text("16/")
        expect(owned).to_have_value("17")
        saved = export_layout()
        assert len(saved["placements"]) == 1
        assert saved["placements"][0]["piece"] == "straight"
        page.reload()
        expect(page.locator("#status")).to_contain_text("Engine ready", timeout=90000)
        expect(owned).to_have_value("17")
        expect(page.locator('[data-piece-id="straight"] .count')).to_have_text("16/")
        assert export_layout() == saved
        saved["links"] = [[0, 0, 0, 1]]  # deliberately forced, 128 mm gap
        page.locator("#importfile").set_input_files({
            "name": "forced.json", "mimeType": "application/json",
            "buffer": json.dumps(saved).encode(),
        })
        expect(page.locator("#status")).to_contain_text("not exactly closed")
        expect(page.locator("#save-status")).to_contain_text("Autosaved")
        assert export_layout() == saved
        page.reload()
        expect(page.locator("#status")).to_contain_text("not exactly closed", timeout=90000)
        assert export_layout() == saved
        assert not errors
    finally:
        context.close()
        server.shutdown()
        server.server_close()
        thread.join()


def test_stale_tab_cannot_overwrite_newer_autosave_on_close(editor):
    page, session, url, errors = editor
    load(page, url)
    newer = page.context.new_page()
    try:
        load(newer, url)
        place_straight(newer)
        newer.evaluate("saveSession()")
        checkpoint = newer.evaluate("localStorage.getItem(STORAGE_KEY)")
        page.wait_for_function("!autosaveReady")
        assert "Another tab" in page.locator("#save-status").inner_text()
        newer.close()
        # Exercise the previous failure path, then close the actually stale page.
        page.evaluate("window.dispatchEvent(new Event('pagehide'))")
        page.evaluate("saveSession()")
        assert page.evaluate("localStorage.getItem(STORAGE_KEY)") == checkpoint
        observer = page.context.new_page()
        load(observer, url)
        assert observer.evaluate("localStorage.getItem(STORAGE_KEY)") == checkpoint
        page.close()
        assert observer.evaluate("localStorage.getItem(STORAGE_KEY)") == checkpoint
        observer.close()
        assert not errors
    finally:
        if not newer.is_closed():
            newer.close()


def test_imported_forced_fit_stays_visible_after_reload(editor):
    import json

    from duplotrain.layout import layout_to_dict

    page, session, url, errors = editor
    layout = build_chain([(session.catalog["straight"], 0, 1)])
    layout = layout.join(*layout.connectable_ends(), force=True)
    load(page, url)
    page.locator("#importfile").set_input_files({
        "name": "forced.json", "mimeType": "application/json",
        "buffer": json.dumps(layout_to_dict(layout)).encode(),
    })
    wait_count(page, 1)
    assert "not exactly closed" in page.locator("#status").inner_text()
    assert "128" in page.locator("#status").inner_text()
    page.evaluate("saveSession()")
    page.reload()
    wait_count(page, 1)
    assert "not exactly closed" in page.locator("#status").inner_text()
    assert "Forced fit" in page.locator("#status").inner_text()
    assert not errors
