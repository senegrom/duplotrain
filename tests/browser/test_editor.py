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
    # This helper also runs against the real worker under production CSP.
    # Wait on rendered navigation instead of evaluating a string predicate.
    from playwright.sync_api import expect

    expect(page.locator("#piece-select option")).to_have_count(count)


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

    from duplotrain.catalog import default_catalog
    from duplotrain.layout import layout_to_dict

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

    page.add_init_script("""
      const NativeWorker = window.Worker;
      window.Worker = class extends NativeWorker {
        constructor(...args) { super(...args); window.__testWorker = this; }
      };
    """)
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

        # Exercise exact completion in WASM as well as import/restore. Keeping
        # reversing enabled bypasses the editor's ring shortcut and reaches DFS.
        half_circle = build_chain([(default_catalog()["curve"], 0, 1)] * 6)
        page.locator("#importfile").set_input_files({
            "name": "half-circle.json", "mimeType": "application/json",
            "buffer": json.dumps(layout_to_dict(half_circle)).encode(),
        })
        expect(page.locator("#status")).to_contain_text("6 pieces")
        for pid, count, remaining in (("curve", "12", "6/"), ("straight", "4", "4/")):
            control = page.locator(f'[data-piece-id="{pid}"] input')
            control.fill(count)
            control.press("Tab")
            expect(control).to_have_value(count)
            expect(page.locator(f'[data-piece-id="{pid}"] .count')).to_have_text(remaining)
        page.locator("#reversing").check()
        page.locator("#solve").tap()
        expect(page.locator(".cand")).to_have_count(3, timeout=30000)
        assert page.evaluate("S.candidates.every(c => c.preview.format === 'duplotrain-preview/1')")
        candidate = page.locator(".cand").first
        candidate.get_by_role("button", name="Preview", exact=True).tap()
        candidate.get_by_role("button", name="Apply").tap()
        expect(page.locator("#status")).to_contain_text("Connectors closed")
        closed = export_layout()
        assert len(closed["placements"]) == 12 and len(closed["links"]) == 12

        # A height mismatch forces the full-inventory stage, exercising projected
        # reachability and future junction targets in the actual worker.
        catalog = default_catalog()
        bridge = build_chain([(catalog["curve"], 0, 1)] * 6 + [(catalog["ramp"], 0, 1)])
        page.locator("#importfile").set_input_files({
            "name": "bridge-gap.json", "mimeType": "application/json",
            "buffer": json.dumps(layout_to_dict(bridge)).encode(),
        })
        expect(page.locator("#status")).to_contain_text("7 pieces")
        page.locator("#slop").fill("1")
        page.locator("#solve").tap()
        candidate = page.locator(".cand").first
        expect(candidate).to_be_visible(timeout=30000)
        candidate.get_by_role("button", name="Preview", exact=True).tap()
        candidate.get_by_role("button", name="Apply").tap()
        expect(page.locator("#status")).to_contain_text("Connectors closed")
        assert len(export_layout()["placements"]) == 14

        # A longer tail exercises heading-conditioned bounds beyond the six-step
        # exact table. Preview and apply must preserve the hand-built base in WASM.
        long_gap = build_chain([(catalog["straight"], 0, 1)] * 4
                               + [(catalog["curve"], 0, 1)] * 2)
        page.locator("#importfile").set_input_files({
            "name": "long-gap.json", "mimeType": "application/json",
            "buffer": json.dumps(layout_to_dict(long_gap)).encode(),
        })
        expect(page.locator("#status")).to_contain_text("6 pieces")
        for pid, count, remaining in (("curve", "16", "14/"), ("straight", "12", "8/")):
            control = page.locator(f'[data-piece-id="{pid}"] input')
            control.fill(count)
            control.press("Tab")
            expect(page.locator(f'[data-piece-id="{pid}"] .count')).to_have_text(remaining)
        page.locator("#solve").tap()
        candidate = page.locator(".cand").first
        expect(candidate).to_be_visible(timeout=30000)
        candidate.get_by_role("button", name="Preview", exact=True).tap()
        candidate.get_by_role("button", name="Apply").tap()
        expect(page.locator("#status")).to_contain_text("Connectors closed")
        closed = export_layout()
        assert len(closed["placements"]) == 20 and len(closed["links"]) == 20
        assert closed["placements"][:6] == layout_to_dict(long_gap)["placements"]

        # A connected imported base already has one forced joint. The new closing
        # joint needs another 5 mm; preview/apply must keep both gaps visible.
        from benchmarks.completion import cases

        offset = next(case for case in cases(catalog) if case.name == "offset_circle_slop_5")
        forced_base = offset.base.join((2, 1), (3, 0), force=True)
        page.locator("#importfile").set_input_files({
            "name": "offset-circle.json", "mimeType": "application/json",
            "buffer": json.dumps(layout_to_dict(forced_base)).encode(),
        })
        expect(page.locator("#status")).to_contain_text("2 open end(s). Forced fit: 5.000 mm")
        for pid, count, remaining in (("curve", "12", "6/"), ("straight", "4", "4/")):
            control = page.locator(f'[data-piece-id="{pid}"] input')
            control.fill(count)
            control.press("Tab")
            expect(page.locator(f'[data-piece-id="{pid}"] .count')).to_have_text(remaining)
        page.locator("#slop").fill("5")
        page.locator("#solve").tap()
        expect(page.locator(".cand")).to_have_count(3, timeout=30000)
        assert page.evaluate("S.candidates.every(c => c.preview.format === 'duplotrain-preview/1')")
        candidate = page.locator(".cand").first
        expect(candidate).to_contain_text("forced 5")
        candidate.get_by_role("button", name="Preview", exact=True).tap()
        candidate.get_by_role("button", name="Apply").tap()
        expect(page.locator("#status")).to_contain_text("Forced fit")
        forced = export_layout()
        assert len(forced["placements"]) == 12 and len(forced["links"]) == 12
        assert forced["placements"][:6] == layout_to_dict(forced_base)["placements"]
        from duplotrain.layout import layout_from_dict

        issues = layout_from_dict(forced, default_catalog()).joint_issues()
        assert len(issues) == 2
        assert sum(joint["gap_mm"] for joint in issues) == pytest.approx(10)
        exercise_project_history_and_tools(page)
        # Force a genuine worker failure after confirmed work. Emergency downloads
        # must use the displayed snapshot, then a new worker must restore it.
        confirmed = page.evaluate("S.snapshot")
        page.evaluate("""() => {
          const worker = window.__testWorker;
          if (!worker) throw new Error("test worker was not captured");
          worker.dispatchEvent(new ErrorEvent("error", {
            message: "test engine failure", cancelable: true
          }));
        }""")
        with page.expect_download() as recovered:
            page.get_by_role("button", name="Download last confirmed session", exact=True).tap()
        assert json.loads(Path(recovered.value.path()).read_text()) == confirmed
        page.get_by_role(
            "button", name="Restart engine and restore last confirmed session", exact=True,
        ).tap()
        expect(page.locator("#status")).to_contain_text("Engine restarted", timeout=90000)
        assert page.evaluate("S.snapshot") == confirmed
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


def test_stale_tab_refreshes_without_replaying_a_delete(editor):
    page, session, url, errors = editor
    session.attach("straight", 0, None)
    session.attach("curve", 0, (0, 1))
    session.attach("switch", 0, (1, 1))
    load(page, url)
    other = page.context.new_page()
    other.on("pageerror", lambda error: errors.append(str(error)))
    try:
        load(other, url)
        other.evaluate("async () => { S = await api('/api/remove', {placement: 0}); redraw(); }")
        # This tab still displays the curve at index 1. Its old index must not
        # remove the switch now occupying index 1 on the shared server.
        assert page.evaluate("S.layout.placements[1].piece") == "curve"
        page.locator("#delete-tool").tap()
        point = page.evaluate("worldToScreen(...S.layout.placements[1].mid)")
        bounds = page.locator("#canvas").bounding_box()
        page.touchscreen.tap(bounds["x"] + point[0], bounds["y"] + point[1])
        wait_count(page, 2)
        assert [p.piece.id for p in session.layout] == ["curve", "switch"]
        assert page.evaluate("S.layout.placements.map(p => p.piece)") == ["curve", "switch"]
        assert page.evaluate("S.revision") == session.revision
        assert page.evaluate("deleting") is False
        assert "not applied" in page.locator("#status").inner_text()
        assert not errors
    finally:
        other.close()


def test_stale_tab_export_saves_the_displayed_layout(editor):
    import json
    from pathlib import Path

    page, session, url, errors = editor
    session.attach("straight", 0, None)
    load(page, url)
    displayed = page.evaluate("S.snapshot.layout")
    other = page.context.new_page()
    try:
        load(other, url)
        other.locator("#clear").tap()
        wait_count(other, 0)
        page.wait_for_function("!autosaveReady")
        assert page.evaluate("S.layout.placements.length") == 1
        # Recovery export must still work if the server has gone offline.
        page.route("**/api/**", lambda route: route.abort())
        with page.expect_download() as downloaded:
            page.locator("#export").tap()
        assert json.loads(Path(downloaded.value.path()).read_text()) == displayed
        assert not errors
    finally:
        other.close()


@pytest.mark.parametrize("intervening", ["import", "edit"])
def test_delayed_import_cannot_overwrite_newer_work(editor, intervening):
    import json

    from duplotrain.layout import layout_to_dict

    page, session, url, errors = editor
    load(page, url)
    page.evaluate("""() => {
      window.importReads = [];
      const read = File.prototype.text;
      File.prototype.text = function() {
        return new Promise((resolve, reject) => {
          window.importReads.push(() => read.call(this).then(resolve, reject));
        });
      };
    }""")

    def choose(piece):
        layout = build_chain([(session.catalog[piece], 0, 1)])
        page.locator("#importfile").set_input_files({
            "name": f"{piece}.json", "mimeType": "application/json",
            "buffer": json.dumps(layout_to_dict(layout)).encode(),
        })

    choose("curve")
    if intervening == "import":
        choose("straight")
        page.evaluate("window.importReads[1]()")
        wait_count(page, 1)
    else:
        place_straight(page)
    page.evaluate("window.importReads[0]()")
    page.wait_for_function("!apiBusy")
    assert page.evaluate("S.layout.placements.map(p => p.piece)") == ["straight"]
    assert [p.piece.id for p in session.layout] == ["straight"]
    if intervening == "edit":
        assert "not applied" in page.locator("#status").inner_text()
    assert not errors


def test_stale_sandbox_toggle_matches_the_refreshed_engine(editor):
    page, session, url, errors = editor
    load(page, url)
    session.attach("straight", 0, None)
    # Dispatch a real change without check() insisting the rejected toggle sticks.
    page.locator("#unlimited").tap()
    page.wait_for_function("S.revision === 1 && !apiBusy")
    assert not page.locator("#unlimited").is_checked()
    assert page.evaluate("S.inventory.unlimited") is False
    assert session.unlimited is False
    assert "not applied" in page.locator("#status").inner_text()
    assert not errors


def test_redraw_preserves_control_identity_focus_and_unsubmitted_inventory(editor):
    page, _session, url, errors = editor
    load(page, url)
    field = page.locator('[data-piece-id="straight"] input')
    field.focus()
    field.fill("321")
    page.evaluate("""() => {
      window.retainedInput = document.activeElement;
      window.retainedSet = document.querySelector('#sets button');
      window.retainedStone = document.querySelector('#stones button');
      // A round trip supplies new objects even when the catalogue is unchanged.
      S = JSON.parse(JSON.stringify(S));
      redraw();
    }""")
    assert field.input_value() == "321"
    assert page.evaluate("document.activeElement === window.retainedInput")
    assert page.evaluate("document.querySelector('#sets button') === window.retainedSet")
    assert page.evaluate("document.querySelector('#stones button') === window.retainedStone")
    field.press("Tab")
    page.wait_for_function("S.inventory.owned.straight === 321 && !apiBusy")
    assert page.evaluate("document.querySelector('[data-piece-id=straight] input') "
                         "=== window.retainedInput")
    # Visibility changes in unlimited mode must not detach/duplicate the input.
    page.locator("#unlimited").check()
    page.wait_for_function("S.inventory.unlimited && !apiBusy")
    assert not field.is_visible()
    page.locator("#unlimited").uncheck()
    page.wait_for_function("!S.inventory.unlimited && !apiBusy")
    assert field.is_visible() and field.input_value() == "321"
    assert not errors


def test_candidate_preview_selection_preserves_card_and_button_identity(editor):
    page, session, url, errors = editor
    session.inventory = {"curve": 12}
    session.history = [build_chain([(session.catalog["curve"], 0, 1)] * 6)]
    load(page, url)
    page.locator("#reversing").uncheck()
    page.locator("#solve").tap()
    page.wait_for_selector(".cand")
    assert page.evaluate("S.candidates[0].preview.format") == "duplotrain-preview/1"
    page.evaluate("window.retainedCard = document.querySelector('.cand'); "
                  "window.retainedPreview = window.retainedCard.querySelector('button')")
    card = page.locator(".cand").first
    card.get_by_role("button", name="Preview", exact=True).tap()
    assert page.evaluate("document.querySelector('.cand') === window.retainedCard")
    assert page.evaluate("document.querySelector('.cand button') === window.retainedPreview")
    assert card.get_by_role("button", name="Apply").is_enabled()
    page.evaluate("redraw()")
    assert page.evaluate("document.querySelector('.cand') === window.retainedCard")
    assert card.get_by_role("button", name="Previewing").get_attribute("aria-pressed") == "true"
    card.get_by_role("button", name="Apply").tap()
    wait_count(page, 12)
    assert session.layout.is_closed
    assert page.locator(".cand").count() == 0
    assert not errors


def test_reported_bridge_search_preview_apply_and_undo(editor):
    import json
    from pathlib import Path

    from duplotrain.layout import layout_from_dict
    from duplotrain.solver import _solution_overlaps

    page, session, url, errors = editor
    fixture = Path(__file__).parents[1] / "fixtures/bridge-gap.json"
    base = layout_from_dict(json.loads(fixture.read_text()), session.catalog)
    load(page, url)
    page.locator("#importfile").set_input_files(str(fixture))
    wait_count(page, 59)
    page.locator("#unlimited").check()
    page.wait_for_function("S.inventory.unlimited && !apiBusy")
    page.locator("#reversing").uncheck()
    page.locator("#solve").tap()
    page.wait_for_selector(".cand", timeout=30000)
    assert page.locator(".cand").count() == 8
    assert page.evaluate("S.candidates.every(c => c.preview.format === 'duplotrain-preview/1' "
                         "&& c.preview.base_count === 59 && c.preview.placements.length === 24)")
    assert page.locator("#expand-search").is_visible()
    assert page.evaluate("S.searched") < 50000
    candidate = page.locator(".cand").first
    candidate.get_by_role("button", name="Preview", exact=True).tap()
    candidate.get_by_role("button", name="Apply").tap()
    wait_count(page, 83)
    assert session.layout.placements[:59] == base.placements
    assert session.layout.is_closed and not session.layout.joint_issues()
    assert not _solution_overlaps(session.layout, 0, 120, 8)
    page.locator("#undo").tap()
    wait_count(page, 59)
    assert session.layout == base
    assert not errors


def exercise_project_history_and_tools(page):
    """Run identical new UI flows on the HTTP host and the real WASM worker."""
    import json
    from pathlib import Path

    from playwright.sync_api import expect

    from duplotrain.catalog import default_catalog
    from duplotrain.layout import layout_to_dict

    layout = build_chain([(default_catalog()["curve"], 0, 1)] * 12).join((0, 0), (11, 1))
    project = {
        "format": "duplotrain-project/1", "name": "Portable circle",
        "session": {"format": "duplotrain-session/1", "layout": layout_to_dict(layout),
                    "inventory": {"curve": 15}, "stones": {"stone_stop": 3}, "unlimited": False},
        "preferences": {"search": {"max_pieces": 52, "slop": 0, "reversing": False}},
    }
    page.locator("#projectfile").set_input_files({
        "name": "circle.project.json", "mimeType": "application/json",
        "buffer": json.dumps(project).encode(),
    })
    wait_count(page, 12)
    expect(page.locator("#max-pieces")).to_have_value("52")
    expect(page.locator("#project-name")).to_have_value("Portable circle")
    field = page.locator('[data-piece-id="curve"] input')
    # Locator assertions wait for accepted UI state without dynamic string eval;
    # this helper also runs under the production CSP in the real worker test.
    field.fill("2")
    field.press("Tab")
    expect(page.locator('[data-piece-id="curve"] .count')).to_have_text("0/")
    expect(field).to_have_value("2")
    expect(page.locator("#project-status")).to_contain_text("Changed since last project")
    page.locator("#undo").tap()
    expect(page.locator('[data-piece-id="curve"] .count')).to_have_text("3/")
    expect(field).to_have_value("15")
    expect(page.locator("#project-status")).to_contain_text("Unchanged since last project")
    assert page.evaluate("S.layout.placements.length") == 12
    page.locator("#redo").tap()
    expect(page.locator('[data-piece-id="curve"] .count')).to_have_text("0/")
    expect(field).to_have_value("2")
    page.locator("#check-layout").tap()
    expect(page.locator("#diagnostics")).to_contain_text("Connectors: exactly closed")
    expect(page.locator("#diagnostics")).to_contain_text("Overlaps: 0")
    expect(page.locator("#diagnostics")).to_contain_text("10")
    # A rejected inventory edit must restore its confirmed value, not show -1.
    field.fill("-1")
    field.press("Tab")
    expect(field).to_have_value("2")
    panel = page.locator("details").filter(has=page.locator("#test-train"))
    panel.locator(":scope > summary").tap()
    page.locator("#train-start").select_option("[0,0]")
    page.locator("#test-train").tap()
    expect(page.locator("#train-report")).to_contain_text("from this start: endless")
    page.locator("#train-step").tap()
    expect(page.locator("#train-report")).to_contain_text("Step 1/12")
    page.locator("#train-play").tap()
    page.locator("#train-pause").tap()
    panel = page.locator("details").filter(has=page.locator("#save-project"))
    panel.locator(":scope > summary").tap()
    with page.expect_download() as download:
        page.locator("#save-project").tap()
    portable = json.loads(Path(download.value.path()).read_text())
    assert portable["session"] == page.evaluate("S.snapshot")
    assert portable["preferences"]["search"]["max_pieces"] == 52
    page.locator("#save-local").tap()
    page.locator("#save-local").tap()
    expect(page.locator("#project-slots option")).to_have_count(2)
    labels = page.locator("#project-slots option").all_text_contents()
    assert len(set(labels)) == 2 and all("12 pieces" in label for label in labels)
    expect(page.locator("#project-status")).to_contain_text("Unchanged since last project")
    page.locator("#rename-local").tap()
    page.get_by_label("New backup name", exact=True).fill("Circle backup renamed")
    page.get_by_role("button", name="Confirm rename", exact=True).tap()
    expect(page.locator("#project-slots option:checked")).to_contain_text("Circle backup renamed")
    expect(page.locator("#project-name")).to_have_value("Portable circle")
    page.locator("#delete-local").tap()
    page.get_by_role("button", name="Cancel backup change", exact=True).tap()
    expect(page.locator("#project-slots option")).to_have_count(2)
    page.locator("#delete-local").tap()
    page.get_by_role("button", name="Confirm delete", exact=True).tap()
    expect(page.locator("#project-slots option")).to_have_count(1)
    wait_count(page, 12)
    page.locator("#clear").tap()
    wait_count(page, 0)
    page.locator("#projectfile").set_input_files({
        "name": "saved.project.json", "mimeType": "application/json",
        "buffer": json.dumps(portable).encode(),
    })
    wait_count(page, 12)
    assert page.evaluate("S.snapshot") == portable["session"]
    page.locator("#undo").tap()
    wait_count(page, 0)
    page.locator("#redo").tap()
    wait_count(page, 12)
    exercise_train_finishing(page)


def test_project_history_diagnostics_and_train_ui(editor):
    page, _session, url, errors = editor
    load(page, url)
    exercise_project_history_and_tools(page)
    assert not errors


def test_endpoint_selection_clears_after_import_and_keyboard_attach(editor):
    import json

    from duplotrain.layout import layout_to_dict

    page, session, url, errors = editor
    session.attach("switch", 0, None)
    load(page, url)
    page.locator("#solve").tap()
    page.evaluate("activateEnd([0, 1])")
    assert page.evaluate("pickMode.grow") == [0, 1]
    curve = build_chain([(session.catalog["curve"], 0, 1)])
    page.locator("#importfile").set_input_files({
        "name": "replacement.json", "mimeType": "application/json",
        "buffer": json.dumps(layout_to_dict(curve)).encode(),
    })
    page.wait_for_function("S.layout.placements[0].piece === 'curve' && !apiBusy")
    assert page.evaluate("pickMode") is None
    panel = page.locator("details").filter(has=page.locator("#end-select"))
    panel.locator(":scope > summary").tap()
    page.locator('[data-piece-id="straight"]').get_by_role("button", name="ahead").tap()
    page.locator("#end-select").select_option("[0,1]")
    page.locator("#use-end").tap()
    wait_count(page, 2)
    assert session.layout.links[(0, 1)] == (1, 0)
    assert not errors


def test_overlap_chooser_and_elevation_picking(editor):
    from duplotrain.geometry import Pose
    from duplotrain.layout import Placement

    page, session, url, errors = editor
    piece = session.catalog["straight"]
    session.history = [Layout((Placement(piece, Pose.make(z=200)),
                               Placement(piece, Pose.make()),
                               Placement(piece, Pose.make(x=1000))))]
    load(page, url)
    assert page.evaluate("placementAt(...worldToScreen(64, 0))") == 0
    page.locator("#delete-tool").tap()
    # Use the real canvas removal path; ambiguity must not immediately delete.
    page.evaluate("removeAt(...worldToScreen(64, 0))")
    assert len(session.layout) == 3
    panel = page.locator("details").filter(has=page.locator("#piece-select"))
    panel.locator(":scope > summary").tap()
    page.locator("#piece-select").select_option("2")
    from playwright.sync_api import expect

    expect(page.locator("#overlap-picker")).to_be_hidden()
    assert len(session.layout) == 3
    page.evaluate("removeAt(...worldToScreen(64, 0))")
    page.locator("#overlap-picker select").select_option("1")
    page.get_by_role("button", name="Remove highlighted piece").tap()
    wait_count(page, 2)
    assert float(session.layout.placements[0].frame.z) == 200
    assert float(session.layout.placements[1].frame.x) == 1000
    page.locator("#undo").tap()
    wait_count(page, 3)
    assert not errors


def exercise_train_finishing(page):
    """Terminal playback and explicit coverage/settings on both real hosts."""
    import json
    from pathlib import Path

    from playwright.sync_api import expect

    from duplotrain.catalog import default_catalog
    from duplotrain.layout import layout_to_dict

    c = default_catalog()
    stopped = build_chain([(c["straight"], 0, 1)] * 2).with_accessory(1, "stone_stop")
    page.locator("#importfile").set_input_files({
        "name": "stopped.json", "mimeType": "application/json",
        "buffer": json.dumps(layout_to_dict(stopped)).encode(),
    })
    wait_count(page, 2)
    page.locator("#train-start").select_option("[0,0]")
    page.locator("#test-train").tap()
    expect(page.locator("#train-report")).to_contain_text("from this start: stopped")
    expect(page.locator("#train-report")).to_contain_text("2 / 2 drivable pieces visited")
    page.locator("#train-step").tap()
    expect(page.locator("#train-report")).to_contain_text("Step 1/1: #1")
    page.locator("#train-step").tap()
    expect(page.locator("#train-report")).to_contain_text("Final event: #2")
    expect(page.locator("#train-step")).to_be_disabled()
    assert page.evaluate("trainTrace.steps.length") == 1
    assert page.evaluate("trainTrace.terminal.placement") == 1
    page.locator("#train-play").tap()
    expect(page.locator("#train-report")).to_contain_text("Final event: #2")

    completed = (Path(__file__).parent.parent / "fixtures" / "bridge-completed.json").read_bytes()
    page.locator("#importfile").set_input_files({
        "name": "bridge-completed.json", "mimeType": "application/json", "buffer": completed,
    })
    wait_count(page, 83)
    page.locator("#train-start").select_option("[0,0]")
    page.locator("#test-train").tap()
    expect(page.locator("#train-report")).to_contain_text("41 / 83 drivable pieces visited")
    expect(page.locator("#train-report")).to_contain_text("cycle 26 steps")
    page.locator("#train-unvisited").check()
    page.locator("#train-cycle").check()
    assert page.evaluate("trainTrace.unvisited.length") == 42
    assert page.evaluate("trainTrace.cycle_pieces.length") == 26
    page.locator("#train-switches").locator("..").locator(":scope > summary").tap()
    page.get_by_label("Initial switch #4", exact=True).select_option("2")
    expect(page.locator("#train-report")).to_have_text("")
    expect(page.locator("#train-cycle")).not_to_be_checked()
    expect(page.locator("#train-step")).to_be_disabled()
    page.locator("#test-train").tap()
    expect(page.locator("#train-report")).to_contain_text("Selected initial switches")
    assert page.evaluate("trainTrace.initial_switch_states['3']") == 2


def test_clear_empty_keeps_redo_in_the_editor(editor):
    from playwright.sync_api import expect

    page, session, url, errors = editor
    load(page, url)
    place_straight(page)
    page.locator("#undo").tap()
    wait_count(page, 0)
    expect(page.locator("#redo")).to_be_enabled()
    revision = session.revision
    page.locator("#clear").tap()
    expect(page.locator("#redo")).to_be_enabled()
    page.locator("#redo").tap()
    wait_count(page, 1)
    assert session.revision == revision + 1
    assert not errors
