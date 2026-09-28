"""Hold update replies while the real editor/HTTP engine receives other actions."""

import json
from threading import Thread

import pytest

from duplotrain.editor import Session
from duplotrain.gui import make_server


@pytest.mark.browser
@pytest.mark.parametrize("phase", ["STATUS", "ACTIVATE"])
def test_update_verification_and_activation_exclude_edits(browser, phase):
    session = Session()
    server = make_server(session, 0)
    thread = Thread(target=server.serve_forever, daemon=True)
    thread.start()
    context = browser.new_context(accept_downloads=True)
    try:
        page = context.new_page()
        errors = []
        page.on("pageerror", lambda error: errors.append(str(error)))
        page.on("dialog", lambda dialog: dialog.accept())
        page.goto(f"http://127.0.0.1:{server.server_port}/")
        page.wait_for_function("S && !apiBusy && recoveryAttempted")
        before = session.snapshot()
        # Only the service-worker replies are controlled. The DOM, busy state,
        # api() guard, downloads and Python engine are the real application.
        page.evaluate("""phase => {
          const worker = new EventTarget(); worker.state = 'activated';
          offlineRegistration = {waiting: worker, active: {}};
          offlineMessage = async (_worker, type) => type === phase ?
            new Promise((_resolve, reject) => { window.rejectUpdate = reject; }) :
            {ready: true, activated: true};
          void applyOfflineUpdate();
        }""", phase)
        # Return a boolean: Playwright invokes a function-valued predicate, which
        # would otherwise call the rejection callback and end our held update.
        page.wait_for_function("apiBusy && typeof window.rejectUpdate === 'function'")
        assert page.locator("body").evaluate("el => el.classList.contains('busy')")
        assert page.locator("#place-first").evaluate(
            "el => getComputedStyle(el).pointerEvents") == "none"
        for endpoint in ("/api/attach", "/api/project/open", "/api/search/start"):
            refused = page.evaluate("""async path => {
              try { await api(path, {piece: 'straight', entry: 0, at: null}); }
              catch (error) { return error.message; }
              return 'unexpectedly accepted';
            }""", endpoint)
            assert "action is still running" in refused
        assert session.snapshot() == before
        with page.expect_download() as download:
            page.locator("#export").click()
        assert json.loads(download.value.path().read_text()) == before["layout"]
        page.evaluate("window.rejectUpdate(new Error('test ends held update'))")
        page.wait_for_function("!apiBusy && !offlineWorking")
        assert not page.locator("body").evaluate("el => el.classList.contains('busy')")
        page.evaluate("""async () => {
          S = await api('/api/attach', {piece: 'straight', entry: 0, at: null});
        }""")
        assert len(session.layout) == 1
        assert errors == []
    finally:
        context.close()
        server.shutdown()
        server.server_close()
        thread.join(timeout=5)
