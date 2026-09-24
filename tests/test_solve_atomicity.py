"""Rejected, interrupted or cancelled editor searches must not consume a revision."""

import json
import threading

import pytest

import duplotrain.editor as editor
from duplotrain import build_chain, default_catalog
from duplotrain.gui import Session, dispatch_session
from duplotrain.solver import Solution, SolveResult, SolveStats
from tests.editor_support import load_adapter, post, running_server, unchanged


def session_with_candidate():
    catalog = default_catalog()
    recipe = [(catalog["curve"], 0, 1)]
    base = build_chain(recipe * 11)
    closed = build_chain(recipe * 12).join((0, 0), (11, 1))
    session = Session(catalog=catalog, inventory={"curve": 12, "buffer": 1}, history=[base])
    session.revision = session._candidate_revision = 9
    session.candidates = [Solution(closed, (), 0.0, True, 0, ())]
    return session


@pytest.mark.parametrize("failure", ["oracle", "solver", "second_stage", "progress"])
def test_search_failures_preserve_existing_usable_candidates(monkeypatch, failure):
    session = session_with_candidate()
    before = unchanged(session)
    candidates = session.candidates

    def fail(*args, **kwargs):
        raise ValueError("injected search failure")

    monkeypatch.setattr(Session, "_arc_closures", fail if failure == "oracle" else
                        lambda self, *args: [])
    calls = []

    def search(inventory, pieces, config, **kwargs):
        calls.append(inventory)
        if failure == "second_stage" and len(calls) == 1:
            return SolveResult([], SolveStats(complete=True, stop_reason="exhausted"))
        if failure == "progress":
            # Succeed if the callback's error were swallowed: only it can fail this.
            config.progress(4096)
            return SolveResult([], SolveStats(complete=True, stop_reason="exhausted"))
        return fail()

    monkeypatch.setattr(editor, "solve", search)
    with pytest.raises(ValueError, match="injected search failure"):
        dispatch_session(session, "/api/solve", {"revision": 9}, progress=fail)
    assert unchanged(session) == before
    assert session.candidates is candidates
    if failure == "second_stage":
        assert len(calls) == 2
    # The last successfully published suggestion remains applicable.
    session.apply_candidate(0, revision=9)
    assert session.layout.is_closed


@pytest.mark.parametrize("result_kind", ["oracle", "solver", "empty", "height_impossible"])
def test_successful_search_publishes_exactly_one_new_revision(monkeypatch, result_kind):
    session = session_with_candidate()
    candidates = list(session.candidates)
    if result_kind == "height_impossible":
        session = Session(inventory={}, history=[build_chain([
            (default_catalog()["ramp"], 0, 1),
        ])])
    monkeypatch.setattr(Session, "_arc_closures", lambda self, *args:
                        candidates if result_kind == "oracle" else [])
    monkeypatch.setattr(editor, "solve", lambda *args, **kwargs: SolveResult(
        candidates if result_kind == "solver" else [],
        SolveStats(complete=True, stop_reason="exhausted"),
    ))
    revision = session.revision
    result = dispatch_session(session, "/api/solve", {"revision": revision})
    assert result["revision"] == session.revision == revision + 1
    assert session._candidate_revision == session.revision
    assert result["found"] == (1 if result_kind in ("oracle", "solver") else 0)
    if result_kind == "height_impossible":
        assert result["stop_reason"] == "height_impossible"


def unjoined_circle_session():
    catalog = default_catalog()
    return Session(catalog=catalog, inventory={"curve": 12}, history=[
        build_chain([(catalog["curve"], 0, 1)] * 12),
    ])


def test_rejected_solve_preserves_session_revision():
    catalog = default_catalog()
    unjoined_circle = build_chain([(catalog["curve"], 0, 1)] * 12)
    session = Session(catalog=catalog, inventory={"curve": 12}, history=[unjoined_circle])
    before = session.snapshot(), session.revision, session._candidate_revision
    with pytest.raises(ValueError, match="already mate"):
        dispatch_session(session, "/api/solve", {
            "revision": session.revision, "reversing": True,
        })
    after = session.snapshot(), session.revision, session._candidate_revision
    preserved = after == before
    assert preserved, "a rejected request changed revision/candidate state"


def test_http_error_does_not_make_the_next_explicit_join_stale():
    session = unjoined_circle_session()
    with running_server(session) as server:
        before = unchanged(session)
        status, result = post(server, "/api/solve", {"revision": 0, "reversing": True})
        assert status == 409 and "already mate" in result["error"]
        assert unchanged(session) == before
        status, result = post(server, "/api/join", {"revision": 0, "a": [0, 0], "b": [11, 1]})
        assert status == 200 and result["layout"]["exactly_closed"]


def test_pyodide_error_preserves_the_same_revision_contract():
    adapter = load_adapter(unjoined_circle_session())
    before = unchanged(adapter.session)
    result = json.loads(adapter.dispatch("/api/solve", '{"revision":0,"reversing":true}'))
    assert "already mate" in result["__error"]
    assert unchanged(adapter.session) == before
    joined = json.loads(adapter.dispatch("/api/join", json.dumps({
        "revision": 0, "a": [0, 0], "b": [11, 1],
    })))
    assert "__error" not in joined and joined["layout"]["exactly_closed"]


def test_cancelled_solve_does_not_publish_or_drop_candidates():
    s = Session()
    s.attach("curve", 0, None)
    before = unchanged(s)
    def cancel(final=False):
        raise ValueError("cancelled")
    with pytest.raises(ValueError, match="cancelled"):
        s.solve_gap(None, None, 0, 1, cancel_check=cancel)
    assert unchanged(s) == before


def test_a_solve_makes_its_last_cancellation_check_just_before_it_commits():
    s = Session()
    s.attach("curve", 0, None)
    checks = []
    s.solve_gap(None, None, 0, 1, cancel_check=lambda final=False: checks.append(final))
    assert checks and checks[-1] is True and not any(checks[:-1])


def test_http_cancel_does_not_wait_for_session_lock(monkeypatch):
    s = Session()
    s.attach("curve", 0, None)
    before = unchanged(s)
    entered = threading.Event()
    def slow(*args, cancel_check=None, **kwargs):
        entered.set()
        # The test's event lets cancellation happen while the session lock is held.
        assert release.wait(3)
        cancel_check()
        raise AssertionError("cancellation was not delivered")
    release = threading.Event()
    monkeypatch.setattr(s, "solve_gap", slow)
    token = "0123456789abcdef0123456789abcdef"
    results = []
    with running_server(s) as server:
        worker = threading.Thread(target=lambda: results.append(post(server, "/api/solve", {
            "revision": s.revision, "operation_id": token,
        })))
        worker.start()
        try:
            assert entered.wait(3)
            code, result = post(server, "/api/cancel", {"operation_id": token})
            assert code == 200 and result["cancelled"]
        finally:
            release.set()
            worker.join(3)
        assert not worker.is_alive()
        assert results[0][0] == 409
        assert results[0][1]["code"] == "cancelled"
        assert post(server, "/api/cancel", {"operation_id": token})[1]["cancelled"] is False
    assert unchanged(s) == before


@pytest.mark.parametrize("token", [
    "0123456789abcde", "0" * 65, "0123456789abcdef!", "0123456789abcdéf", "0123 56789abcdef",
    12345678901234567, None,
])
def test_http_solve_and_cancel_need_a_valid_operation_id(token):
    # 16-64 ASCII letters, digits, '-' or '_': a random id names one solve.
    s = Session()
    s.attach("curve", 0, None)
    before = unchanged(s)
    with running_server(s) as server:
        for path in ("/api/solve", "/api/cancel"):
            code, result = post(server, path, {"revision": s.revision, "operation_id": token})
            assert code == 409 and "a valid operation_id is required" in result["error"], path
    assert unchanged(s) == before


def test_http_operation_id_names_one_running_solve(monkeypatch):
    s = Session()
    s.attach("curve", 0, None)
    entered, release = threading.Event(), threading.Event()

    def slow(*args, cancel_check=None, **kwargs):
        entered.set()
        assert release.wait(3)
        return {"found": 0, "aborted": False, "searched": 0}

    monkeypatch.setattr(s, "solve_gap", slow)
    token = "0123456789abcdef0123456789abcdef"
    results = []
    with running_server(s) as server:
        worker = threading.Thread(target=lambda: results.append(post(server, "/api/solve", {
            "revision": s.revision, "operation_id": token})))
        worker.start()
        try:
            assert entered.wait(3)
            # Refused at once, without waiting for the session the first one holds.
            code, result = post(server, "/api/solve", {
                "revision": s.revision, "operation_id": token})
        finally:
            release.set()
            worker.join(3)
    assert code == 409 and "operation_id is already active" in result["error"]
    assert results[0][0] == 200


def test_http_cancel_after_the_last_check_reports_that_it_was_not_active(monkeypatch):
    s = Session()
    s.attach("curve", 0, None)
    committed, answered = threading.Event(), threading.Event()

    def solve(*args, cancel_check=None, **kwargs):
        cancel_check(final=True)          # past this point the search commits
        committed.set()
        assert answered.wait(3)
        return {"found": 0, "aborted": False, "searched": 0}

    monkeypatch.setattr(s, "solve_gap", solve)
    token = "0123456789abcdef0123456789abcdef"
    results = []
    with running_server(s) as server:
        worker = threading.Thread(target=lambda: results.append(post(server, "/api/solve", {
            "revision": s.revision, "operation_id": token})))
        worker.start()
        assert committed.wait(3)
        status, reply = post(server, "/api/cancel", {"operation_id": token})
        answered.set()
        worker.join(3)
    assert status == 200 and reply == {"cancelled": False}
    assert results[0][0] == 200
