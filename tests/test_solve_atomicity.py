"""Rejected or interrupted editor searches must not consume a revision."""

import http.client
import importlib.util
import json
import threading
from pathlib import Path

import pytest

import duplotrain.gui as gui
from duplotrain import build_chain, default_catalog
from duplotrain.gui import Session, dispatch_session, make_server
from duplotrain.solver import Solution, SolveResult, SolveStats


def session_with_candidate():
    catalog = default_catalog()
    recipe = [(catalog["curve"], 0, 1)]
    base = build_chain(recipe * 11)
    closed = build_chain(recipe * 12).join((0, 0), (11, 1))
    session = Session(catalog=catalog, inventory={"curve": 12, "buffer": 1}, history=[base])
    session.revision = session._candidate_revision = 9
    session.candidates = [Solution(closed, (), 0.0, True, 0, ())]
    return session


def unchanged(session):
    return (session.snapshot(), list(session.history), session.revision,
            list(session.candidates), session._candidate_revision)


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
            config.progress(4096)
        return fail()

    monkeypatch.setattr(gui, "solve", search)
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
    monkeypatch.setattr(gui, "solve", lambda *args, **kwargs: SolveResult(
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


def test_http_error_does_not_make_the_next_explicit_join_stale():
    session = unjoined_circle_session()
    server = make_server(session, 0)
    thread = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.01})
    thread.start()

    def post(path, body):
        conn = http.client.HTTPConnection("127.0.0.1", server.server_port, timeout=3)
        try:
            conn.request("POST", path, json.dumps(body), {"Content-Type": "application/json"})
            response = conn.getresponse()
            return response.status, json.loads(response.read())
        finally:
            conn.close()

    try:
        before = unchanged(session)
        status, result = post("/api/solve", {"revision": 0, "reversing": True})
        assert status == 409 and "already mate" in result["error"]
        assert unchanged(session) == before
        status, result = post("/api/join", {"revision": 0, "a": [0, 0], "b": [11, 1]})
        assert status == 200 and result["layout"]["exactly_closed"]
    finally:
        server.shutdown()
        server.server_close()
        thread.join()


def test_pyodide_error_preserves_the_same_revision_contract():
    spec = importlib.util.spec_from_file_location(
        "atomic_adapter", Path(__file__).parents[1] / "webapp" / "adapter.py"
    )
    adapter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(adapter)
    adapter.session = unjoined_circle_session()
    before = unchanged(adapter.session)
    result = json.loads(adapter.dispatch("/api/solve", '{"revision":0,"reversing":true}'))
    assert "already mate" in result["__error"]
    assert unchanged(adapter.session) == before
    joined = json.loads(adapter.dispatch("/api/join", json.dumps({
        "revision": 0, "a": [0, 0], "b": [11, 1],
    })))
    assert "__error" not in joined and joined["layout"]["exactly_closed"]
