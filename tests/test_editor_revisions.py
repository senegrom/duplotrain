"""Stale edits and stale candidates: every edit, and every candidate applied, must
match the revision and the engine instance the client displayed."""

import json
import threading
from concurrent.futures import ThreadPoolExecutor

import pytest

from duplotrain.editor import MUTATING_ROUTES
from duplotrain.gui import RevisionConflictError, Session, dispatch_session
from tests.editor_support import complete, load_adapter, post, running_server, unchanged


def half_circle_session():
    session = Session(inventory={"curve": 12})
    for i in range(6):
        session.attach("curve", 0, None if i == 0 else (i - 1, 1))
    complete(session, max_results=3)
    assert session.candidates
    return session


@pytest.mark.parametrize("path", sorted(MUTATING_ROUTES))
@pytest.mark.parametrize("revision", [None, -1, 0, True, "1", 1.0])
def test_all_mutations_require_an_exact_current_revision(path, revision):
    session = Session()
    session.attach("straight", 0, None)
    before = unchanged(session)
    body = {} if revision is None else {"revision": revision}
    # Other fields are deliberately absent: revision validation must happen first.
    with pytest.raises(RevisionConflictError):
        dispatch_session(session, path, body)
    assert unchanged(session) == before


# The mutating routes are covered above; these two only read.
@pytest.mark.parametrize("route", ["/api/check", "/api/drive"])
def test_revision_checked_reports_reject_stale_revision_without_changes(route):
    s = Session()
    before = unchanged(s)
    with pytest.raises(RevisionConflictError):
        dispatch_session(s, route, {"revision": -1})
    assert unchanged(s) == before


@pytest.fixture()
def local_session():
    session = Session()
    session.attach("straight", 0, None)
    session.attach("curve", 0, (0, 1))
    session.attach("switch", 0, (1, 1))
    with running_server(session) as server:
        yield session, server


def test_two_tabs_cannot_delete_a_reindexed_piece(local_session):
    session, server = local_session
    old_revision = session.revision
    assert post(server, "/api/remove", {"placement": 0, "revision": old_revision})[0] == 200
    before = unchanged(session)
    status, result = post(server, "/api/remove", {"placement": 1, "revision": old_revision})
    assert status == 409
    assert result["code"] == "stale_revision"
    assert result["state"]["revision"] == session.revision
    assert [p["piece"] for p in result["state"]["layout"]["placements"]] == ["curve", "switch"]
    assert unchanged(session) == before
    # Only a fresh, explicit action can now remove the curve at its new index.
    assert post(server, "/api/remove", {"placement": 0, "revision": session.revision})[0] == 200
    assert [p.piece.id for p in session.layout] == ["switch"]


def test_restarted_engine_rejects_a_stale_tab_at_the_same_revision():
    # A restarted local server counts revisions from 0 again. A tab that saw
    # revision 2 of the previous engine must not edit revision 2 of the new one.
    old, new = Session(), Session()
    assert old.instance != new.instance
    new.attach("straight", 0, None)
    new.attach("curve", 0, (0, 1))
    stale = {"placement": 0, "revision": new.revision, "instance": old.instance}
    before = unchanged(new)
    with running_server(new) as server:
        status, result = post(server, "/api/remove", stale)
        assert status == 409 and result["code"] == "stale_revision"
        assert result["state"]["instance"] == new.instance
        assert unchanged(new) == before
        # Clients naming this engine, and older clients naming none, still edit.
        assert post(server, "/api/remove", {**stale, "instance": new.instance})[0] == 200
        assert post(server, "/api/remove", {"placement": 0, "revision": new.revision})[0] == 200
    assert not new.layout


def test_old_clients_without_revision_fail_closed(local_session):
    session, server = local_session
    before = unchanged(session)
    status, result = post(server, "/api/clear", {})
    assert status == 409 and result["code"] == "stale_revision"
    assert unchanged(session) == before


def test_concurrent_same_revision_edits_have_only_one_winner(local_session, monkeypatch):
    session, server = local_session
    revision = session.revision
    barrier = threading.Barrier(2)
    arrivals, both_arrived = [], threading.Event()
    remove_piece = Session.remove_piece

    def held_open(self, placement):
        # Keep the first edit open for a while. Were requests not serialised,
        # the second would pass the same revision check and arrive here too.
        arrivals.append(placement)
        if len(arrivals) == 2:
            both_arrived.set()
        both_arrived.wait(1.0)
        return remove_piece(self, placement)

    monkeypatch.setattr(Session, "remove_piece", held_open)

    def remove():
        barrier.wait(timeout=3)
        return post(server, "/api/remove", {"placement": 0, "revision": revision})[0]

    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [pool.submit(remove) for _ in range(2)]
        assert sorted(f.result(timeout=5) for f in futures) == [200, 409]
    assert arrivals == [0]  # the loser was refused before it reached the edit
    assert [p.piece.id for p in session.layout] == ["curve", "switch"]
    assert session.revision == revision + 1


def test_pyodide_revision_conflicts_match_http():
    adapter = load_adapter()
    result = json.loads(adapter.dispatch("/api/attach", json.dumps({
        "piece": "straight", "entry": 0, "revision": 0,
    })))
    assert result["revision"] == 1
    stale = json.loads(adapter.dispatch("/api/clear", '{"revision":0}'))
    assert stale["code"] == "stale_revision" and "__error" in stale
    assert stale["state"]["snapshot"] == result["snapshot"]


def test_repeated_search_invalidates_the_previous_candidate_indices():
    session = Session(unlimited=True)
    session.attach("straight", 0, None)
    complete(session, max_results=1)
    old_revision = session.revision
    complete(session, max_results=1)
    assert session.revision > old_revision
    before = unchanged(session)
    with pytest.raises(ValueError, match="stale"):
        session.apply_candidate(0, old_revision)
    assert unchanged(session) == before


@pytest.mark.parametrize("change", ["inventory", "sandbox", "set"])
def test_inventory_changes_invalidate_candidates(change):
    session = half_circle_session()
    revision = session.revision
    if change == "inventory":
        session.set_inventory({"curve": 6})
    elif change == "sandbox":
        session.set_unlimited(True)
    else:
        session.add_set("10882")
    assert not session.candidates
    assert session.revision > revision
    with pytest.raises(ValueError, match="stale"):
        session.apply_candidate(0, revision)


def test_old_candidate_revision_cannot_select_a_new_candidate():
    session = half_circle_session()
    old_revision = session.revision
    session.set_inventory({"curve": 13})
    complete(session, max_results=3)
    with pytest.raises(ValueError, match="stale"):
        session.apply_candidate(0, old_revision)


def test_candidate_application_rechecks_inventory_even_without_setter():
    session = half_circle_session()
    session.inventory["curve"] = 6
    with pytest.raises(ValueError, match="inventory"):
        session.apply_candidate(0)
    assert len(session.layout) == 6
