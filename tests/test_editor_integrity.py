"""Regression tests for stale edits, recoverable snapshots and exact mate indexing."""

import copy
import http.client
import importlib.util
import json
import threading
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from pathlib import Path

import pytest

import duplotrain.gui as gui
from duplotrain.catalog import default_catalog
from duplotrain.geometry import Pose
from duplotrain.gui import (
    MUTATING_ROUTES,
    RevisionConflictError,
    Session,
    dispatch_session,
    make_server,
)
from duplotrain.layout import Layout, Placement, layout_from_dict, layout_to_dict
from duplotrain.solver import Solution
from duplotrain.validation import MAX_ACCESSORIES, MAX_PLACEMENTS


def unchanged(session):
    return (session.snapshot(), list(session.history), session.revision,
            list(session.candidates), session._candidate_revision)


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


@pytest.fixture()
def local_session():
    session = Session()
    session.attach("straight", 0, None)
    session.attach("curve", 0, (0, 1))
    session.attach("switch", 0, (1, 1))
    server = make_server(session, 0)
    thread = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.01})
    thread.start()
    try:
        yield session, server
    finally:
        server.shutdown()
        server.server_close()
        thread.join()


def post(server, path, body):
    conn = http.client.HTTPConnection("127.0.0.1", server.server_port, timeout=3)
    try:
        conn.request("POST", path, json.dumps(body), {"Content-Type": "application/json"})
        response = conn.getresponse()
        return response.status, json.loads(response.read())
    finally:
        conn.close()


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


def test_old_clients_without_revision_fail_closed(local_session):
    session, server = local_session
    before = unchanged(session)
    status, result = post(server, "/api/clear", {})
    assert status == 409 and result["code"] == "stale_revision"
    assert unchanged(session) == before


def test_concurrent_same_revision_edits_have_only_one_winner(local_session):
    session, server = local_session
    revision = session.revision
    barrier = threading.Barrier(2)

    def remove():
        barrier.wait(timeout=3)
        return post(server, "/api/remove", {"placement": 0, "revision": revision})[0]

    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [pool.submit(remove) for _ in range(2)]
        assert sorted(f.result(timeout=5) for f in futures) == [200, 409]
    assert [p.piece.id for p in session.layout] == ["curve", "switch"]
    assert session.revision == revision + 1


def test_repeated_search_invalidates_the_previous_candidate_indices(monkeypatch):
    session = Session(unlimited=True)
    session.attach("straight", 0, None)
    monkeypatch.setattr(Session, "_arc_closures", lambda self, *args: [
        Solution(layout=self.layout, steps=(), gap=0, exact=True, open_stubs=2, signature=()),
    ])
    session.solve_gap(None, None, 0, 1)
    old_revision = session.revision
    session.solve_gap(None, None, 0, 1)
    assert session.revision > old_revision
    before = unchanged(session)
    with pytest.raises(ValueError, match="stale"):
        session.apply_candidate(0, old_revision)
    assert unchanged(session) == before


def test_pyodide_revision_conflicts_match_http():
    spec = importlib.util.spec_from_file_location(
        "integrity_adapter", Path(__file__).parents[1] / "webapp" / "adapter.py"
    )
    adapter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(adapter)
    result = json.loads(adapter.dispatch("/api/attach", json.dumps({
        "piece": "straight", "entry": 0, "revision": 0,
    })))
    assert result["revision"] == 1
    stale = json.loads(adapter.dispatch("/api/clear", '{"revision":0}'))
    assert stale["code"] == "stale_revision" and "__error" in stale
    assert stale["state"]["snapshot"] == result["snapshot"]


def straights(count):
    straight = default_catalog()["straight"]
    return Layout(tuple(Placement(straight, Pose.make(x=128 * i)) for i in range(count)))


def assert_round_trip(session):
    snapshot = json.loads(json.dumps(session.snapshot()))
    restored = Session()
    restored.restore(snapshot)
    assert restored.snapshot() == snapshot
    assert restored.layout == session.layout
    assert layout_from_dict(layout_to_dict(session.layout), session.catalog) == session.layout


def test_201st_stone_is_rejected_but_existing_200_stone_save_round_trips():
    layout = straights(MAX_ACCESSORIES + 1)
    session = Session(unlimited=True)
    session._push(Layout(layout.placements, accessories=tuple(
        (i, "stone_stop") for i in range(MAX_ACCESSORIES)
    )))
    assert_round_trip(session)
    before = unchanged(session)
    with pytest.raises(ValueError, match="accessories must be a list"):
        session.toggle_stone(MAX_ACCESSORIES, "stone_stop")
    assert unchanged(session) == before
    # Removing a stone at the limit still works, and makes room for another one.
    session.toggle_stone(0, "stone_stop")
    session.toggle_stone(MAX_ACCESSORIES, "stone_stop")
    assert_round_trip(session)


def test_placement_limit_cannot_be_crossed_by_editing_or_candidates():
    session = Session(unlimited=True)
    session._push(straights(MAX_PLACEMENTS))
    assert_round_trip(session)
    before = unchanged(session)
    with pytest.raises(ValueError, match="placements must be a list"):
        session.attach("straight", 0, (MAX_PLACEMENTS - 1, 1))
    assert unchanged(session) == before
    session.candidates = [Solution(
        layout=straights(MAX_PLACEMENTS + 1), steps=(), gap=0, exact=True,
        open_stubs=0, signature=(),
    )]
    session._candidate_revision = session.revision
    before = unchanged(session)
    with pytest.raises(ValueError, match="placements must be a list"):
        session.apply_candidate(0, session.revision)
    assert unchanged(session) == before


def test_attach_cannot_make_saved_coefficients_exceed_the_import_bound():
    straight = default_catalog()["straight"]
    session = Session(unlimited=True)
    session._push(Layout((Placement(straight, Pose.make(x=10**9)),)))
    before = unchanged(session)
    with pytest.raises(ValueError, match="magnitude"):
        session.attach("straight", 0, (0, 1))
    assert unchanged(session) == before
    assert_round_trip(session)


@pytest.mark.parametrize("action", ["attach", "inventory", "restore"])
def test_save_size_budget_is_checked_before_any_session_change(monkeypatch, action):
    session = Session()
    session.attach("straight", 0, None)
    before = unchanged(session)
    monkeypatch.setattr(gui, "MAX_SNAPSHOT_BYTES", len(json.dumps(session.snapshot()).encode()))
    with pytest.raises(ValueError, match="too large to save"):
        if action == "attach":
            session.attach("straight", 0, (0, 1))
        elif action == "inventory":
            session.set_inventory({"straight": 10000})
        else:
            snapshot = copy.deepcopy(session.snapshot())
            snapshot["inventory"]["straight"] = 10000
            session.restore(snapshot)
    assert unchanged(session) == before


def test_exact_pose_index_agrees_with_pairwise_reference():
    catalog = default_catalog()
    layout = Layout()
    # Includes irrational coordinates, all headings, ramps, sealed buffer ends,
    # duplicate positions, different heights and an almost-but-not-exact match.
    for i in range(24):
        piece = catalog[("straight", "curve", "ramp", "buffer")[i % 4]]
        frame = Pose.make(x=(i % 3) * 128, y=(i % 2) * 128, z=i % 2, heading=i)
        layout, _ = layout.with_piece(piece, frame)
    for x, z in [(128, 0), (128, 0), (128, 1), (128 + Fraction(1, 10**20), 0)]:
        layout, _ = layout.with_piece(catalog["straight"], Pose.make(x=x, z=z))
    layout, _ = layout.with_piece(catalog["straight"], Pose.make())
    ends = layout.connectable_ends()
    expected = [(a, b) for i, a in enumerate(ends) for b in ends[i + 1:]
                if layout.pose_of(a).connects_to(layout.pose_of(b))]
    assert expected
    assert layout.matable_pairs() == expected
    a, b = expected[0]
    linked = layout.join(a, b)
    assert all(a not in pair and b not in pair for pair in linked.matable_pairs())


def test_pose_index_computes_each_endpoint_once(monkeypatch):
    layout = straights(128)
    calls = []
    original = Layout.pose_of

    def counted(self, end):
        calls.append(end)
        return original(self, end)

    monkeypatch.setattr(Layout, "pose_of", counted)
    pairs = layout.matable_pairs()
    assert len(pairs) == 127
    assert calls == layout.connectable_ends()
    assert Session(history=[layout]).state()["matable"] == [
        [list(a), list(b)] for a, b in pairs
    ]
