"""Regression coverage for the non-solver review, through real host APIs too."""

import copy
import json
import threading

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.drive import DriveLimitError, drive
from duplotrain.editor import RevisionConflictError, Session, dispatch_session
from duplotrain.editor_tools import check_session, trace_train, validate_project
from duplotrain.geometry import Pose
from duplotrain.layout import Layout, Placement, build_chain
from duplotrain.sets import SETS
from tests.editor_support import load_adapter, post, running_server


def project(session, **prefs):
    return {"format": "duplotrain-project/1", "name": "Bridge", "session": session.snapshot(),
            "preferences": prefs}


def state_key(s):
    return (s.snapshot(), s.revision, list(s.history), list(s._history_state),
            list(s._future), list(s.candidates), s._candidate_revision)


@pytest.mark.parametrize("action", [
    lambda s: s.set_inventory({"straight": 17}),
    lambda s: s.set_inventory({"stone_stop": 17}),
    lambda s: s.set_unlimited(True),
    lambda s: s.add_set(next(iter(SETS))),
    lambda s: s.toggle_stone(0, "stone_stop"),
    lambda s: s.remove_piece(0),
    lambda s: s.clear(),
    lambda s: s.restore(Session(unlimited=True).snapshot()),
])
def test_every_session_edit_roundtrips_undo_and_redo(action):
    s = Session()
    s.attach("straight", 0, None)
    before, layout = s.snapshot(), s.layout
    action(s)
    after = s.snapshot()
    assert after != before
    revision = s.revision
    s.undo()
    assert s.snapshot() == before
    assert s.layout is layout
    assert s.revision == revision + 1
    assert s.state()["can_redo"]
    s.redo()
    assert s.snapshot() == after
    assert s.revision == revision + 2


def test_noop_or_rejected_edit_keeps_redo_but_new_edit_clears_it():
    s = Session()
    s.set_inventory({"straight": 17})
    s.undo()
    before = state_key(s)
    s.set_inventory({"straight": s.inventory["straight"]})
    s.set_unlimited(s.unlimited)
    with pytest.raises(ValueError):
        s.set_inventory({"straight": -1})
    assert state_key(s) == before
    s.attach("straight", 0, None)
    assert not s.state()["can_redo"]


def test_history_is_bounded_and_inventory_records_share_layout():
    s = Session()
    layout = s.layout
    for n in range(250):
        s.set_inventory({"straight": n})
    assert len(s.history) == len(s._history_state) == 200
    assert all(item is layout for item in s.history)
    for _ in range(199):
        s.undo()
    assert s.inventory["straight"] == 8
    for _ in range(199):
        s.redo()
    assert s.inventory["straight"] == 249
    assert not s._future


@pytest.mark.parametrize("route", ["/api/redo", "/api/project/open", "/api/check", "/api/drive"])
def test_new_api_calls_reject_stale_revision_without_changes(route):
    s = Session()
    before = state_key(s)
    with pytest.raises(RevisionConflictError):
        dispatch_session(s, route, {"revision": -1})
    assert state_key(s) == before


@pytest.mark.parametrize("host", ["direct", "adapter", "http"])
def test_project_restore_and_history_across_transports(host):
    target = Session(unlimited=True, inventory={"curve": 77}, stones={"stone_stop": 5})
    target.attach("curve", 0, None)
    data = project(target, view={"x": 14, "y": -30, "scale": 1.5},
                   search={"max_pieces": 52, "slop": 1, "reversing": True})
    s = Session()
    before = s.snapshot()

    def check(call):
        result = call("/api/project/open", {"data": data, "revision": s.revision})
        assert result["project"]["name"] == "Bridge"
        assert result["snapshot"] == target.snapshot()
        call("/api/undo", {"revision": s.revision})
        assert s.snapshot() == before
        call("/api/redo", {"revision": s.revision})
        assert s.snapshot() == target.snapshot()

    if host == "direct":
        check(lambda path, body: dispatch_session(s, path, body))
    elif host == "adapter":
        adapter = load_adapter(s)
        check(lambda path, body: json.loads(adapter.dispatch(path, json.dumps(body))))
    else:
        with running_server(s) as server:
            def request(path, body):
                code, result = post(server, path, body)
                assert code == 200, result
                return result
            check(request)


@pytest.mark.parametrize("prefs", [
    {"view": {"x": 0, "y": 0, "scale": float("nan")}},
    {"view": {"x": True, "y": 0, "scale": 1}},
    {"search": {"max_pieces": 2.5, "slop": 0, "reversing": False}},
    {"search": {"max_pieces": 26, "slop": -1, "reversing": False}},
    {"search": {"max_pieces": 26, "slop": 0, "reversing": "yes"}},
])
def test_invalid_project_preferences_cannot_partially_restore(prefs):
    s = Session()
    before = state_key(s)
    data = project(Session(unlimited=True), **prefs)
    with pytest.raises(ValueError):
        dispatch_session(s, "/api/project/open", {"data": data, "revision": s.revision})
    assert state_key(s) == before


def test_invalid_project_session_cannot_partially_restore():
    s = Session()
    s.set_unlimited(True)
    s.undo()
    before = state_key(s)
    data = project(Session(unlimited=True))
    data["session"]["layout"]["format"] = "bad"
    with pytest.raises(ValueError):
        dispatch_session(s, "/api/project/open", {"data": data, "revision": s.revision})
    assert state_key(s) == before
    with pytest.raises(ValueError):
        validate_project({**data, "name": " "})


def test_diagnostics_distinguish_closed_from_overlapping_and_missing():
    c = default_catalog()
    layout = build_chain([(c["curve"], 0, 1)] * 24).join((0, 0), (23, 1))
    s = Session(history=[layout], inventory={"curve": 2})
    before = state_key(s)
    report = check_session(s)
    assert report["connector_closed"]
    assert report["overlaps"]
    assert report["missing"][0]["missing"] == 22
    assert report["overlap_check_complete"]
    assert state_key(s) == before


@pytest.mark.parametrize("z,expected", [(0, True), (200, False)])
def test_diagnostics_use_existing_height_collision_rules(z, expected):
    c = default_catalog()
    layout = Layout((Placement(c["straight"], Pose.make()),
                     Placement(c["straight"], Pose.make(z=z))))
    report = check_session(Session(history=[layout]))
    assert bool(report["overlaps"]) == expected


def test_diagnostics_limit_is_not_a_clean_bill_of_health():
    straight = default_catalog()["straight"]
    s = Session(history=[Layout(tuple(Placement(straight, Pose.make()) for _ in range(30)))])
    report = check_session(s)
    assert not report["overlap_check_complete"]
    assert len(report["overlaps"]) == 200


def test_diagnostics_reports_stone_shortages_even_in_sandbox():
    s = Session(unlimited=True, stones={})
    s.attach("straight", 0, None)
    s.toggle_stone(0, "stone_stop")
    report = check_session(s)
    assert report["sandbox"]
    assert report["missing"][0]["piece"] == "stone_stop"
    assert report["missing"][0]["missing"] == 1


@pytest.mark.parametrize("start", [[-1, 0], [999, 0], [0, 999], [False, 0], None])
def test_train_rejects_invalid_start_without_mutation(start):
    s = Session()
    s.attach("straight", 0, None)
    before = state_key(s)
    with pytest.raises((ValueError, TypeError)):
        trace_train(s, start)
    assert state_key(s) == before


def test_trace_is_one_start_bounded_and_readonly():
    c = default_catalog()
    s = Session(history=[build_chain([(c["curve"], 0, 1)] * 12).join((0, 0), (11, 1))])
    before = state_key(s)
    report = trace_train(s, [0, 0])
    assert report["outcome"] == "endless"
    assert report["period"] == 12
    assert report["covers"]
    limited = trace_train(s, [0, 0], 3)
    assert limited["outcome"] == "limit" and not limited["complete"]
    assert state_key(s) == before
    with pytest.raises(DriveLimitError):
        drive(s.layout, max_steps=3)


@pytest.mark.parametrize("limit", [0, 10001, True, 1.5, "4"])
def test_train_budget_validation(limit):
    s = Session()
    s.attach("straight", 0, None)
    with pytest.raises(ValueError):
        trace_train(s, [0, 0], limit)


def test_cancelled_solve_does_not_publish_or_drop_candidates():
    s = Session()
    s.attach("curve", 0, None)
    before = state_key(s)
    def cancel():
        raise ValueError("cancelled")
    with pytest.raises(ValueError, match="cancelled"):
        s.solve_gap(None, None, 0, 1, cancel_check=cancel)
    assert state_key(s) == before


def test_http_cancel_does_not_wait_for_session_lock(monkeypatch):
    s = Session()
    s.attach("curve", 0, None)
    before = state_key(s)
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
    assert state_key(s) == before


def test_project_validation_does_not_modify_input():
    original = project(Session(), view={"x": 0, "y": 0, "scale": 1})
    before = copy.deepcopy(original)
    validate_project(original)
    assert original == before
