"""Regression tests for PR 18's finishing pass; no search semantics change."""

import json
from pathlib import Path

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.drive import DriveLimitError, drive
from duplotrain.editor import Session, dispatch_session
from duplotrain.editor_tools import trace_train
from duplotrain.layout import build_chain, layout_from_dict
from tests.editor_support import load_adapter, post, running_server


def content_state(session):
    return (session.snapshot(), session.revision, list(session.history),
            list(session._history_state), list(session._future), list(session.candidates))


@pytest.mark.parametrize("transport", ["direct", "adapter", "http"])
def test_empty_clear_preserves_redo_revision_and_history(transport):
    session = Session()
    session.attach("straight", 0, None)
    placed = session.snapshot()
    session.undo()
    before = content_state(session)
    body = {"revision": session.revision}
    if transport == "direct":
        result = dispatch_session(session, "/api/clear", body)
    elif transport == "adapter":
        result = json.loads(load_adapter(session).dispatch("/api/clear", json.dumps(body)))
    else:
        with running_server(session) as server:
            status, result = post(server, "/api/clear", body)
            assert status == 200
    assert result["can_redo"]
    assert content_state(session) == before
    session.redo()
    assert session.snapshot() == placed


def test_nonempty_clear_is_still_one_undoable_change():
    session = Session()
    session.attach("straight", 0, None)
    before = session.snapshot()
    session.clear()
    assert not len(session.layout)
    revision = session.revision
    session.clear()
    assert session.revision == revision
    session.undo()
    assert session.snapshot() == before


@pytest.mark.parametrize("piece,stone,at_port,expected_steps,reason,event_port", [
    ("straight", True, None, 1, "stop_stone", None),
    ("straight", True, 1, 1, "stop_stone", 1),
    ("straight", False, None, 2, "open_end", 1),
    ("buffer", False, None, 2, "buffer", 1),
])
def test_terminal_event_does_not_add_a_traversal(piece, stone, at_port, expected_steps,
                                               reason, event_port):
    c = default_catalog()
    layout = build_chain([(c["straight"], 0, 1)])
    layout, index = layout.attach(c[piece], 0, (0, 1))
    if stone:
        layout = layout.with_accessory(index, "stone_stop", at_port=at_port)
    session = Session(history=[layout])
    before = content_state(session)
    result = trace_train(session, [0, 0])
    assert len(result["steps"]) == expected_steps
    assert result["terminal"] == {"placement": 1, "entry": 0, "at_port": event_port,
                                  "reason": reason}
    assert result["cycle_start"] is None and result["period"] is None
    assert result["visited"] == [0, 1]
    assert result["drivable_count"] == (1 if piece == "buffer" else 2)
    assert result["visited_drivable"] == ([0] if piece == "buffer" else [0, 1])
    assert result["unvisited"] == []
    assert content_state(session) == before


def test_immediate_stop_has_terminal_but_zero_traversals():
    c = default_catalog()
    layout = build_chain([(c["straight"], 0, 1)]).with_accessory(0, "stone_stop")
    result = trace_train(Session(history=[layout]), [0, 1])
    assert result["steps"] == []
    assert result["terminal"]["entry"] == 1
    assert result["terminal"]["placement"] == 0
    assert result["visited_drivable"] == [0]


def test_endless_and_limited_runs_never_invent_a_terminal_event():
    c = default_catalog()
    layout = build_chain([(c["curve"], 0, 1)] * 12).join((0, 0), (11, 1))
    session = Session(history=[layout])
    before = content_state(session)
    complete = trace_train(session, [0, 0])
    assert complete["outcome"] == "endless" and complete["covers"]
    assert complete["terminal"] is None
    assert complete["cycle_start"] == 0 and complete["period"] == 12
    assert complete["cycle_pieces"] == list(range(12))
    # One start and a step budget: past it there is no verdict and no claim.
    limited = trace_train(session, [0, 0], 3)
    assert limited["outcome"] == "limit" and not limited["complete"]
    assert limited["terminal"] is None
    assert limited["unvisited"] is None
    assert limited["cycle_pieces"] == []
    assert content_state(session) == before
    with pytest.raises(DriveLimitError):
        drive(layout, max_steps=3)


@pytest.mark.parametrize("fixture,total", [("bridge-gap.json", 59), ("bridge-completed.json", 83)])
def test_reported_layout_coverage_is_separate_from_cycle(fixture, total):
    c = default_catalog()
    data = json.loads((Path(__file__).parent / "fixtures" / fixture).read_text())
    layout = layout_from_dict(data, c)
    session = Session(history=[layout])
    result = trace_train(session, [0, 0])
    assert result["outcome"] == "endless"
    assert result["drivable_count"] == result["total_pieces"] == total
    assert len(result["visited_drivable"]) == 41
    assert len(result["unvisited"]) == total - 41
    assert len(result["cycle_pieces"]) == 26
    assert result["period"] == 26 and result["cycle_start"] == 47
    assert len(result["steps"]) == 73
    assert set(result["cycle_pieces"]) <= set(result["visited"])
    assert set(result["unvisited"]).isdisjoint(result["visited"])
    assert result["terminal"] is None


@pytest.mark.parametrize("transport", ["direct", "adapter", "http"])
def test_explicit_initial_switches_reach_drive_model_without_mutating_layout(transport):
    s = Session()
    s.attach("switch", 0, None)
    before = content_state(s)
    choices = s.state()["train_switches"]
    assert choices[0]["placement"] == 0
    ports = [o["port"] for o in choices[0]["options"]]
    assert ports == [1, 2]
    body = {"revision": s.revision, "start": [0, 0], "switch_states": {"0": 2}}
    if transport == "direct":
        result = dispatch_session(s, "/api/drive", body)
    elif transport == "adapter":
        result = json.loads(load_adapter(s).dispatch("/api/drive", json.dumps(body)))
    else:
        with running_server(s) as server:
            status, result = post(server, "/api/drive", body)
            assert status == 200
    assert result["steps"] == [[0, 0, 2]]
    assert result["terminal"]["at_port"] == 2
    assert content_state(s) == before
    assert trace_train(s, [0, 0])["steps"] == [[0, 0, 1]]


@pytest.mark.parametrize("states", [[], True, "0", {"0": True}, {"0": 0}, {"0": 999},
                                     {"0": "2"}, {"0": 2.0}, {"1": 2}, {False: 1},
                                     {0.0: 1}, {"00": 1}, {"-1": 1}, {"٠": 1},
                                     {0: 1, "0": 2}, {"9" * 100: 2}])
def test_invalid_switch_choices_are_rejected_before_any_change(states):
    s = Session()
    s.attach("switch", 0, None)
    before = content_state(s)
    with pytest.raises(ValueError):
        trace_train(s, [0, 0], switch_states=states)
    assert content_state(s) == before


def test_explicit_defaults_preserve_existing_route_cycle_and_coverage():
    c = default_catalog()
    data = json.loads((Path(__file__).parent / "fixtures" / "bridge-completed.json").read_text())
    layout = layout_from_dict(data, c)
    s = Session(history=[layout])
    direct = drive(layout, start=(0, 0))
    trace = trace_train(s, [0, 0], switch_states={str(x["placement"]): x["default"]
                                              for x in s.state()["train_switches"]})
    assert trace["steps"] == [list(x) for x in direct.steps]
    assert trace["period"] == direct.period
    assert trace["visited"] == sorted(direct.visited)
    assert trace["final_switch_states"] == direct.final_switch_states
