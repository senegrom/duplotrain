"""Session snapshots: an edit that would cross a save limit changes nothing, a
restore is exact or leaves the session untouched, and responses are copies."""

import copy
import importlib.util
import json
from pathlib import Path

import pytest

import duplotrain.editor as editor
from duplotrain.catalog import ACCESSORIES, default_catalog
from duplotrain.geometry import Pose
from duplotrain.gui import Session, dispatch_session
from duplotrain.layout import Layout, Placement, layout_from_dict, layout_to_dict
from duplotrain.solver import Solution
from duplotrain.validation import MAX_ACCESSORIES, MAX_PLACEMENTS
from tests.editor_support import unchanged
from tests.test_editor_revisions import half_circle_session


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
    monkeypatch.setattr(editor, "MAX_SNAPSHOT_BYTES", len(json.dumps(session.snapshot()).encode()))
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


def stone_limit(session, _monkeypatch):
    """200 stones already on 201 straights: the 201st stone must be refused."""
    layout = straights(MAX_ACCESSORIES + 1)
    session._push(Layout(layout.placements, accessories=tuple(
        (i, "stone_stop") for i in range(MAX_ACCESSORIES))))
    return lambda: session.toggle_stone(MAX_ACCESSORIES, "stone_stop")


def placement_limit(session, _monkeypatch):
    session._push(straights(MAX_PLACEMENTS))
    return lambda: session.attach("straight", 0, (MAX_PLACEMENTS - 1, 1))


def save_budget(session, monkeypatch):
    session.attach("straight", 0, None)

    def rejected():
        size = len(json.dumps(session.snapshot()).encode())
        monkeypatch.setattr(editor, "MAX_SNAPSHOT_BYTES", size)
        session.set_inventory({"straight": 10000})
    return rejected


def unknown_piece(session, _monkeypatch):
    session.attach("straight", 0, None)
    return lambda: dispatch_session(session, "/api/attach", {
        "revision": session.revision, "piece": "warp", "entry": 0, "at": [0, 1]})


def bad_restore(session, _monkeypatch):
    snapshot = session.snapshot()
    snapshot["layout"]["links"] = [[0, 0, 0, 0]]
    return lambda: session.restore(snapshot)


@pytest.mark.parametrize("prepare", [stone_limit, placement_limit, save_budget, unknown_piece,
                                     bad_restore])
def test_a_rejected_edit_keeps_redo(monkeypatch, prepare):
    # docs/editor.md: "a no-op or rejected edit ... keeps [redo]". Limits are
    # checked on the complete proposed snapshot, before anything changes.
    session = Session(unlimited=True)
    rejected = prepare(session, monkeypatch)
    session.set_unlimited(False)
    session.undo()
    assert session.state()["can_redo"] and session.state()["redo_label"] == "sandbox change"
    before = unchanged(session)
    with pytest.raises(ValueError):
        rejected()
    assert unchanged(session) == before
    session.redo()
    assert not session.unlimited


def test_session_recovery_round_trips_geometry_inventory_and_stones():
    source = half_circle_session()
    source.set_inventory({"straight": 17, "stone_direction": 3})
    source.set_unlimited(True)
    checkpoint = json.loads(json.dumps(source.snapshot()))
    restored = Session()
    dispatch_session(restored, "/api/restore", {"data": checkpoint, "revision": 0})
    assert restored.snapshot() == checkpoint
    assert restored.layout == source.layout
    assert restored.candidates == []


def test_failed_restore_preserves_entire_session():
    session = half_circle_session()
    before = session.snapshot(), session.revision, list(session.candidates)
    bad = copy.deepcopy(session.snapshot())
    bad["inventory"]["curve"] = 123
    bad["layout"]["placements"][0]["frame"]["x"][0] = "1e999999999"
    with pytest.raises(ValueError):
        session.restore(bad)
    assert (session.snapshot(), session.revision, session.candidates) == before


def test_pyodide_adapter_uses_same_validation_and_recovery():
    path = Path(__file__).parents[1] / "webapp" / "adapter.py"
    spec = importlib.util.spec_from_file_location("recovery_adapter", path)
    adapter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(adapter)
    for body in ("not JSON", "[]", '{"data": null}'):
        assert "__error" in json.loads(adapter.dispatch("/api/restore", body))
    source = half_circle_session().snapshot()
    body = json.dumps({"data": source, "revision": 0})
    result = json.loads(adapter.dispatch("/api/restore", body))
    assert result["snapshot"] == source


def test_session_state_metadata_is_independent_between_responses_and_sessions():
    session = Session()
    before = copy.deepcopy(ACCESSORIES)
    state = session.state()
    state["stones"]["catalog"]["stone_horn"]["name"] = "changed"
    del state["stones"]["catalog"]["stone_direction"]
    assert ACCESSORIES == before
    assert session.state()["stones"]["catalog"] == before
    assert Session().state()["stones"]["catalog"] == before


def test_a_search_offers_exactly_the_candidates_the_editor_could_save(monkeypatch):
    import duplotrain.editor_search as editor_search
    from duplotrain.editor_search import SearchJob

    straight = default_catalog()["straight"]
    bar = straights(MAX_PLACEMENTS - 5)
    bar = Layout(bar.placements, {**{(i, 1): (i + 1, 0) for i in range(len(bar) - 1)},
                                  **{(i + 1, 0): (i, 1) for i in range(len(bar) - 1)}})
    session = Session(history=[bar], unlimited=True)

    def longer(count):
        layout, cursor = bar, (len(bar) - 1, 1)
        for _ in range(count):
            layout, index = layout.attach(straight, 0, cursor)
            cursor = (index, 1)
        return layout

    def saved(job, layout):  # the check an Apply would make
        try:
            Session._check_snapshot({**job.snapshot_metadata, "layout": layout_to_dict(layout)})
        except ValueError:
            return False
        return True

    size = len(json.dumps(session.snapshot(), ensure_ascii=True).encode())
    verdicts = []
    # The piece limit, then byte budgets that end among the added straights.
    for budget in (None, size + 600, size + 900):
        if budget is not None:
            monkeypatch.setattr(editor, "MAX_SNAPSHOT_BYTES", budget)
            monkeypatch.setattr(editor_search, "MAX_SNAPSHOT_BYTES", budget)
        job = SearchJob(session, {"grow": [len(bar) - 1, 1], "close": [0, 0]})
        try:
            for count in range(8):
                layout = longer(count)
                assert job._saveable(layout) == saved(job, layout), (budget, count)
                verdicts.append(saved(job, layout))
        finally:
            job.close()
    assert True in verdicts and False in verdicts

