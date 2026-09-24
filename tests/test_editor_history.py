"""Undo, redo and clear: every edit is one undoable step, a no-op or rejected edit
keeps redo, and the bounded history undoes exactly the edit each label names."""

import json

import pytest

from duplotrain.editor import Session, dispatch_session
from duplotrain.sets import SETS
from tests.editor_support import load_adapter, post, running_server, unchanged
from tests.test_editor_revisions import half_circle_session


def content_state(session):
    return (session.snapshot(), session.revision, list(session.history),
            list(session._history_state), list(session._future), list(session.candidates))


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


def test_clear_is_undoable():
    session = half_circle_session()
    before = session.layout
    session.clear()
    assert len(session.layout) == 0
    assert session.state()["can_undo"]
    session.undo()
    assert session.layout == before


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


def test_noop_or_rejected_edit_keeps_redo_but_new_edit_clears_it():
    s = Session()
    s.set_inventory({"straight": 17})
    s.undo()
    before = unchanged(s)
    s.set_inventory({"straight": s.inventory["straight"]})
    s.set_unlimited(s.unlimited)
    with pytest.raises(ValueError):
        s.set_inventory({"straight": -1})
    assert unchanged(s) == before
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
    # The oldest kept edit is the base: undo never jumps past dropped edits.
    assert s.inventory["straight"] == 50 and not s.state()["can_undo"]
    for _ in range(199):
        s.redo()
    assert s.inventory["straight"] == 249
    assert not s._future


def test_the_bounded_history_undoes_exactly_the_edit_each_label_names():
    s = Session()
    s.restore(Session(unlimited=True).snapshot())       # an undoable project open
    for _ in range(199):
        s.attach("straight", 0, None if not s.layout.placements else s.layout.connectable_ends()[0])
    assert len(s.history) == 200
    while s.state()["can_undo"]:
        s.undo()
    # The oldest kept state is the opened project, not the engine's first empty one.
    assert s.unlimited and s.layout.placements == ()


def test_a_recovered_session_starts_a_new_history_but_opening_a_project_is_undoable():
    source = Session()
    source.attach("curve", 0, None)
    source.set_unlimited(True)
    engine = Session()
    dispatch_session(engine, "/api/restore", {"data": source.snapshot(), "revision": 0})
    assert engine.snapshot() == source.snapshot() and not engine.state()["can_undo"]
    project = {"format": "duplotrain-project/1", "name": "Loop", "session": Session().snapshot(),
               "preferences": {}}
    dispatch_session(engine, "/api/project/open", {"data": project, "revision": engine.revision})
    assert engine.state()["can_undo"]
    engine.undo()
    assert engine.snapshot() == source.snapshot()
