"""A selected stone is identified by type AND position, on every API transport."""

import http.client
import importlib.util
import json
import threading
from pathlib import Path

import pytest

from duplotrain import build_chain, default_catalog, layout_from_dict, layout_to_dict
from duplotrain.gui import Session, dispatch_session, make_server


def positioned_session():
    catalog = default_catalog()
    layout = build_chain([(catalog["straight"], 0, 1)])
    for position in (None, 0, 1):
        layout = layout.with_accessory(0, "stone_lights", at_port=position)
    return Session(catalog=catalog, stones={"stone_lights": 3}, history=[layout])


def request(session, position, **extra):
    return {"revision": session.revision, "placement": 0, "id": "stone_lights",
            "at_port": position, "remove": True, **extra}


@pytest.mark.parametrize("position", [None, 0, 1])
def test_remove_exact_position_and_undo_preserve_other_markers(position):
    session = positioned_session()
    before = session.layout
    state = dispatch_session(session, "/api/stone", request(session, position))
    assert state["stones"]["remaining"]["stone_lights"] == 1
    assert session.layout.stone_entries_on(0) == [
        ("stone_lights", p) for p in (None, 0, 1) if p != position
    ]
    assert layout_from_dict(layout_to_dict(session.layout), session.catalog) == session.layout
    session.undo()
    assert session.layout == before and session.stones_remaining()["stone_lights"] == 0


def test_library_omitted_position_keeps_legacy_last_of_colour_removal():
    layout = positioned_session().layout
    removed = layout.without_accessory(0, "stone_lights")
    assert removed.stone_entries_on(0) == [("stone_lights", None), ("stone_lights", 0)]
    assert layout.without_accessory(0, "stone_lights", at_port=None).stone_entries_on(0) == [
        ("stone_lights", 0), ("stone_lights", 1),
    ]


def test_duplicate_markers_at_one_position_remove_only_one_copy():
    layout = positioned_session().layout.with_accessory(0, "stone_lights", at_port=0)
    removed = layout.without_accessory(0, "stone_lights", at_port=0)
    assert removed == positioned_session().layout


def test_toggling_another_position_does_not_remove_same_colour_elsewhere():
    session = positioned_session()
    session.toggle_stone(0, "stone_lights", at_port=1)
    assert ("stone_lights", 0) in session.layout.stone_entries_on(0)
    session.toggle_stone(0, "stone_lights", at_port=1)
    assert len(session.layout.stone_entries_on(0)) == 3


@pytest.mark.parametrize("position", [True, False, 0.5, "0", -1, 2, {}, []])
def test_invalid_position_does_not_mutate_or_remove_a_different_stone(position):
    session = positioned_session()
    before = session.snapshot(), session.revision
    with pytest.raises(ValueError, match="position"):
        dispatch_session(session, "/api/stone", request(session, position))
    assert (session.snapshot(), session.revision) == before


@pytest.mark.parametrize("remove", [1, 0, "true", None])
def test_remove_mode_must_be_boolean(remove):
    session = positioned_session()
    before = session.snapshot(), session.revision
    with pytest.raises(ValueError, match="boolean"):
        dispatch_session(session, "/api/stone", request(session, 0, remove=remove))
    assert (session.snapshot(), session.revision) == before


def test_explicit_removal_of_missing_marker_never_adds_it():
    session = positioned_session()
    session.toggle_stone(0, "stone_lights", at_port=0)
    before = session.snapshot(), session.revision
    with pytest.raises(ValueError, match="no such stone"):
        dispatch_session(session, "/api/stone", request(session, 0))
    assert (session.snapshot(), session.revision) == before


@pytest.mark.parametrize("position", [None, 0, 1])
def test_http_removal_preserves_selected_position(position):
    session = positioned_session()
    server = make_server(session, 0)
    thread = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.01})
    thread.start()
    conn = http.client.HTTPConnection("127.0.0.1", server.server_port, timeout=3)
    try:
        conn.request("POST", "/api/stone", json.dumps(request(session, position)),
                     {"Content-Type": "application/json"})
        response = conn.getresponse()
        state = json.loads(response.read())
        assert response.status == 200
        assert state["layout"]["placements"][0]["stone_marks"] == [
            {"id": "stone_lights", "at": p} for p in (None, 0, 1) if p != position
        ]
    finally:
        conn.close()
        server.shutdown()
        server.server_close()
        thread.join()


@pytest.mark.parametrize("position", [None, 0, 1])
def test_pyodide_adapter_preserves_selected_position(position):
    spec = importlib.util.spec_from_file_location(
        "position_adapter", Path(__file__).parents[1] / "webapp" / "adapter.py"
    )
    adapter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(adapter)
    adapter.session = positioned_session()
    body = json.dumps(request(adapter.session, position))
    state = json.loads(adapter.dispatch("/api/stone", body))
    assert "__error" not in state
    assert state["layout"]["placements"][0]["stone_marks"] == [
        {"id": "stone_lights", "at": p} for p in (None, 0, 1) if p != position
    ]
