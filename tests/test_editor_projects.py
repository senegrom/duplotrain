"""Projects: opening one is validated in full before anything changes, on every
transport, and is one undoable change."""

import copy
import json

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.editor import Session, dispatch_session
from duplotrain.editor_tools import validate_project
from tests.editor_support import load_adapter, post, running_server, unchanged


def project(session, **prefs):
    return {"format": "duplotrain-project/1", "name": "Bridge", "session": session.snapshot(),
            "preferences": prefs}


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
    before = unchanged(s)
    data = project(Session(unlimited=True), **prefs)
    with pytest.raises(ValueError):
        dispatch_session(s, "/api/project/open", {"data": data, "revision": s.revision})
    assert unchanged(s) == before


def test_invalid_project_session_cannot_partially_restore():
    s = Session()
    s.set_unlimited(True)
    s.undo()
    before = unchanged(s)
    data = project(Session(unlimited=True))
    data["session"]["layout"]["format"] = "bad"
    with pytest.raises(ValueError):
        dispatch_session(s, "/api/project/open", {"data": data, "revision": s.revision})
    assert unchanged(s) == before
    with pytest.raises(ValueError):
        validate_project({**data, "name": " "}, default_catalog())


def test_project_validation_does_not_modify_input():
    original = project(Session(), view={"x": 0, "y": 0, "scale": 1})
    before = copy.deepcopy(original)
    validate_project(original, default_catalog())
    assert original == before
