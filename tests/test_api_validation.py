"""Malformed indices must never become edits in HTTP, Pyodide or direct dispatch."""

import json
from contextlib import ExitStack

import pytest

from duplotrain import ORIGIN, Layout, Placement, Pose, default_catalog
from duplotrain.gui import Session, dispatch_session
from duplotrain.solver import Solution
from tests.editor_support import load_adapter, post, running_server, unchanged


def session_with_candidates():
    catalog = default_catalog()
    straight = catalog["straight"]
    base = Layout((Placement(straight, ORIGIN), Placement(straight, Pose.make(x=128))))
    joined = base.join((0, 1), (1, 0))
    session = Session(catalog=catalog, inventory={"straight": 3, "curve": 2}, history=[base])
    session.revision = session._candidate_revision = 5
    candidate = Solution(joined, (), 0.0, True, 2, ("saved",))
    session.candidates = [candidate, candidate]
    return session


@pytest.fixture(params=["direct", "http", "pyodide"])
def endpoint(request):
    session = session_with_candidates()
    with ExitStack() as stack:
        server = stack.enter_context(running_server(session)) if request.param == "http" else None
        adapter = load_adapter(session) if request.param == "pyodide" else None

        def reject(path, body):
            before = unchanged(session)
            candidates = session.candidates
            body = {"revision": session.revision, **body}
            if request.param == "direct":
                with pytest.raises(ValueError):
                    dispatch_session(session, path, body)
            elif request.param == "pyodide":
                result = json.loads(adapter.dispatch(path, json.dumps(body)))
                assert "__error" in result and result.get("code") != "stale_revision"
            else:
                status, result = post(server, path, body)
                assert status == 409
                assert "error" in result and result.get("code") != "stale_revision"
            assert unchanged(session) == before
            assert session.candidates is candidates
            # A rejected request must not stale an already-published valid candidate.
            session.apply_candidate(0, session.revision)
            assert session.layout.links[(0, 1)] == (1, 0)

        yield session, reject


INTEGER_FIELDS = [
    ("/api/attach", "entry", {"piece": "curve", "at": [1, 1]}),
    ("/api/remove", "placement", {}),
    ("/api/stone", "placement", {"id": "stone_stop"}),
    ("/api/stone", "at_port", {"id": "stone_stop", "placement": 0}),
    ("/api/apply", "index", {}),
    ("/api/solve", "max_results", {"grow": [1, 1], "close": [0, 0], "max_pieces": 1}),
    ("/api/solve", "max_pieces", {"grow": [1, 1], "close": [0, 0], "max_results": 1}),
]


@pytest.mark.parametrize("path,field,body", INTEGER_FIELDS)
@pytest.mark.parametrize("value", [0.9, -0.9, 1.0, True, False, "0", -1, {}, []])
def test_indices_and_integer_limits_reject_coercion(endpoint, path, field, body, value):
    _, reject = endpoint
    reject(path, {**body, field: value})


END_FIELDS = [
    ("/api/attach", "at", {"piece": "curve", "entry": 0}),
    ("/api/join", "a", {"b": [1, 0]}),
    ("/api/join", "b", {"a": [0, 1]}),
    ("/api/solve", "grow", {"close": [0, 0], "max_pieces": 1}),
    ("/api/solve", "close", {"grow": [1, 1], "max_pieces": 1}),
]


@pytest.mark.parametrize("path,field,body", END_FIELDS)
@pytest.mark.parametrize("value", [
    [False, 1], [0, True], [0.0, 1], [0, 1.0], ["0", 1], [0, "1"],
    [-1, 1], [0, -1], [], [0], [0, 1, 2], "01", {"0": 0, "1": 1},
])
def test_endpoint_pairs_validate_each_index_and_shape(endpoint, path, field, body, value):
    _, reject = endpoint
    reject(path, {**body, field: value})


@pytest.mark.parametrize("field,value", [
    ("max_results", None), ("max_pieces", None),
    ("slop", True), ("slop", False), ("slop", "0"), ("slop", None),
    ("slop", -0.1), ("slop", float("inf")), ("slop", float("nan")),
    ("reversing", "false"), ("reversing", 0), ("reversing", 1), ("reversing", None),
])
def test_search_options_reject_wrong_types_without_losing_candidates(endpoint, field, value):
    _, reject = endpoint
    reject("/api/solve", {"grow": [1, 1], "close": [0, 0], "max_pieces": 1, field: value})


@pytest.mark.parametrize("field,value", [
    ("max_results", 0), ("max_results", 51),
    ("max_pieces", 0), ("max_pieces", 129),
])
def test_search_integer_bounds_remain_enforced(endpoint, field, value):
    _, reject = endpoint
    reject("/api/solve", {"grow": [1, 1], "close": [0, 0], "max_pieces": 1, field: value})


@pytest.mark.parametrize("path,body", [
    ("/api/attach", {"piece": "curve", "entry": 0, "at": [1, 1]}),
    ("/api/join", {"a": [0, 1], "b": [1, 0]}),
    ("/api/remove", {"placement": 0}),
    ("/api/stone", {"placement": 0, "id": "stone_stop", "at_port": 1}),
    ("/api/apply", {"index": 0}),
    ("/api/solve", {"grow": [1, 1], "close": [0, 0], "max_results": 1,
                    "max_pieces": 1, "slop": 0, "reversing": False}),
])
def test_correctly_typed_requests_still_succeed(path, body):
    session = session_with_candidates()
    before = session.revision
    result = dispatch_session(session, path, {"revision": before, **body})
    assert result["revision"] == session.revision == before + 1
