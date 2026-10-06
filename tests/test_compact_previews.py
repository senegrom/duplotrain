"""Compact candidate previews must not change exact candidates or their metrics."""

import json
from dataclasses import replace
from pathlib import Path

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.editor import PREVIEW_FORMAT, Session, dispatch_session
from duplotrain.geometry import Pose
from duplotrain.layout import Layout, build_chain, layout_from_dict, layout_to_dict
from duplotrain.solver import Solution, _solution_overlaps
from tests.editor_support import complete, load_adapter, post, running_server, unchanged


def candidate_session(count=6):
    catalog = default_catalog()
    circle = build_chain([(catalog["curve"], 0, 1)] * 12).join((0, 0), (11, 1))
    base = build_chain([(catalog["curve"], 0, 1)] * count)
    session = Session(history=[base], inventory={"curve": 12})
    session.revision = session._candidate_revision = 4
    session.candidates = [Solution(circle, (), 0, True, 0, ())]
    return session


def drawings(placements):
    return [{"lines": p["lines"], "width": p["width"]} for p in placements]


def full_drawing(layout):
    """Every placement's drawing: what a preview sharing no base would carry."""
    return drawings(Session._drawing_json(p) for p in layout)


def test_compact_preview_reconstructs_the_candidate_drawing_and_keeps_its_metrics():
    session = candidate_session()
    before = unchanged(session)
    state = session.state()
    candidate = state["candidates"][0]
    preview = candidate["preview"]
    assert preview["format"] == PREVIEW_FORMAT
    assert preview["base_revision"] == state["revision"] == 4
    assert preview["base_count"] == 6
    circle = session.candidates[0].layout
    reconstructed = drawings(state["layout"]["placements"]) + preview["placements"]
    assert reconstructed == full_drawing(circle)
    assert all(set(p) == {"lines", "width"} for p in preview["placements"])
    width, height = circle.size()
    assert candidate["size_cm"] == [round(width / 10, 1), round(height / 10, 1)]
    assert candidate["added"] == {"curve": 6} and candidate["exact"]
    assert unchanged(session) == before


@pytest.mark.parametrize("count", [0, 12])
def test_empty_base_and_zero_additions_keep_the_drawing_contract(count):
    session = candidate_session(count)
    preview = session.state()["candidates"][0]["preview"]
    assert preview["base_count"] == count
    assert len(preview["placements"]) == 12 - count


def test_changed_base_geometry_falls_back_to_full_drawing_without_sharing():
    session = candidate_session()
    solution = session.candidates[0]
    placements = list(solution.layout.placements)
    placements[0] = replace(placements[0], frame=Pose.make(x=100))
    session.candidates = [replace(solution, layout=Layout(tuple(placements)))]
    compact = session.state()["candidates"][0]["preview"]
    assert compact["base_count"] == 0
    assert compact["placements"] == full_drawing(session.candidates[0].layout)


def test_modifying_a_compact_response_cannot_change_exact_candidates_or_later_responses():
    session = candidate_session()
    before = unchanged(session)
    state = session.state()
    original = session.state()
    state["candidates"][0]["preview"]["placements"][0]["lines"][0][0][0] = 99999
    state["layout"]["placements"][0]["lines"][0][0][0] = 99999
    assert unchanged(session) == before
    assert session.state() == original


@pytest.mark.parametrize("transport", ["direct", "worker", "http"])
def test_compact_previews_apply_export_and_undo_over_every_transport(transport):
    session = candidate_session()
    adapter = load_adapter(session)
    with running_server(session) as server:
        def request(path, body):
            if transport == "direct":
                return dispatch_session(session, path, body)
            if transport == "worker":
                result = json.loads(adapter.dispatch(path, json.dumps(body)))
                assert "__error" not in result
                return result
            status, result = post(server, path, body)
            assert status == 200
            return result

        baseline = layout_to_dict(session.layout)
        state = request("/api/state", {})
        assert state["candidates"][0]["preview"]["format"] == PREVIEW_FORMAT
        state = request("/api/apply", {"revision": state["revision"], "index": 0})
        assert state["layout"]["exactly_closed"] and not state["candidates"]
        exported = state["snapshot"]["layout"]
        assert exported["format"] == "duplotrain-layout/1"
        assert len(exported["placements"]) == 12
        state = request("/api/undo", {"revision": state["revision"]})
        assert state["snapshot"]["layout"] == baseline


def test_reported_bridge_payload_is_small_and_keeps_eight_audited_candidates():
    path = Path(__file__).parent / "fixtures/bridge-gap.json"
    base = layout_from_dict(json.loads(path.read_text()), default_catalog())
    session = Session(history=[base], unlimited=True)
    assert len(complete(session, max_pieces=26, max_results=8).solutions) == 8
    state = session.state()
    assert len(json.dumps(state, separators=(",", ":")).encode()) < 135_000
    for candidate, slim in zip(session.candidates, state["candidates"], strict=True):
        assert len(candidate.layout) == 83 and candidate.layout.is_closed
        assert candidate.layout.placements[:59] == base.placements
        assert not candidate.layout.joint_issues()
        assert not _solution_overlaps(candidate.layout, 0, 120, 8)
        preview = slim["preview"]
        assert preview["base_count"] == 59 and len(preview["placements"]) == 24
        assert drawings(state["layout"]["placements"]) + preview["placements"] == full_drawing(
            candidate.layout
        )


@pytest.mark.parametrize("transport", ["direct", "worker"])
def test_search_job_previews_are_compact(transport):
    session = Session(history=[build_chain([(default_catalog()["curve"], 0, 1)] * 6)],
                      inventory={"curve": 12})
    adapter = load_adapter(session)

    def request(path, body):
        body = {"revision": session.revision, **body}
        if transport == "direct":
            return dispatch_session(session, path, body)
        result = json.loads(adapter.dispatch(path, json.dumps(body)))
        assert "__error" not in result
        return result

    job = request("/api/search/start", {"max_results": 2})
    while job["status"] == "running":
        job = request("/api/search/tick", {"job_id": job["job_id"]})
    published = request("/api/search/publish", {"job_id": job["job_id"]})
    for candidates in (job["candidates"], published["search_job"]["candidates"],
                       request("/api/state", {})["candidates"]):
        assert candidates
        assert all(c["preview"]["format"] == PREVIEW_FORMAT for c in candidates)


def test_publication_builds_one_page_and_keeps_every_exact_candidate(monkeypatch):
    path = Path(__file__).parent / "fixtures/bridge-gap.json"
    base = layout_from_dict(json.loads(path.read_text()), default_catalog())
    session = Session(history=[base], unlimited=True)
    before = session.snapshot()
    job = dispatch_session(session, "/api/search/start", {"revision": 0, "max_results": 16})
    while job["status"] == "running":
        job = dispatch_session(session, "/api/search/tick",
                               {"revision": 0, "job_id": job["job_id"]})
    built, build = [], session._candidate_json

    def record(index, *args, **kwargs):
        built.append(index)
        return build(index, *args, **kwargs)

    monkeypatch.setattr(session, "_candidate_json", record)
    response = dispatch_session(session, "/api/search/publish", {
        "job_id": job["job_id"], "revision": 0, "page": 1, "sort": "pieces",
    })
    # The requested page alone: the state leaves the suggestions out.
    assert len(built) == 8 and response["candidates"] == []
    shown = response["search_job"]["candidates"]
    assert len(shown) == 8 and len(session.candidates) == 16
    assert session.snapshot() == before
    assert all(c["revision"] == c["preview"]["base_revision"] == session.revision
               for c in shown)
    # A later page's index, not its place on the screen, selects the exact layout.
    index = shown[-1]["index"]
    chosen = session.candidates[index].layout
    session.apply_candidate(index)
    assert session.layout == chosen
    session.undo()
    assert session.snapshot() == before


@pytest.mark.parametrize("transport", ["worker", "http"])
def test_publication_answers_alike_over_the_worker_and_http(transport):
    session = Session(history=[build_chain([(default_catalog()["curve"], 0, 1)] * 6)],
                      inventory={"curve": 12})
    adapter = load_adapter(session)
    with running_server(session) as server:
        def request(path, body):
            body = {"revision": session.revision, **body}
            if transport == "worker":
                reply = json.loads(adapter.dispatch(path, json.dumps(body)))
                assert "__error" not in reply
                return reply
            status, reply = post(server, path, body)
            assert status == 200
            return reply

        job = request("/api/search/start", {"max_results": 2})
        while job["status"] == "running":
            job = request("/api/search/tick", {"job_id": job["job_id"]})
        published = request("/api/search/publish", {"job_id": job["job_id"]})
        assert published["candidates"] == []
        assert published["search_job"]["candidates"] == request(
            "/api/state", {})["candidates"] == session.state()["candidates"]


@pytest.mark.parametrize("transport", ["worker", "http"])
def test_a_stale_request_answers_with_compact_previews(transport):
    session = candidate_session()
    adapter = load_adapter(session)
    body = {"revision": 3}
    with running_server(session) as server:
        if transport == "worker":
            reply = json.loads(adapter.dispatch("/api/clear", json.dumps(body)))
        else:
            status, reply = post(server, "/api/clear", body)
            assert status == 409
    assert reply["code"] == "stale_revision"
    assert reply["state"]["candidates"][0]["preview"]["format"] == PREVIEW_FORMAT
