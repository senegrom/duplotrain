"""The opt-in drawing contract must not change exact candidates or legacy APIs."""

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


def test_compact_preview_reconstructs_legacy_drawing_and_preserves_all_metrics():
    session = candidate_session()
    before = unchanged(session)
    legacy = session.state()
    compact = session.state(preview_format=PREVIEW_FORMAT)
    full, slim = legacy["candidates"][0], compact["candidates"][0]
    assert {k: v for k, v in legacy.items() if k != "candidates"} == {
        k: v for k, v in compact.items() if k != "candidates"
    }
    assert {k: v for k, v in full.items() if k != "preview"} == {
        k: v for k, v in slim.items() if k != "preview"
    }
    preview = slim["preview"]
    assert preview["format"] == PREVIEW_FORMAT
    assert preview["base_revision"] == compact["revision"] == 4
    assert preview["base_count"] == 6
    reconstructed = drawings(compact["layout"]["placements"]) + preview["placements"]
    assert reconstructed == drawings(full["preview"]["placements"])
    assert all(set(p) == {"lines", "width"} for p in preview["placements"])
    assert unchanged(session) == before


@pytest.mark.parametrize("count", [0, 12])
def test_empty_base_and_zero_additions_keep_the_drawing_contract(count):
    session = candidate_session(count)
    preview = session.state(preview_format=PREVIEW_FORMAT)["candidates"][0]["preview"]
    assert preview["base_count"] == count
    assert len(preview["placements"]) == 12 - count


def test_changed_base_geometry_falls_back_to_full_drawing_without_sharing():
    session = candidate_session()
    solution = session.candidates[0]
    placements = list(solution.layout.placements)
    placements[0] = replace(placements[0], frame=Pose.make(x=100))
    session.candidates = [replace(solution, layout=Layout(tuple(placements)))]
    compact = session.state(preview_format=PREVIEW_FORMAT)["candidates"][0]["preview"]
    legacy = session.state()["candidates"][0]["preview"]
    assert compact["base_count"] == 0
    assert compact["placements"] == drawings(legacy["placements"])


def test_modifying_a_compact_response_cannot_change_exact_candidates_or_later_responses():
    session = candidate_session()
    before = unchanged(session)
    state = session.state(preview_format=PREVIEW_FORMAT)
    original = session.state(preview_format=PREVIEW_FORMAT)
    state["candidates"][0]["preview"]["placements"][0]["lines"][0][0][0] = 99999
    state["layout"]["placements"][0]["lines"][0][0][0] = 99999
    assert unchanged(session) == before
    assert session.state(preview_format=PREVIEW_FORMAT) == original


@pytest.mark.parametrize("invalid", ["duplotrain-preview/2", "", True, 1, [], {}])
def test_unknown_preview_contract_rejects_before_edit(invalid):
    session = candidate_session()
    before = unchanged(session)
    with pytest.raises(ValueError, match="preview format"):
        dispatch_session(session, "/api/clear", {"revision": 4, "preview_format": invalid})
    with pytest.raises(ValueError, match="preview format"):
        session.state(preview_format=invalid)
    assert unchanged(session) == before


@pytest.mark.parametrize("transport", ["direct", "worker", "http"])
def test_compact_negotiation_apply_export_undo_and_legacy_default(transport):
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
        state = request("/api/state", {"preview_format": PREVIEW_FORMAT})
        assert state["candidates"][0]["preview"]["format"] == PREVIEW_FORMAT
        assert "format" not in request("/api/state", {})["candidates"][0]["preview"]
        state = request("/api/apply", {
            "revision": state["revision"], "index": 0, "preview_format": PREVIEW_FORMAT,
        })
        assert state["layout"]["exactly_closed"] and not state["candidates"]
        exported = request("/api/export", {})
        assert exported["format"] == "duplotrain-layout/1"
        assert len(exported["placements"]) == 12
        state = request("/api/undo", {"revision": state["revision"]})
        assert state["snapshot"]["layout"] == baseline


def test_reported_bridge_payload_is_small_and_keeps_eight_audited_candidates():
    path = Path(__file__).parent / "fixtures/bridge-gap.json"
    base = layout_from_dict(json.loads(path.read_text()), default_catalog())
    session = Session(history=[base], unlimited=True)
    assert len(complete(session, max_pieces=26, max_results=8).solutions) == 8
    legacy, compact = session.state(), session.state(preview_format=PREVIEW_FORMAT)
    def size(state):
        return len(json.dumps(state, separators=(",", ":")).encode())

    assert size(compact) < size(legacy) * 0.30
    assert size(compact) < 135_000
    for candidate, full, slim in zip(
        session.candidates, legacy["candidates"], compact["candidates"], strict=True,
    ):
        assert len(candidate.layout) == 83 and candidate.layout.is_closed
        assert candidate.layout.placements[:59] == base.placements
        assert not candidate.layout.joint_issues()
        assert not _solution_overlaps(candidate.layout, 0, 120, 8)
        preview = slim["preview"]
        assert preview["base_count"] == 59 and len(preview["placements"]) == 24
        assert drawings(compact["layout"]["placements"]) + preview["placements"] == drawings(
            full["preview"]["placements"]
        )


@pytest.mark.parametrize("transport", ["direct", "worker"])
def test_search_job_previews_follow_the_negotiated_contract(transport):
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

    for negotiated in (False, True):
        extra = {"preview_format": PREVIEW_FORMAT} if negotiated else {}
        job = request("/api/search/start", {"max_results": 2, **extra})
        while job["status"] == "running":
            job = request("/api/search/tick", {"job_id": job["job_id"], **extra})
        published = request("/api/search/publish", {"job_id": job["job_id"], **extra})
        for candidates in (job["candidates"], published["search_job"]["candidates"],
                           published["candidates"]):
            assert candidates
            assert all(("format" in c["preview"]) == negotiated for c in candidates)


@pytest.mark.parametrize("page_only", [False, True])
def test_page_only_publication_builds_one_page_and_keeps_every_exact_candidate(monkeypatch,
                                                                               page_only):
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
        "job_id": job["job_id"], "revision": 0, "preview_format": PREVIEW_FORMAT,
        "page_only": page_only, "page": 1, "sort": "pieces",
    })
    # The requested page alone, where a full reply builds every candidate too.
    assert len(built) == (8 if page_only else 24)
    assert len(response["candidates"]) == (0 if page_only else 16)
    shown = response["search_job"]["candidates"]
    assert len(shown) == 8 and len(session.candidates) == 16
    assert session.snapshot() == before
    assert all(c["revision"] == c["preview"]["base_revision"] == session.revision
               for c in shown)
    # A later page's index, not its place on the screen, selects the exact layout.
    index = shown[-1]["index"]
    chosen = session.candidates[index].layout
    session.apply_candidate(index, session.revision)
    assert session.layout == chosen
    session.undo()
    assert session.snapshot() == before


@pytest.mark.parametrize("value", [None, 1, "true", []])
def test_a_bad_page_only_value_publishes_nothing(value):
    session = Session(history=[build_chain([(default_catalog()["curve"], 0, 1)] * 6)],
                      inventory={"curve": 12})
    job = dispatch_session(session, "/api/search/start", {"revision": 0})
    before = unchanged(session)
    with pytest.raises(ValueError, match="page_only"):
        dispatch_session(session, "/api/search/publish",
                         {"revision": 0, "job_id": job["job_id"], "page_only": value})
    assert unchanged(session) == before
    assert session._interactive_job.id == job["job_id"]


@pytest.mark.parametrize("transport", ["worker", "http"])
def test_page_only_publication_answers_alike_over_the_worker_and_http(transport):
    session = Session(history=[build_chain([(default_catalog()["curve"], 0, 1)] * 6)],
                      inventory={"curve": 12})
    adapter = load_adapter(session)
    with running_server(session) as server:
        def request(path, body):
            body = {"revision": session.revision, "preview_format": PREVIEW_FORMAT, **body}
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
        published = request("/api/search/publish", {"job_id": job["job_id"], "page_only": True})
        assert published["candidates"] == []
        assert published["search_job"]["candidates"] == request(
            "/api/state", {})["candidates"] == session.state(
            preview_format=PREVIEW_FORMAT)["candidates"]


@pytest.mark.parametrize("transport", ["worker", "http"])
def test_a_stale_request_answers_in_the_negotiated_preview_contract(transport):
    session = candidate_session()
    adapter = load_adapter(session)
    body = {"revision": 3, "preview_format": PREVIEW_FORMAT}
    with running_server(session) as server:
        if transport == "worker":
            reply = json.loads(adapter.dispatch("/api/clear", json.dumps(body)))
        else:
            status, reply = post(server, "/api/clear", body)
            assert status == 409
    assert reply["code"] == "stale_revision"
    assert reply["state"]["candidates"][0]["preview"]["format"] == PREVIEW_FORMAT
