"""Complete requested model spaces versus honestly bounded route analysis."""
import gc
import json
import weakref
from dataclasses import asdict, replace
from pathlib import Path

import pytest

from duplotrain import build_chain, default_catalog
from duplotrain.drive import classify, drive
from duplotrain.editor import RevisionConflictError, Session, dispatch_session
from duplotrain.editor_routes import RouteJob
from duplotrain.editor_search import MAX_JOB_SECONDS
from duplotrain.layout import layout_from_dict
from tests.editor_support import load_adapter, post, running_server


def finished(job):
    for _ in range(20000):
        if job.status != "running":
            return job.response()
        job.tick()
    pytest.fail("route analysis did not stop within the tested run budget")


@pytest.fixture
def completed():
    return layout_from_dict(json.loads((Path(__file__).parent / "fixtures/bridge-completed.json")
                                      .read_text()), default_catalog())


@pytest.mark.parametrize("scope,required", [("selected", 64), ("all", 11008)])
def test_actual_bridge_best_route_and_exhaustive_model_coverage(completed, scope, required):
    session = Session(history=[completed], unlimited=True)
    before = session.snapshot()
    job = RouteJob(session, {"scope": scope, "start": [0, 0], "max_runs": 20000})
    try:
        result = finished(job)
        assert result["complete"] and result["optimal"]
        assert result["runs"] == required and result["required_runs"] == str(required)
        assert result["best"]["visited"] == 57
        assert result["best"]["cycle_visited"] == 26
        assert result["outcomes"] == {"endless": required}
        assert result["classification"] == {
            "locally_looping": True, "looping": True,
            "completely_looping": False, "perfectly_looping": False,
        }
        best = result["best"]
        replay = drive(completed, start=tuple(best["start"]), switch_states=best["switch_states"])
        assert len(replay.visited) == 57 and replay.outcome == "endless"
        assert session.snapshot() == before and len(session.history) == 1
    finally:
        job.close()


@pytest.mark.parametrize("goal", ["visited", "cycle"])
def test_complete_simple_model_matches_existing_classifier(goal):
    c = default_catalog()
    circle = build_chain([(c["curve"], 0, 1)] * 12).join((0, 0), (11, 1))
    session = Session(history=[circle])
    job = RouteJob(session, {"goal": goal})
    result = finished(job)
    expected = asdict(classify(circle))
    assert result["classification"] == {k: expected[k] for k in result["classification"]}
    assert result["best"]["visited"] == result["best"]["cycle_visited"] == 12
    job.close()


def test_run_cap_is_partial_never_universal(completed):
    job = RouteJob(Session(history=[completed]), {"max_runs": 3})
    result = finished(job)
    assert result["runs"] == 3 and result["status"] == "limited"
    assert result["best"] and result["classification"] is None
    assert not result["complete"] and not result["optimal"]
    job.close()


def test_step_limited_runs_produce_no_terminal_or_coverage_claim(completed):
    job = RouteJob(Session(history=[completed]), {"max_runs": 2, "max_steps": 1})
    result = finished(job)
    assert result["step_limited_runs"] == 2
    assert result["best"] is None and result["counterexample"] is None
    assert result["classification"] is None and not result["complete"]
    job.close()


def test_runs_share_one_ten_million_step_allowance(completed, monkeypatch):
    # A run that reaches its step limit spends that whole limit. Once the job has
    # spent 10,000,000 steps it stops, limited, however many runs remain.
    import duplotrain.editor_routes as routes
    from duplotrain.drive import DriveLimitError

    def limited(layout, **kwargs):
        raise DriveLimitError(f"{kwargs['max_steps']} steps without a verdict")

    monkeypatch.setattr(routes, "drive", limited)
    job = RouteJob(Session(history=[completed]), {"max_runs": 100000, "max_steps": 10000})
    result = finished(job)
    assert result["required_runs"] == "11008" and result["max_runs"] == 100000
    assert result["runs"] == result["step_limited_runs"] == 1000
    assert result["steps"] == 10_000_000
    assert result["status"] == "limited" and not result["complete"]
    assert result["classification"] is None and result["best"] is None
    job.close()


def test_an_open_end_produces_a_loadable_counterexample():
    c = default_catalog()
    layout = build_chain([(c["straight"], 0, 1)] * 2)
    job = RouteJob(Session(history=[layout]), {})
    result = finished(job)
    assert result["complete"] and not result["classification"]["looping"]
    witness = result["counterexample"]
    assert drive(layout, start=tuple(witness["start"]),
                 switch_states=witness["switch_states"]).outcome == witness["outcome"]
    job.close()


def test_the_counterexample_breaks_the_weakest_property_that_fails():
    # A ring through a switch with an open spur: some runs loop over the whole
    # track, others leave by the spur. Not every run loops, so the counterexample
    # is one that does not, as drive.classify reports it.
    c = default_catalog()
    ring = build_chain([(c["switch"], 0, 1)] + [(c["curve"], 0, 1)] * 11)
    ends = ring.connectable_ends()
    layout = ring.join(*next((a, b) for a in ends for b in ends
                             if a < b and ring.pose_of(a).connects_to(ring.pose_of(b))))
    job = RouteJob(Session(history=[layout]), {})
    result = finished(job)
    assert not result["classification"]["looping"]
    witness = result["counterexample"]
    assert witness["outcome"] != "endless"
    assert (tuple(witness["start"]), witness["switch_states"],
            witness["outcome"]) == classify(layout).counterexample
    job.close()


@pytest.mark.parametrize("bad", [{"max_runs": 0}, {"max_runs": 100001}, {"max_runs": True},
    {"scope": "whatever"}, {"scope": "selected", "start": [10000, 0]},
    {"scope": "selected", "start": [0, 99]}, {"goal": "all guaranteed"},
    {"max_steps": 10001}, {"max_steps": 1.5}])
def test_invalid_analysis_cannot_replace_existing_search(completed, bad):
    s = Session(history=[completed])
    body = {"revision": s.revision}
    dispatch_session(s, "/api/routes/start", body)
    original, before = s._interactive_job, s.snapshot()
    with pytest.raises(ValueError):
        dispatch_session(s, "/api/routes/start", {**body, **bad})
    assert s._interactive_job is original and s.snapshot() == before
    original.close()


def test_pause_resume_is_incremental_and_content_change_discards(completed):
    s = Session(history=[completed])
    start = dispatch_session(s, "/api/routes/start", {"revision": s.revision})
    body = {"revision": s.revision, "job_id": start["job_id"]}
    one = dispatch_session(s, "/api/routes/tick", body)
    dispatch_session(s, "/api/routes/pause", body)
    assert dispatch_session(s, "/api/routes/tick", body)["runs"] == one["runs"]
    dispatch_session(s, "/api/routes/resume", body)
    two = dispatch_session(s, "/api/routes/tick", body)
    assert two["runs"] > one["runs"]
    old = s._interactive_job
    s.set_unlimited(True)
    assert s._interactive_job is None and old.status == "discarded"
    with pytest.raises(RevisionConflictError):
        dispatch_session(s, "/api/routes/tick", body)


def test_idle_route_analysis_expires_and_releases_iterator(completed):
    s = Session(history=[completed])
    job = RouteJob(s, {})
    s._interactive_job = job
    job.last_touch -= MAX_JOB_SECONDS + 1
    with pytest.raises(ValueError, match="expired"):
        dispatch_session(s, "/api/routes/tick", {"revision": s.revision, "job_id": job.id})
    assert s._interactive_job is None and job.status == "discarded"


def test_route_job_does_not_leak_after_discard_without_cyclic_gc(completed):
    enabled = gc.isenabled()
    gc.disable()
    try:
        s = Session(history=[completed])
        response = dispatch_session(s, "/api/routes/start", {"revision": s.revision})
        ref = weakref.ref(s._interactive_job)
        body = {"revision": s.revision, "job_id": response["job_id"]}
        dispatch_session(s, "/api/routes/tick", body)
        dispatch_session(s, "/api/routes/discard", body)
        assert ref() is None
    finally:
        if enabled:
            gc.enable()


@pytest.mark.parametrize("host", ["adapter", "http"])
def test_route_analysis_transports_do_not_change_layout_or_history(host):
    c = default_catalog()
    s = Session(history=[build_chain([(c["straight"], 0, 1)])])
    before = s.snapshot()
    def exercise(request):
        start = request("start", {"revision": s.revision})
        result = request("tick", {"revision": s.revision, "job_id": start["job_id"]})
        assert result["complete"] and result["classification"] is not None
        assert s.snapshot() == before and len(s.history) == 1
    if host == "adapter":
        adapter = load_adapter(s)
        exercise(lambda action, body: json.loads(adapter.dispatch(
            "/api/routes/" + action, json.dumps(body))))
    else:
        with running_server(s) as server:
            def request(action, body):
                code, result = post(server, "/api/routes/" + action, body)
                assert code == 200, result
                return result
            exercise(request)


def test_project_options_roundtrip_with_custom_catalogue():
    c = default_catalog()
    c["custom"] = replace(c["straight"], id="custom")
    s = Session(catalog=c)
    data = {"format": "duplotrain-project/1", "name": "Room", "session": s.snapshot(),
            "preferences": {"search": {"max_pieces": 26, "slop": 0, "reversing": False,
                                       "options": {"exclude": ["custom"], "room": [-1, -1, 1, 1]}}}}
    result = dispatch_session(s, "/api/project/open", {"revision": s.revision, "data": data})
    assert result["project"]["preferences"]["search"]["options"]["exclude"] == ["custom"]
