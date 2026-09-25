"""An interactive result quota can continue beyond a successful plain-track stage."""
import pytest

from benchmarks.completion import cases
from duplotrain import build_chain, default_catalog
from duplotrain.editor import PREVIEW_FORMAT, Session, dispatch_session
from duplotrain.editor_search import layout_key
from duplotrain.solver import _solution_overlaps


@pytest.mark.parametrize("slop", [0, 5])
def test_interactive_quota_preserves_first_stage_and_publishes_job_counters(slop):
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 6)
    if slop:
        case = next(c for c in cases(catalog) if c.name == "offset_circle_slop_5")
        base = case.base.join((2, 1), (3, 0), force=True)
    session = Session(history=[base])
    session.inventory.update(curve=12, straight=4)
    stock = session.remaining()
    before = session.snapshot()
    dispatch_session(session, "/api/search/start", {
        "revision": session.revision, "slop": slop, "reversing": True,
    })
    job = session._interactive_job
    try:
        for _ in range(1000):
            if job.status != "running":
                break
            job.tick()
        assert job.status == "results_ready"
        keys = [layout_key(s.layout) for s in job.solutions]
        assert len(keys) == len(set(keys)) == 8
        # The plain-track stage settles first with its three closures; the quota
        # then continues into the later stages instead of stopping there.
        plain = [not set(s.layout.piece_counts) - {"curve", "straight"} for s in job.solutions]
        assert plain == [True] * 3 + [False] * 5
        for sol in job.solutions:
            assert sol.layout.placements[:len(base)] == base.placements
            assert all(sol.layout.links[a] == b for a, b in base.links.items())
            assert not _solution_overlaps(sol.layout, 0, 120, 8)
            for pid, used in sol.layout.piece_counts.items():
                assert used - base.piece_counts.get(pid, 0) <= stock.get(pid, 0)
            issues = sol.layout.joint_issues()
            assert len(issues) == (2 if slop else 0)
            assert sum(j["gap_mm"] for j in issues) == pytest.approx(2 * slop)
        published = dispatch_session(session, "/api/search/publish", {
            "revision": session.revision, "job_id": job.id, "preview_format": PREVIEW_FORMAT,
        })
        # Plain track (75 nodes), then the ordinary bridge stage, which reversing
        # does not skip (102), then the full inventory (20).
        assert published["search_job"]["searched"] == job.nodes == 197
        assert published["search_job"]["found"] == len(published["candidates"]) == 8
        assert published["snapshot"] == before
        assert len(session.history) == 1
        assert all(c["revision"] == published["revision"] for c in published["candidates"])
    finally:
        job.close()
