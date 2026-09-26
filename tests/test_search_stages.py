"""Interactive searches follow the documented stage order under reversing and slop."""
import json
from pathlib import Path

import pytest

import duplotrain.editor_search as editor_search
from benchmarks.completion import cases
from duplotrain.catalog import default_catalog
from duplotrain.editor import PREVIEW_FORMAT, Session, dispatch_session
from duplotrain.editor_search import PairSearch, SearchJob, search_options
from duplotrain.layout import build_chain, layout_from_dict
from duplotrain.solver import _solution_overlaps
from tests.editor_support import complete, layout_key


@pytest.fixture(scope="module")
def gap():
    path = Path(__file__).parent / "fixtures/bridge-gap.json"
    return layout_from_dict(json.loads(path.read_text()), default_catalog())


def run(gap, body, nodes=None):
    job = SearchJob(Session(history=[gap], unlimited=True), dict(body))
    stages = []
    for _ in range(100_000):
        if job.status != "running" or (nodes is not None and job.nodes > nodes):
            break
        job.tick()
        if not stages or stages[-1] != job.stage:
            stages.append(job.stage)
    return job, stages


def test_allowing_reversing_loops_keeps_the_ordinary_and_bridge_stages(gap):
    # Reversing is ticked by default whenever a direction stone is owned. Only the
    # full-inventory fallback searches reversing closures.
    exact, _ = run(gap, {})
    reversing, stages = run(gap, {"reversing": True})
    try:
        assert "standard bridge" in stages and "full inventory" not in stages
        assert reversing.status == "results_ready"
        assert [s.layout for s in reversing.solutions] == [s.layout for s in exact.solutions]
    finally:
        exact.close()
        reversing.close()


def test_a_one_direction_stage_runs_before_the_next_stage_starts(gap):
    # A forced fit grows from one end: its plain stage (25,000 nodes) must run to
    # its own limit before the bridge stage starts, and is never resumed after it.
    job, stages = run(gap, {"slop": 1}, nodes=30_000)
    try:
        assert stages == ["templates", "plain track", "standard bridge"]
    finally:
        job.close()


@pytest.mark.parametrize("slop, ends", [(0, {(5, 1), (0, 0)}), (1, {(5, 1)})])
def test_an_exact_stage_alternates_doubling_turns_within_one_shared_cap(monkeypatch, slop,
                                                                        ends):
    catalog, turns = default_catalog(), []

    def never_settles(inventory, pieces, config, *, base, grow_from, close_onto, limits):
        while True:
            turns.append((grow_from, limits.max_nodes))
            yield {"kind": "node_limit", "nodes": limits.max_nodes, "depth": 1}

    monkeypatch.setattr(editor_search, "solve_steps", never_settles)
    pool = PairSearch(build_chain([(catalog["curve"], 0, 1)] * 6), catalog,
                      {"curve": 6, "straight": 4}, (5, 1), (0, 0), 26, 1, slop, False,
                      search_options(None, catalog))
    try:
        while pool.step()["kind"] not in ("limited", "exhausted"):
            pass
        # A forced fit grows from the chosen end only; an exact stage alternates.
        assert {grow for grow, _ in turns} == ends
        assert sum(c.nodes for c in pool.cursors) == 60_000  # one cap, not one per end
        if not slop:
            assert turns[:4] == [((5, 1), 1024), ((0, 0), 1024), ((5, 1), 2048),
                                 ((0, 0), 2048)]
    finally:
        pool.close()


def test_piece_depth_limit_is_not_a_proof_of_impossibility():
    catalog = default_catalog()
    layout = build_chain([(catalog["straight"], 0, 1)] * 34)
    for index in range(32, 0, -1):
        layout = layout.remove(index)
    session = Session(catalog=catalog, inventory={"straight": 34}, history=[layout])
    job = complete(session, (0, 1), (1, 0), max_results=3)
    assert not job.solutions
    assert job.status == "limited" and not job.complete
    assert max(c.depth for c in job.pool.cursors) == 26  # the search reached the bound
    deeper = complete(session, (0, 1), (1, 0), max_results=3, max_pieces=64)
    assert len(deeper.solutions) == 1
    assert deeper.status == "exhausted" and deeper.complete
    assert session.candidates[0].piece_count == 34


def test_search_harder_keeps_both_ends_of_an_exact_stage_taking_turns(monkeypatch):
    catalog, turns = default_catalog(), []

    def never_settles(inventory, pieces, config, *, base, grow_from, close_onto, limits):
        while True:
            turns.append(grow_from)
            yield {"kind": "node_limit", "nodes": limits.max_nodes, "depth": 1}

    monkeypatch.setattr(editor_search, "solve_steps", never_settles)
    pool = PairSearch(build_chain([(catalog["curve"], 0, 1)] * 6), catalog,
                      {"curve": 6, "straight": 4}, (5, 1), (0, 0), 26, 1, 0, False,
                      search_options(None, catalog))
    try:
        while pool.step()["kind"] not in ("limited", "exhausted"):
            pass
        before = len(turns)
        pool.harder()
        while pool.step()["kind"] not in ("limited", "exhausted"):
            pass
        # The doubled budget is spent by turns from both ends, not by one.
        assert set(turns[before:]) == {(5, 1), (0, 0)}
        assert sum(c.nodes for c in pool.cursors) == 120_000
    finally:
        pool.close()


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
