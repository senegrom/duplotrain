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
        assert [stage for stage in stages if stage != "templates"] == [
            "plain track", "standard bridge"]
    finally:
        job.close()


@pytest.mark.parametrize("floor", [0, -76.8, 57.6])
def test_the_bridge_stage_spans_a_gap_on_the_floor_at_any_height(floor):
    # A layout loaded from a loop that began up on a crest stands lower than zero:
    # its floor gap still gets the standard bridge. A gap up on bricks does not.
    from fractions import Fraction

    from duplotrain.exact import Alg
    from duplotrain.geometry import Pose

    catalog = default_catalog()
    z = Alg(Fraction(floor).limit_denominator(5))
    base = build_chain([(catalog["curve"], 0, 1)] * 6, start=Pose(Alg(0), Alg(0), z, 0))
    if floor > 0:  # the floor lies under a ramp standing beside the gap
        base, _ = base.with_piece(catalog["ramp"], Pose.make(x=-2000))
    stock = {"curve": 12, "straight": 8, "ramp": 2, "span": 2}
    pool = PairSearch(base, catalog, stock, (5, 1), (0, 0), 26, 1, 0, False,
                      search_options(None, catalog))
    try:
        assert ("standard bridge" in {c.stage for c in pool.cursors}) == (floor <= 0)
    finally:
        pool.close()


@pytest.mark.parametrize("slop, ends", [(0, {(5, 1), (0, 0)}), (1, {(5, 1)})])
def test_an_exact_stage_alternates_doubling_turns_within_one_shared_cap(monkeypatch, slop,
                                                                        ends):
    catalog, turns = default_catalog(), []

    def never_settles(inventory, pieces, config, *, base, grow_from, close_onto, limits):
        while True:
            turns.append((grow_from, limits.max_nodes))
            yield {"kind": "node_limit", "nodes": limits.max_nodes}

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
            # Search harder: both ends spend the doubled budget in turns, not one.
            before = len(turns)
            pool.harder()
            while pool.step()["kind"] not in ("limited", "exhausted"):
                pass
            assert {grow for grow, _ in turns[before:]} == {(5, 1), (0, 0)}
            assert sum(c.nodes for c in pool.cursors) == 120_000
    finally:
        pool.close()


def test_the_last_direction_of_a_stage_runs_before_the_next_stage_starts(monkeypatch):
    # One end of the plain stage is cut at once: the other end spends the stage's
    # whole budget, as a one-direction stage does, before the full inventory runs.
    catalog, turns = default_catalog(), []

    def one_end_cut(inventory, pieces, config, *, base, grow_from, close_onto, limits):
        stage = "plain" if set(inventory) <= {"curve", "straight"} else "full"
        while True:
            turns.append(stage)
            if stage == "plain" and grow_from == (5, 1):
                yield {"kind": "walk_limit", "nodes": 10}
            yield {"kind": "node_limit", "nodes": limits.max_nodes}

    monkeypatch.setattr(editor_search, "solve_steps", one_end_cut)
    pool = PairSearch(build_chain([(catalog["curve"], 0, 1)] * 6), catalog,
                      {"curve": 6, "straight": 4, "switch": 1}, (5, 1), (0, 0), 26, 1, 0,
                      False, search_options(None, catalog))
    try:
        while pool.step()["kind"] not in ("limited", "exhausted"):
            pass
        first_full = turns.index("full")
        assert "plain" not in turns[first_full:]
        assert sum(c.nodes for c in pool.cursors if c.stage == "plain track") == 25_000
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
    deeper = complete(session, (0, 1), (1, 0), max_results=3, max_pieces=64)
    assert len(deeper.solutions) == 1
    assert deeper.status == "exhausted" and deeper.complete
    assert session.candidates[0].piece_count == 34


def test_a_reversing_search_names_its_first_stage_from_the_start(gap):
    # A reversing search runs no arc templates: its first stage names it at once.
    job = SearchJob(Session(history=[gap], unlimited=True), {"reversing": True})
    try:
        assert job.stage == job.pool.cursors[0].stage != "templates"
    finally:
        job.close()


def test_the_arc_templates_build_their_session_when_they_first_run():
    # Setting a search up builds nothing it may never use: the templates' session
    # comes with the first step, which asks for the first template.
    catalog = default_catalog()
    pool = PairSearch(build_chain([(catalog["curve"], 0, 1)] * 6), catalog, {"curve": 6},
                      (5, 1), (0, 0), 26, 1, 0, False, search_options(None, catalog))
    try:
        assert pool.arc_session is None
        assert pool.step()["stage"] == "templates"
        assert pool.arc_session is not None
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


def test_the_full_inventory_running_out_of_search_settles_every_stage(monkeypatch):
    # Earlier stages search subsets of its stock and moves: once it has run out of
    # search, a plain stage stopped at its cap has nothing left to find either.
    catalog = default_catalog()

    def plain_capped(inventory, pieces, config, *, base, grow_from, close_onto, limits):
        if set(inventory) <= {"curve", "straight"}:
            while True:
                yield {"kind": "node_limit", "nodes": limits.max_nodes}
        yield {"kind": "progress", "nodes": 5}

    monkeypatch.setattr(editor_search, "solve_steps", plain_capped)
    pool = PairSearch(build_chain([(catalog["curve"], 0, 1)] * 6), catalog,
                      {"curve": 6, "straight": 4, "switch": 1}, (5, 1), (0, 0), 26, 1, 0,
                      False, search_options(None, catalog))
    try:
        while (event := pool.step())["kind"] not in ("limited", "exhausted"):
            pass
        assert event["kind"] == "exhausted"
        assert all(c.exhausted and not c.blocked for c in pool.cursors)
    finally:
        pool.close()


def test_search_harder_lifts_a_directions_result_limit(monkeypatch):
    # A direction can reach its 50 results with repeats of tracks the other end
    # found: Search harder, which it offers, must let it go on.
    catalog, found = default_catalog(), []

    def repeats(inventory, pieces, config, *, base, grow_from, close_onto, limits):
        count = 0
        while True:
            if count >= limits.max_results:
                yield {"kind": "result_limit", "nodes": count}
            else:
                count += 1
                found.append(grow_from)
                yield {"kind": "solution", "solution": None, "nodes": count}

    monkeypatch.setattr(editor_search, "solve_steps", repeats)
    pool = PairSearch(build_chain([(catalog["curve"], 0, 1)] * 6), catalog,
                      {"curve": 6, "straight": 4}, (5, 1), (0, 0), 26, 1, 0, False,
                      search_options(None, catalog))
    try:
        while pool.step()["kind"] not in ("limited", "exhausted"):
            pass
        before = len(found)
        pool.harder()
        while pool.step()["kind"] not in ("limited", "exhausted"):
            pass
        assert len(found) > before
    finally:
        pool.close()


def test_pieces_no_walk_can_place_add_no_stage():
    # Buffers beside plain track: the solver drops them, so a plain stage would
    # search the full stage's problem again.
    from duplotrain.geometry import Pose

    catalog = default_catalog()
    half = build_chain([(catalog["curve"], 0, 1)] * 6)
    session = Session(history=[half], inventory={"curve": 20, "buffer": 2})
    job = SearchJob(session, {})
    try:
        assert {cursor.stage for cursor in job.pool.cursors} == {"full inventory"}
    finally:
        job.close()
    # Spare arches too, when the one ramp stands apart from the gap: no walk
    # between the gap's two ends meets that ramp's top, where an arch's foot rests.
    apart, _ = half.with_piece(catalog["ramp"], Pose.make(x=-2000))
    session = Session(history=[apart], inventory={"curve": 20, "ramp": 1, "span": 2})
    job = SearchJob(session, {"grow": [5, 1], "close": [0, 0]})
    try:
        assert {cursor.stage for cursor in job.pool.cursors} == {"full inventory"}
    finally:
        job.close()
