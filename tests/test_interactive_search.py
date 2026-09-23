"""Real suspended searches, safety boundaries and atomic editor publication."""
import gc
import json
import weakref
from dataclasses import asdict, replace
from pathlib import Path

import pytest

from duplotrain import build_chain, default_catalog
from duplotrain.editor import PREVIEW_FORMAT, RevisionConflictError, Session, dispatch_session
from duplotrain.editor_search import (
    MAX_JOB_SECONDS,
    PairSearch,
    SearchJob,
    fits_space,
    layout_key,
    search_options,
    valid_extension,
)
from duplotrain.geometry import Pose
from duplotrain.layout import Layout, Placement, layout_from_dict
from duplotrain.solver import (
    SearchLimits,
    Solution,
    SolverConfig,
    _solution_overlaps,
    solve,
    solve_steps,
)
from tests.editor_support import load_adapter, post, running_server


@pytest.fixture
def catalog():
    return default_catalog()


@pytest.fixture
def gap(catalog):
    path = Path(__file__).parent / "fixtures/bridge-gap.json"
    return layout_from_dict(json.loads(path.read_text()), catalog)


def half(catalog):
    return build_chain([(catalog["curve"], 0, 1)] * 6)


def settle(job, limit=20000):
    for _ in range(limit):
        if job.status != "running":
            return
        job.tick()
    pytest.fail("bounded interactive search did not yield a stopping status")


def call(session, action, **body):
    if action != "start" and "job_id" not in body and session._interactive_job is not None:
        body["job_id"] = session._interactive_job.id
    return dispatch_session(session, "/api/search/" + action,
                            {"revision": session.revision,
                             "preview_format": PREVIEW_FORMAT, **body})


def assert_plan(base, solution, stock):
    layout = solution.layout
    assert layout.placements[:len(base)] == base.placements
    assert all(layout.links[a] == b for a, b in base.links.items())
    assert layout.accessories == base.accessories
    assert not layout.joint_issues()
    assert not _solution_overlaps(layout, 0, 120.0, 8.0)
    assert all(n - base.piece_counts.get(pid, 0) <= stock.get(pid, 0)
               for pid, n in layout.piece_counts.items())


def test_bridge_more_resumes_exact_stack_and_retains_every_original(gap):
    session = Session(history=[gap], unlimited=True)
    before = session.snapshot()
    job = SearchJob(session, {"max_results": 8})
    try:
        settle(job)
        assert (len(job.solutions), job.nodes) == (8, 1878)
        first = [layout_key(s.layout) for s in job.solutions]
        for count, nodes in [(16, 1961), (32, 2101)]:
            job.more()
            settle(job)
            assert len(job.solutions) == count
            assert job.nodes == nodes  # total, NOT previous work plus a restarted search
            assert [layout_key(s.layout) for s in job.solutions[:len(first)]] == first
            first = [layout_key(s.layout) for s in job.solutions]
            assert len(set(first)) == count
            for solution in job.solutions:
                assert len(solution.layout) - len(gap) == 24
                assert_plan(gap, solution, session.remaining())
        assert session.snapshot() == before
        assert len(session.history) == 1
    finally:
        job.close()


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_core_generator_resumption_matches_uninterrupted_exhaustion(catalog, engine):
    base = half(catalog)
    cfg = SolverConfig(min_pieces=0, max_pieces=10, max_results=50, max_nodes=50000,
                       engine=engine)
    stock = {"curve": 6, "straight": 4}
    expected = solve(stock, catalog, cfg, base=base)
    limits = SearchLimits(max_nodes=3, max_results=1, max_pieces=2, quantum=1)
    generator = solve_steps(stock, catalog, cfg, base=base, limits=limits)
    kinds, emitted = set(), []
    try:
        for _ in range(100000):
            try:
                event = next(generator)
            except StopIteration as done:
                result = done.value
                break
            kinds.add(event["kind"])
            if event["kind"] == "node_limit":
                limits.max_nodes += 13
            elif event["kind"] == "piece_limit":
                limits.max_pieces += 2
            elif event["kind"] == "result_limit":
                limits.max_results += 1
            elif event["kind"] == "solution":
                emitted.append(layout_key(event["solution"].layout))
        else:
            pytest.fail("iterator did not exhaust the tiny inventory")
        assert {"solution", "progress", "node_limit", "piece_limit", "result_limit"} <= kinds
        assert len(set(emitted)) == len(emitted)
        assert [s.signature for s in result.solutions] == [s.signature for s in expected.solutions]
        a, b = asdict(result.stats), asdict(expected.stats)
        # Raising tiny budgets changes reverse-table construction effort, not
        # the accepted layouts or visited DFS nodes. Compare traversal counters.
        for key in ("duration_s", "completion_probes", "completion_work", "completion_states"):
            a.pop(key)
            b.pop(key)
        assert a == b
    finally:
        generator.close()


@pytest.mark.parametrize("field,value", [("max_nodes", 0), ("quantum", True),
                                        ("max_pieces", -1), ("max_results", 2.5)])
def test_invalid_mutable_limits_reject_before_search(catalog, field, value):
    limits = SearchLimits()
    setattr(limits, field, value)
    iterator = solve_steps({"curve": 6}, catalog, base=half(catalog), limits=limits)
    with pytest.raises(ValueError):
        next(iterator)


def test_publication_pause_resume_and_apply_are_revision_bound_and_undoable(catalog):
    session = Session(history=[half(catalog)], inventory={"curve": 12, "straight": 4})
    before = session.snapshot()
    call(session, "start")
    job = session._interactive_job
    call(session, "tick")
    call(session, "pause")
    paused_nodes, paused_solutions = job.nodes, len(job.solutions)
    call(session, "tick")
    assert (job.nodes, len(job.solutions)) == (paused_nodes, paused_solutions)
    call(session, "resume")
    settle(job)
    old_revision = session.revision
    result = call(session, "publish")
    assert session.revision == old_revision + 1
    assert job.revision == session.revision
    assert session._interactive_job is job
    assert session.snapshot() == before and len(session.history) == 1
    assert result["search_job"]["candidates"]
    with pytest.raises(RevisionConflictError):
        call(session, "tick", revision=old_revision)
    session.apply_candidate(0, revision=session.revision)
    assert session._interactive_job is None and job.status == "discarded"
    assert session.layout.is_closed
    session.undo()
    assert session.snapshot() == before
    session.redo()
    assert session.layout.is_closed


@pytest.mark.parametrize("action", ["tick", "pause", "resume", "continue", "publish", "page"])
def test_wrong_job_identity_never_reuses_new_problem(catalog, action):
    session = Session(history=[half(catalog)])
    old = call(session, "start")["job_id"]
    call(session, "start")
    current = session._interactive_job
    with pytest.raises(ValueError, match="no longer active"):
        call(session, action, job_id=old)
    assert session._interactive_job is current


@pytest.mark.parametrize("body", [
    {"max_results": 51}, {"max_pieces": True}, {"search_effort": 0}, {"slop": float("nan")},
    {"all_gaps": "yes"}, {"options": {"exclude": ["does-not-exist"]}},
    {"options": {"room": [0, 0, 0, 1]}}, {"options": {"sort": "shortest-guaranteed"}},
    {"page": -1}, {"sort": "bad"}, {"harder": "yes"},
])
def test_invalid_new_request_cannot_discard_existing_job(catalog, body):
    session = Session(history=[half(catalog)])
    call(session, "start")
    old, snapshot, revision = session._interactive_job, session.snapshot(), session.revision
    with pytest.raises(ValueError):
        call(session, "start", **body)
    assert session._interactive_job is old and old.status == "running"
    assert session.snapshot() == snapshot and session.revision == revision
    old.close()


def test_failed_tick_releases_job_and_preserves_confirmed_content(catalog, monkeypatch):
    session = Session(history=[half(catalog)])
    call(session, "start")
    old, before = session._interactive_job, session.snapshot()
    def fail():
        raise ValueError("candidate audit error")
    monkeypatch.setattr(old, "tick", fail)
    with pytest.raises(ValueError, match="audit error"):
        call(session, "tick")
    assert session._interactive_job is None
    assert old.status == "discarded" and not old.pool.cursors
    assert session.snapshot() == before


def test_expiry_releases_only_retained_search(catalog):
    session = Session(history=[half(catalog)])
    call(session, "start")
    old, before = session._interactive_job, session.snapshot()
    old.last_touch -= MAX_JOB_SECONDS + 1
    with pytest.raises(ValueError, match="expired"):
        call(session, "page")
    assert session._interactive_job is None and old.status == "discarded"
    assert session.snapshot() == before


def test_abandoned_search_is_collectable_without_cyclic_gc(gap):
    enabled = gc.isenabled()
    gc.disable()
    try:
        session = Session(history=[gap], unlimited=True)
        call(session, "start")
        job = session._interactive_job
        settle(job)
        refs = [weakref.ref(job), weakref.ref(job.pool), weakref.ref(job.pool.arc_session)]
        call(session, "discard")
        del job
        assert all(ref() is None for ref in refs)
    finally:
        if enabled:
            gc.enable()


@pytest.mark.parametrize("host", ["adapter", "http"])
def test_interactive_routes_share_transport_revision_guards(catalog, host):
    session = Session(history=[half(catalog)], inventory={"curve": 12})
    before = session.snapshot()
    def exercise(request):
        start = request("start", {"revision": session.revision})
        body = {"revision": session.revision, "job_id": start["job_id"]}
        for _ in range(200):
            response = request("tick", body)
            if response["status"] != "running":
                break
        assert response["found"] >= 1 and session.snapshot() == before
        published = request("publish", body)
        assert published["revision"] == body["revision"] + 1
        stale = request("tick", body, stale=True)
        assert "error" in stale or "__error" in stale
    if host == "adapter":
        adapter = load_adapter(session)
        exercise(lambda action, body, **_: json.loads(adapter.dispatch(
            "/api/search/" + action, json.dumps(body))))
    else:
        with running_server(session) as server:
            def request(action, body, stale=False):
                code, result = post(server, "/api/search/" + action, body)
                assert code == (409 if stale else 200), result
                return result
            exercise(request)


def test_empty_stock_touching_ends_join_without_spinning_on_find_more(catalog):
    base = build_chain([(catalog["curve"], 0, 1)] * 12)
    session = Session(history=[base], inventory={"curve": 12})
    job = SearchJob(session, {})
    assert len(job.solutions) == 1 and job.status == "direct_join"
    job.more()
    job.more(harder=True)
    job.tick()
    assert job.status == "direct_join" and not job.response(session, {})["resumable"]
    assert_plan(base, job.solutions[0], session.remaining())
    job.close()


def test_two_gap_repair_debits_stock_and_is_one_atomic_plan(catalog):
    ring = build_chain([(catalog["curve"], 0, 1)] * 12).join((0, 0), (11, 1))
    session = Session(history=[ring], inventory={"curve": 12})
    session.remove_piece(7)
    session.remove_piece(2)
    base, before = session.layout, session.snapshot()
    history = len(session.history)
    call(session, "start", all_gaps=True, max_pieces=2, max_results=1)
    job = session._interactive_job
    settle(job)
    assert len(job.solutions) == 1
    assert len(job.solutions[0].layout) == 12
    assert not job.solutions[0].layout.connectable_ends()
    assert_plan(base, job.solutions[0], session.remaining())
    assert session.snapshot() == before and len(session.history) == history
    call(session, "publish")
    session.apply_candidate(0, revision=session.revision)
    assert len(session.history) == history + 1
    session.undo()
    assert session.snapshot() == before


def test_multi_gap_short_stock_does_not_publish_partial_plan(catalog):
    ring = build_chain([(catalog["curve"], 0, 1)] * 12).join((0, 0), (11, 1))
    session = Session(history=[ring], inventory={"curve": 11})
    session.remove_piece(7)
    session.remove_piece(2)
    before = session.snapshot()
    job = SearchJob(session, {"all_gaps": True, "max_pieces": 2, "max_results": 1})
    settle(job)
    assert not job.solutions and not job.complete
    assert session.snapshot() == before
    job.close()


@pytest.mark.parametrize("value", [[], [0, 0, 1], [0, 0, 0, 1], [0, 0, float("inf"), 1],
                                   [True, 0, 3, 4], [0, 0, 1e8, 2]])
def test_room_input_rejects_invalid_rectangles(catalog, value):
    with pytest.raises(ValueError):
        search_options({"room": value}, catalog)


def test_room_and_keepout_include_width_overhang_and_all_heights(catalog):
    straight = Layout((Placement(catalog["straight"], Pose.make()),))
    pad = catalog["straight"].width / 2
    permissive = search_options({"room": [-100, -100, 300, 100]}, catalog)
    assert fits_space(straight, permissive)
    assert not fits_space(straight, search_options({"room": [-100, -pad, 300, pad]}, catalog))
    crossing = search_options({"keep_out": [[30, -1, 40, 1]]}, catalog)
    assert not fits_space(straight, crossing)
    elevated = Layout((Placement(catalog["straight"], Pose.make(z=1000)),))
    assert not fits_space(elevated, crossing)  # floor-to-ceiling, not underpass restrictions
    assert fits_space(straight, search_options({"keep_out": [[900, 900, 950, 950]]}, catalog))
    plate = replace(catalog["straight"], id="test-overhang", end_overhang=120)
    assert not fits_space(Layout((Placement(plate, Pose.make()),)), permissive)


def test_exclusions_do_not_change_owned_inventory_and_ranked_pages_keep_identity(catalog):
    session = Session(history=[half(catalog)], unlimited=True)
    before = session.snapshot()
    job = SearchJob(session, {"options": {"exclude": ["switch", "ramp", "span"],
                                          "sort": "pieces"}, "max_results": 16})
    settle(job)
    assert len(job.solutions) == 16
    for candidate in job.solutions:
        assert all(p.piece.id not in {"switch", "ramp", "span"}
                   for p in candidate.layout.placements[len(session.layout):])
    response = job.response(session, {"page": 1})
    assert len(response["candidates"]) == 8
    for item in response["candidates"]:
        assert item["candidate_id"] == layout_key(job.solutions[item["index"]].layout)
    assert not response["optimal"] and session.snapshot() == before
    ranked = [len(sol.layout) for _, sol in job.ordered()]
    assert ranked == sorted(ranked)
    job.close()


def test_exact_dedup_is_independent_of_new_placement_order(catalog):
    original = build_chain([(catalog["curve"], 0, 1)] * 3)
    n = len(original)
    reversed_layout = Layout(tuple(reversed(original.placements)), {
        (n - 1 - a, ap): (n - 1 - b, bp) for (a, ap), (b, bp) in original.links.items()
    })
    assert layout_key(original) == layout_key(reversed_layout)
    moved = Layout(tuple(Placement(p.piece, Pose(p.frame.x + 1, p.frame.y,
                                                p.frame.z, p.frame.heading)) for p in original),
                   original.links)
    assert layout_key(moved) != layout_key(original)


def test_full_plan_audit_does_not_ignore_colliding_original_track(catalog):
    bad = build_chain([(catalog["curve"], 0, 1)] * 24).join((0, 0), (23, 1))
    candidate = Solution(bad, (), 0, True, 0, ("overlap",))
    assert not valid_extension(bad, candidate, {}, 1, search_options({}, catalog), all_gaps=True)


def test_harder_retains_existing_exact_dfs_objects_and_lifts_depth(catalog):
    base = half(catalog)
    pool = PairSearch(base, catalog, {"curve": 20, "straight": 4}, (5, 1), (0, 0),
                      2, 1, 0, False, search_options({}, catalog))
    objects = [c.iterator for c in pool.cursors]
    for _ in range(10000):
        event = pool.step()
        if event["kind"] == "limited":
            break
    assert event["kind"] == "limited"
    before = pool.nodes
    pool.harder()
    pool.harder()
    assert objects == [c.iterator for c in pool.cursors]
    assert pool.nodes == before and pool.depth == 8
    for _ in range(10000):
        event = pool.step()
        if event["kind"] == "solution":
            break
    assert event["kind"] == "solution"
    pool.close()


def test_response_constraints_are_copied_and_cannot_change_the_saved_problem(catalog):
    session = Session(history=[half(catalog)])
    job = SearchJob(session, {"options": {"room": [-2000, -2000, 2000, 2000],
                                          "keep_out": [[3000, 3000, 4000, 4000]]}})
    try:
        response = job.response(session, {})
        response["options"]["room"][0] = 100000
        response["options"]["exclude"].append("curve")
        response["options"]["keep_out"][0][0] = -100000
        assert job.options["room"][0] == -2000
        assert job.options["exclude"] == []
        assert job.options["keep_out"][0][0] == 3000
    finally:
        job.close()


def test_multi_gap_backtracks_after_an_early_valid_plan_consumes_scarce_stock(catalog,
                                                                            monkeypatch):
    # First half-circle closes with zero or two straights. The second needs all
    # four available straights. Deliberately emit the longer *real exact* first
    # alternative to exercise backtracking rather than just the greedy success.
    import duplotrain.editor_search as module

    a = half(catalog)
    b = build_chain([(catalog["straight"], 0, 1)] * 4 + [(catalog["curve"], 0, 1)] * 6)
    offset = len(a)
    placements = a.placements + tuple(Placement(p.piece, Pose(
        p.frame.x + 5000, p.frame.y, p.frame.z, p.frame.heading)) for p in b)
    links = {**a.links, **{(i + offset, ip): (j + offset, jp)
                           for (i, ip), (j, jp) in b.links.items()}}
    base = Layout(placements, links)
    session = Session(history=[base], inventory={"curve": 24, "straight": 8})
    observed = []

    class ReorderedPair(PairSearch):
        def __init__(self, *args, **kw):
            super().__init__(*args, **kw)
            self.pending = None
            self.reordered = False
            self.primary = len(self.base) == len(base) and max(self.grow[0], self.close_end[0]) < 6

        def step(self):
            if self.primary and self.reordered and self.pending is not None:
                first, self.pending = self.pending, None
                observed.append(len(first["solution"].layout) - len(self.base))
                return first
            event = super().step()
            if self.primary and not self.reordered and event["kind"] == "solution":
                if self.pending is None:
                    self.pending = event
                    return {"kind": "progress"}
                self.reordered = True
                observed.append(len(event["solution"].layout) - len(self.base))
            return event

    monkeypatch.setattr(module, "PairSearch", ReorderedPair)
    job = SearchJob(session, {"all_gaps": True, "max_pieces": 16, "max_results": 1})
    try:
        settle(job)
        assert observed[:2] == [8, 6]
        assert len(job.solutions) == 1
        assert_plan(base, job.solutions[0], session.remaining())
        assert job.solutions[0].layout.is_closed
        assert len(job.solutions[0].layout) - len(base) == 16
    finally:
        job.close()


def test_interactive_exhaustion_uses_the_raised_result_limit_not_initial_config(catalog):
    base = half(catalog)
    stock = {"curve": 6, "straight": 2}
    cfg = SolverConfig(min_pieces=0, max_pieces=8, max_results=1, max_nodes=50000)
    limits = SearchLimits(max_nodes=50000, max_results=50, max_pieces=8)
    iterator = solve_steps(stock, catalog, cfg, base=base, limits=limits)
    try:
        while True:
            event = next(iterator)
            assert event["kind"] not in ("node_limit", "piece_limit", "result_limit")
    except StopIteration as done:
        result = done.value
    finally:
        iterator.close()
    assert result.stats.complete
    assert len(result.solutions) > 1
    expected = solve(stock, catalog, replace(cfg, max_results=50), base=base)
    assert result.solutions == expected.solutions


@pytest.mark.parametrize("slop, count", [(4.9, 0), (5.0, 3)])
def test_interactive_forced_fit_preserves_exactness_and_joint_budget(catalog, slop, count):
    from benchmarks.completion import cases

    case = next(c for c in cases(catalog) if c.name == "offset_circle_slop_5")
    owned = {pid: n + case.base.piece_counts.get(pid, 0) for pid, n in case.inventory.items()}
    session = Session(history=[case.base], inventory=owned)
    ends = case.ends or {}
    job = SearchJob(session, {"slop": slop, "max_pieces": 20,
                             "grow": ends.get("grow_from"), "close": ends.get("close_onto")})
    try:
        settle(job)
        assert len(job.solutions) == count
        for solution in job.solutions:
            assert not solution.exact and solution.gap == pytest.approx(5)
            assert solution.layout.placements[:len(case.base)] == case.base.placements
            assert not _solution_overlaps(solution.layout, len(case.base), 120, 8)
    finally:
        job.close()


def test_ends_at_different_heights_explain_the_proof_instead_of_searching(catalog):
    # Both ramps climb and no ramp is left to come down: nothing to search.
    up = build_chain([(catalog["straight"], 0, 1), (catalog["ramp"], 0, 1)]
                     + [(catalog["straight"], 0, 1)] * 2)
    session = Session(history=[up], inventory={"straight": 3, "ramp": 1, "curve": 12})
    state = call(session, "start")
    assert state["status"] == "exhausted" and state["complete"] and state["searched"] == 0
    assert "can never come back down" in state["reason"]
    assert state["reason"] == session.solve_gap(None, None, 0, 8)["reason"]
