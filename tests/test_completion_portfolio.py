"""Direction fairness, shared budgets and candidate acceptance regressions."""

import json
from dataclasses import replace
from pathlib import Path

import pytest

import duplotrain.completion_search as portfolio
from duplotrain import Layout, Pose, SolverConfig, build_chain, default_catalog, solve
from duplotrain.completion_search import solve_completion
from duplotrain.gui import Session
from duplotrain.layout import layout_from_dict
from duplotrain.solver import SolveResult, SolveStats, _solution_overlaps


def small_case():
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 6)
    return catalog, base, {"curve": 6, "straight": 4}


def test_easy_search_keeps_the_original_results_without_a_second_probe():
    catalog, base, stock = small_case()
    config = SolverConfig(min_pieces=0, max_results=1000, max_nodes=100_000)
    ends = dict(base=base, grow_from=(5, 1), close_onto=(0, 0))
    reference = solve(stock, catalog, config, **ends)
    result = solve_completion(stock, catalog, config, **ends)
    assert result.solutions == reference.solutions
    assert result.stats.complete
    assert result.stats.nodes == reference.stats.nodes


def test_wrong_end_is_not_allowed_to_spend_the_whole_budget(monkeypatch):
    catalog, base, stock = small_case()
    calls = []
    heartbeats = []

    def search(inventory, pieces, config, *, base, grow_from, close_onto, tables=None):
        calls.append((grow_from, close_onto, config.max_nodes))
        config.progress(1)
        if grow_from == (5, 1):
            return SolveResult([], SolveStats(nodes=config.max_nodes + 1,
                               aborted=True, stop_reason="node_limit", pruned_reach=3))
        return SolveResult([], SolveStats(nodes=5, stop_reason="piece_limit", pruned_reach=2))

    monkeypatch.setattr(portfolio, "solve", search)
    config = SolverConfig(max_nodes=100, progress=heartbeats.append)
    result = solve_completion(stock, catalog, config,
                              base=base, grow_from=(5, 1), close_onto=(0, 0))
    # A hundred-node allowance probes sixteen nodes at a time; the other end
    # settled its first turn, so the wrong end spent sixteen of the hundred.
    assert calls == [((5, 1), (0, 0), 15), ((0, 0), (5, 1), 15)]
    # The core's own heartbeat, then the shared count at each turn boundary.
    assert heartbeats == [1, 16, 17, 21]
    assert result.stats.nodes == 21 and result.stats.pruned_reach == 5
    assert not result.stats.complete and not result.stats.aborted
    assert result.stats.stop_reason == "piece_limit"


@pytest.mark.parametrize("budget, probes", [
    (32, 2), (33, 2), (100, 4), (25_000, 7), (60_000, 9), (250_000, 13),
])
def test_exhausted_probes_share_one_hard_node_allowance(monkeypatch, budget, probes):
    catalog, base, stock = small_case()
    calls = []

    def search(inventory, pieces, config, *, base, grow_from, close_onto, tables=None):
        calls.append((grow_from, config.max_nodes))
        return SolveResult([], SolveStats(nodes=config.max_nodes + 1,
                           aborted=True, stop_reason="node_limit", max_pieces_searched=12))

    monkeypatch.setattr(portfolio, "solve", search)
    result = solve_completion(stock, catalog, SolverConfig(max_nodes=budget),
                              base=base, grow_from=(5, 1), close_onto=(0, 0))
    # The directions alternate with doubling budgets, the rest goes to the turn
    # it no longer fits, the allowance is spent exactly and never exceeded.
    assert len(calls) == probes
    assert [grow for grow, _ in calls] == [(5, 1), (0, 0)] * (probes // 2) + [(5, 1)] * (probes % 2)
    for grow in ((5, 1), (0, 0)):
        budgets = [nodes for start, nodes in calls if start == grow]
        assert budgets == sorted(budgets) and len(set(budgets)) == len(budgets)
    assert result.stats.nodes == budget
    assert result.stats.aborted and not result.stats.complete
    assert result.stats.max_pieces_searched == 12


def test_a_stage_prefers_the_direction_that_settled_the_previous_one(monkeypatch):
    catalog, base, stock = small_case()
    calls = []

    def search(inventory, pieces, config, *, base, grow_from, close_onto, tables=None):
        calls.append(grow_from)
        if grow_from == (5, 1):
            return SolveResult([], SolveStats(nodes=config.max_nodes + 1,
                               aborted=True, stop_reason="node_limit"))
        return SolveResult([], SolveStats(nodes=3, stop_reason="exhausted", complete=True))

    monkeypatch.setattr(portfolio, "solve", search)
    memo = {}
    for _ in range(2):
        solve_completion(stock, catalog, SolverConfig(max_nodes=25_000),
                         base=base, grow_from=(5, 1), close_onto=(0, 0), memo=memo)
    # The first stage tried the wrong end first; the second started with the
    # end that settled it, and never went back.
    assert calls == [(5, 1), (0, 0), (0, 0)]
    assert memo["prefer"] == ((0, 0), (5, 1))


def test_attempts_in_one_direction_share_their_reverse_tables(monkeypatch):
    import duplotrain.solver as solver

    built = []
    original = solver._CompletionReachability

    class Counting(original):
        def __init__(self, eng, *args, **kwargs):
            built.append(eng.anchor)
            super().__init__(eng, *args, **kwargs)

    monkeypatch.setattr(solver, "_CompletionReachability", Counting)
    catalog = default_catalog()
    base = layout_from_dict(json.loads(
        (Path(__file__).parent / "fixtures" / "bridge-gap.json").read_text()), catalog)
    stock = {"curve": 16, "straight": 4}
    ends = dict(base=base, grow_from=(25, 0), close_onto=(23, 1))
    memo = {}
    # Sixteen nodes per turn: both ends run out of budget, and no turn can repeat.
    tiny = SolverConfig(min_pieces=0, max_results=100, max_nodes=40)
    result = solve_completion(stock, catalog, tiny, **ends, memo=memo)
    assert result.stats.aborted and len(built) == 2  # one table per direction
    # The same problem again: no new tables, and the tables keep their answers.
    again = solve_completion(stock, catalog, tiny, **ends, memo=memo)
    assert again.stats.aborted and len(built) == 2
    assert all(table.nodes_spent > 0 for table in memo["tables"].values())
    # A different stock is a different problem (six curves exhaust at once, so
    # only the first direction runs).
    solve_completion({"curve": 6}, catalog, tiny, **ends, memo=memo)
    assert len(built) == 3
    # Without a memo every search builds its own tables and reports only its own work.
    fresh = solve_completion(stock, catalog, tiny, **ends)
    assert len(built) == 5 and fresh.stats.completion_work > 0


@pytest.mark.parametrize("extra", [{"slop": 5.0}, {"reversing_loops": True}, {"max_nodes": 10}])
def test_forced_fits_reversing_targets_and_tiny_requests_keep_one_direction(monkeypatch, extra):
    catalog, base, stock = small_case()
    config = replace(SolverConfig(), **extra)
    calls = []

    def search(*args, **kwargs):
        calls.append((args, kwargs))
        return SolveResult([], SolveStats())

    monkeypatch.setattr(portfolio, "solve", search)
    solve_completion(stock, catalog, config, base=base, grow_from=(5, 1), close_onto=(0, 0))
    assert len(calls) == 1 and calls[0][0][2] is config
    assert calls[0][1]["grow_from"] == (5, 1)


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_rejected_candidates_do_not_exhaust_the_result_limit(engine):
    catalog, base, stock = small_case()
    seen = []

    def accept(candidate):
        seen.append(candidate.piece_count)
        return candidate.piece_count == 16  # six base curves + six curves/four straights

    result = solve(stock, catalog, SolverConfig(min_pieces=0, max_results=1, engine=engine,
                   solution_filter=accept), base=base)
    assert result.solutions and len(result.solutions[0].layout) == 16
    assert result.stats.dropped_filter > 0
    assert 12 in seen and 16 in seen
    assert result.solutions[0].layout.is_closed
    assert not _solution_overlaps(result.solutions[0].layout, 0, 120, 8)


def test_filter_validation_and_exceptions_are_not_silenced():
    with pytest.raises(ValueError, match="solution_filter"):
        SolverConfig(solution_filter=42)
    catalog, base, stock = small_case()

    def fail(candidate):
        raise RuntimeError("audit failed")

    with pytest.raises(RuntimeError, match="audit failed"):
        solve(stock, catalog, SolverConfig(solution_filter=fail), base=base)


def test_mating_hints_never_offer_overlapping_road_plates():
    catalog = default_catalog()
    layout, a = Layout().with_piece(catalog["level_crossing"], Pose.make())
    layout, b = layout.with_piece(catalog["level_crossing"], Pose.make(x=128))
    layout, c = layout.with_piece(catalog["straight"], Pose.make(x=128))
    assert ((a, 1), (b, 0)) not in layout.matable_pairs()
    assert ((a, 1), (c, 0)) in layout.matable_pairs()
    assert [[a, 1], [b, 0]] not in Session(history=[layout]).state()["matable"]
    for first, second in layout.matable_pairs():
        layout.join(first, second)  # each advertised joint can actually be made


def test_even_a_forced_joint_cannot_link_an_end_to_itself():
    catalog = default_catalog()
    layout = build_chain([(catalog["straight"], 0, 1)])
    with pytest.raises(ValueError, match="itself"):
        layout.join((0, 0), (0, 0), force=True)
    assert not layout.links


def test_editor_closes_the_reported_gap_from_either_end_in_few_nodes():
    catalog = default_catalog()
    base = layout_from_dict(json.loads(
        (Path(__file__).parent / "fixtures" / "bridge-gap.json").read_text()), catalog)
    spare = {"curve": 16, "straight": 4, "ramp": 2, "span": 2}
    owned = {pid: base.piece_counts.get(pid, 0) + spare.get(pid, 0) for pid in catalog}
    found = []
    for grow, close in (((25, 0), (23, 1)), ((23, 1), (25, 0))):
        session = Session(history=[base], inventory=owned)
        outcome = session.solve_gap(grow, close, 0, 8)
        # The plain stage from (25, 0) could wander for tens of thousands of
        # nodes; the other end proves it impossible in about a hundred, and the
        # bridge stage then starts from that end.
        assert outcome["found"] == 8 and outcome["stop_reason"] == "bridge_search"
        assert outcome["searched"] < 3000
        found.append({candidate.signature for candidate in session.candidates})
    assert found[0] == found[1]
