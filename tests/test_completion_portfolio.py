"""Direction fairness, shared budgets and candidate acceptance regressions."""

from dataclasses import replace

import pytest

import duplotrain.completion_search as portfolio
from duplotrain import Layout, Pose, SolverConfig, build_chain, default_catalog, solve
from duplotrain.completion_search import solve_completion
from duplotrain.gui import Session
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

    def search(inventory, pieces, config, *, base, grow_from, close_onto):
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
    # A final forward probe of 24 nodes would repeat the first one exactly, so
    # the reverse probe takes the rest of the allowance.
    assert calls == [((5, 1), (0, 0), 24), ((0, 0), (5, 1), 74)]
    assert heartbeats == [1, 26]
    assert result.stats.nodes == 30 and result.stats.pruned_reach == 5
    assert not result.stats.complete and not result.stats.aborted
    assert result.stats.stop_reason == "piece_limit"


@pytest.mark.parametrize("budget, probes", [
    (32, 2), (33, 3), (100, 2), (25_000, 2), (60_000, 2), (250_000, 3),
])
def test_exhausted_probes_share_one_hard_node_allowance(monkeypatch, budget, probes):
    catalog, base, stock = small_case()
    calls = []

    def search(inventory, pieces, config, **kwargs):
        calls.append(config.max_nodes)
        return SolveResult([], SolveStats(nodes=config.max_nodes + 1,
                           aborted=True, stop_reason="node_limit", max_pieces_searched=12))

    monkeypatch.setattr(portfolio, "solve", search)
    result = solve_completion(stock, catalog, SolverConfig(max_nodes=budget),
                              base=base, grow_from=(5, 1), close_onto=(0, 0))
    # The search is deterministic: a final forward probe only runs when its
    # budget exceeds the first one's, and the allowance is spent in full.
    assert len(calls) == probes
    assert probes == 2 or calls[2] > calls[0]
    assert result.stats.nodes == budget
    assert result.stats.aborted and not result.stats.complete
    assert result.stats.max_pieces_searched == 12


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
