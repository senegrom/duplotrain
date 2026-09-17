"""Bounded direction portfolios for editor completions, not fresh-loop enumeration.

A difficult obstacle can be near either end. Spend short, deterministic probes in
both directions before committing the rest of the node budget to one long search.
The core solver and its exact collision/reachability checks are unchanged.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import fields, replace
from time import perf_counter

from .layout import End, Layout
from .pieces import PieceType
from .solver import SolverConfig, SolveResult, SolveStats, solve

# Counters sum across attempts; table sizes and attempted depth are high-water marks.
_HIGH_WATER = frozenset({
    "completion_states", "completion_height_states", "completion_bound_depth",
    "completion_bound_states", "max_pieces_searched",
})
_STATUS = frozenset({"complete", "aborted", "stop_reason", "engine", "duration_s"})


def solve_completion(
    inventory: Mapping[str, int],
    pieces: Mapping[str, PieceType],
    config: SolverConfig,
    *,
    base: Layout,
    grow_from: End,
    close_onto: End,
) -> SolveResult:
    """Try either end without multiplying the caller's total search-node budget.

    Exact ordinary connections are reversible. Reversing-loop targets and forced
    fits are not assumed to be direction-equivalent, so those retain the original
    one-direction search. A returned batch comes from ONE search: signatures and
    step traces never mix opposite directions. The existing base remains untouched.

    A probe stops the portfolio if it finds candidates or exhausts its configured
    piece bound, even if stock remains. Exhausting that bound is not the same as
    exhausting the inventory, and ``complete`` keeps the core solver's meaning.
    Interrupted probes never make an impossibility claim. Retries restart rather
    than retain a search tree; their nodes all count against the shared allowance.

    The search is deterministic, so a final probe in the original direction can
    only get further than the first one with a larger budget. Below 65,536 nodes
    the three shares are a quarter, a half and a quarter again: that last probe
    would repeat the first one node for node and stop where it stopped. The
    reverse probe then takes the rest of the allowance instead.
    """
    if config.reversing_loops or config.slop or config.max_nodes < 32:
        return solve(inventory, pieces, config, base=base,
                     grow_from=grow_from, close_onto=close_onto)
    started = perf_counter()
    totals = SolveStats()
    attempts = (
        (grow_from, close_onto, min(16_384, config.max_nodes // 4)),
        (close_onto, grow_from, min(32_768, config.max_nodes // 2)),
        (grow_from, close_onto, config.max_nodes),
    )
    result = None
    first_budget = None
    for grow, close, allowance in attempts:
        remaining = config.max_nodes - totals.nodes
        if remaining < 2:
            break
        if first_budget is None:
            first_budget = min(allowance, remaining) - 1
        elif (grow, close) != (grow_from, close_onto):
            # What the final probe would get after this one; if that cannot
            # exceed the first probe's budget, it cannot find anything new.
            if remaining - min(allowance, remaining) - 1 <= first_budget:
                allowance = remaining
        # The core counts the node that detects its limit. Reserve that one so
        # the portfolio never exceeds the public allowance, even on tiny budgets.
        budget = min(allowance, remaining) - 1
        offset = totals.nodes

        def progress(nodes: int, offset: int = offset) -> None:
            if config.progress is not None:
                config.progress(offset + nodes)

        result = solve(
            inventory, pieces,
            replace(config, max_nodes=budget, progress=progress),
            base=base, grow_from=grow, close_onto=close,
        )
        for item in fields(totals):
            name = item.name
            if name in _STATUS:
                continue
            value = getattr(result.stats, name)
            setattr(totals, name, max(getattr(totals, name), value)
                    if name in _HIGH_WATER else getattr(totals, name) + value)
        if result.solutions or not result.stats.aborted:
            break
    # At least the first probe always runs; validation/error propagation is the
    # core solver's job, before anything is published in the editor.
    assert result is not None
    totals = replace(totals, complete=result.stats.complete, aborted=result.stats.aborted,
                     stop_reason=result.stats.stop_reason, engine=result.stats.engine,
                     duration_s=perf_counter() - started)
    return SolveResult(result.solutions, totals)
