"""Bounded direction portfolios for editor completions, not fresh-loop enumeration.

A difficult obstacle can be near either end, and which end is the hard one is not
known in advance: on tests/fixtures/bridge-gap.json one direction proves the plain
stage impossible in about a hundred nodes while the other wanders for tens of
thousands. So the two directions take turns, each turn with twice the previous
budget, starting small. Whichever direction settles a stage is tried first in
the next one, and each direction keeps its reverse tables between its attempts.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import fields, replace
from time import perf_counter

from .layout import End, Layout
from .pieces import PieceType
from .solver import SolverConfig, SolveResult, SolveStats, solve

#: The first probe in each direction (a sixteenth of a small allowance, at least
#: 16 nodes); every later turn doubles the budget.
FIRST_PROBE = 1024

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
    memo: dict | None = None,
) -> SolveResult:
    """Try either end without multiplying the caller's total search-node budget.

    Exact ordinary connections are reversible. Reversing-loop targets and forced
    fits are not assumed to be direction-equivalent, so those search from the
    chosen end only. A returned batch comes from ONE search: signatures and
    step traces never mix opposite directions. The existing base remains untouched.

    The directions alternate, each turn with twice the previous budget, starting
    at ``FIRST_PROBE`` nodes; whatever is left when a doubled turn would not fit
    goes to that turn. The search is deterministic, so a direction is only given
    a turn when that turn's budget exceeds its previous one. A probe stops the
    portfolio if it finds candidates or exhausts its configured piece bound, even
    if stock remains. Exhausting that bound is not the same as exhausting the
    inventory, and ``complete`` keeps the core solver's meaning. Interrupted
    probes never make an impossibility claim. Retries restart rather than
    retain a search tree; their nodes all count against the shared allowance.

    *memo* is a dict the caller keeps for one closing problem across its stages:
    the direction that settled the last stage is tried first in the next, and each
    direction's reverse tables carry over between attempts and stages that share
    the stock. Tables are keyed by the ends, the stock and the search settings,
    so the memo must not outlive the base layout it was made for.
    """
    if config.reversing_loops or config.slop or config.max_nodes < 32:
        return solve(inventory, pieces, config, base=base,
                     grow_from=grow_from, close_onto=close_onto)
    started = perf_counter()
    totals = SolveStats()
    forward, backward = (grow_from, close_onto), (close_onto, grow_from)
    directions = [forward, backward]
    if memo is not None and memo.get("prefer") == backward:
        directions.reverse()
    tables = memo.setdefault("tables", {}) if memo is not None else None
    # A probe keeps the tables a search of the whole allowance would have built.
    settings = replace(config, completion_base_work=min(4096, config.max_nodes // 8))
    budgets = {forward: 0, backward: 0}
    first = min(FIRST_PROBE, max(16, config.max_nodes // 16))
    result = None
    settled = None
    turn = 0
    while True:
        remaining = config.max_nodes - totals.nodes
        if remaining < 2:
            break
        direction = directions[turn % 2]
        allowance = first << (turn // 2)
        if remaining < 2 * allowance:
            allowance = remaining
        # The core counts the node that detects its limit. Reserve that one so
        # the portfolio never exceeds the public allowance, even on tiny budgets.
        budget = min(allowance, remaining) - 1
        last = False
        if budget <= budgets[direction]:
            # A repeat of an earlier attempt, node for node: give the rest to the
            # other direction if that can still get further, else stop.
            direction = directions[(turn + 1) % 2]
            budget = remaining - 1
            last = True
            if budget <= budgets[direction]:
                break
        budgets[direction] = budget
        offset = totals.nodes

        def progress(nodes: int, offset: int = offset) -> None:
            if config.progress is not None:
                config.progress(offset + nodes)

        grow, close = direction
        result = solve(
            inventory, pieces,
            replace(settings, max_nodes=budget, progress=progress),
            base=base, grow_from=grow, close_onto=close, tables=tables,
        )
        for item in fields(totals):
            name = item.name
            if name in _STATUS:
                continue
            value = getattr(result.stats, name)
            setattr(totals, name, max(getattr(totals, name), value)
                    if name in _HIGH_WATER else getattr(totals, name) + value)
        turn += 1
        # Short turns never reach the core's own heartbeat interval: report the
        # shared count at every turn boundary so a long search stays visibly alive.
        if config.progress is not None:
            config.progress(totals.nodes)
        if result.solutions or not result.stats.aborted:
            settled = direction
            break
        if last:
            break
    if memo is not None and settled is not None:
        memo["prefer"] = settled
    # At least the first probe always runs; validation/error propagation is the
    # core solver's job, before anything is published in the editor.
    assert result is not None
    totals = replace(totals, complete=result.stats.complete, aborted=result.stats.aborted,
                     stop_reason=result.stats.stop_reason, engine=result.stats.engine,
                     duration_s=perf_counter() - started)
    return SolveResult(result.solutions, totals)
