"""Finding genuinely different layouts: isomorphism and the hunt for perfection.

**Isomorphism.**  Two layouts are considered the same when their track centrelines
trace congruent subsets of space -- the "track as a curve in R^2" view (with z kept,
so parallel layers and bridges distinguish naturally).  This is deliberately coarser
than the solver's piece-level signatures: a straight and a level crossing draw the
same line, and which straight carries the action stone doesn't change the curve at
all.  Congruence is decided by choosing a canonical frame for the exact centreline
union over the 24 lattice rotations and reflection, then sampling and rounding in
that frame.

**Perfection.** By exhaustive simulation (:func:`duplotrain.drive.classify`),
classify each candidate's train dynamics. Known constructions include a ring with a
direction stone, reversing topology (dogbones), and buffered shuttles guarded by
face stones. The search helpers expose their enumeration limits and stone-placement
policy; a classification of a candidate is not a completeness proof for a search.

:func:`find_perfect_loops` searches the one-stone ring family;
:func:`find_perfect_networks` searches closed networks with guarded buffers and at
most one optional mid-piece direction stone. :func:`make_dogbone` constructs the
stone-free family from a solver-found teardrop.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator, Mapping
from typing import TYPE_CHECKING

from ._congruence import congruence_key
from .catalog import STONE_MOUNTS
from .drive import LoopClassification, classify
from .layout import Layout
from .pieces import PieceType
from .solver import Solution, SolverConfig, SolveStats, _Place, solve

if TYPE_CHECKING:
    from .networks import NetworkConfig, NetworkStats


class IncompleteSearchError(RuntimeError):
    """A requested exhaustive search hit a bound; ``result`` retains partial work."""

    def __init__(self, result: PerfectResult) -> None:
        self.result = result
        super().__init__(f"search incomplete: {result.stats.stop_reason}")


class PerfectResult(list[tuple[Layout, LoopClassification]]):
    """List-compatible perfect layouts plus the underlying enumeration status.

    ``stats.complete`` means the searched family was exhausted over the inventory,
    not a proof that our stone-placement policy covers every possible accessory
    arrangement. ``require_complete`` rejects node, result and piece caps.
    """

    def __init__(
        self, layouts: Iterable[tuple[Layout, LoopClassification]],
        stats: SolveStats | NetworkStats,
    ) -> None:
        super().__init__(layouts)
        self.stats = stats

    def require_complete(self) -> PerfectResult:
        """Return this result, or raise with the partial result still attached."""
        if not self.stats.complete:
            raise IncompleteSearchError(self)
        return self


def find_perfect_loops(
    inventory: Mapping[str, int],
    pieces: Mapping[str, PieceType],
    config: SolverConfig | None = None,
    *,
    require_complete: bool = False,
) -> PerfectResult:
    """Perfectly looping layouts buildable from *inventory* plus one direction stone.

    Runs the loop solver, clips the stone onto the first stone-mountable piece of
    each closed solution (which straight carries it is irrelevant to the curve), and
    keeps the layouts that classify as perfectly looping -- deduplicated up to
    congruence of their track curves, so a loop realised with a level crossing in
    place of a straight does not count twice. Results retain ``stats``; pass
    ``require_complete=True`` to reject a capped enumeration of this family.
    """
    result = solve(inventory, pieces, config)
    found: dict[tuple, tuple[Layout, LoopClassification]] = {}
    for sol in result.solutions:
        if not sol.exact or sol.kind != "loop" or not sol.layout.is_closed:
            continue
        mount = next(
            (
                index
                for index, placement in enumerate(sol.layout.placements)
                if placement.piece.id in STONE_MOUNTS
            ),
            None,
        )
        if mount is None:
            continue  # nowhere to clip the stone: completely looping at best
        key = congruence_key(sol.layout)
        if key in found:
            continue
        candidate = sol.layout.with_accessory(mount, "stone_direction")
        verdict = classify(candidate)
        if verdict.perfectly_looping:
            found[key] = (candidate, verdict)
    perfect = PerfectResult(found.values(), result.stats)
    return perfect.require_complete() if require_complete else perfect


def _lobe_recipe(teardrop: Solution, pieces: Mapping[str, PieceType]) -> list:
    """The self-contained switch-onward part of a teardrop's step trace."""
    steps = [s for s in teardrop.steps if isinstance(s, _Place)]
    if len(steps) != len(teardrop.steps):
        raise ValueError("teardrop recipe with transits is not replayable here")
    # The steps place the pieces after a completion's base: step k is placement
    # offset + k. The walk's last piece closes into a stub of the switch that starts
    # the lobe (the first junction in the trace may be a crossing on the tail).
    layout = teardrop.layout
    offset = len(layout) - len(steps)
    target = layout.links.get((offset + len(steps) - 1, steps[-1].exit)) if steps else None
    if target is None:
        raise ValueError("no junction in the teardrop recipe")
    if target[0] >= offset:
        lobe = steps[target[0] - offset:]
    else:
        # A completion closing into the base junction it grew from: the lobe is that
        # junction, entered from its one port routed to the walk's start, then the walk.
        junction = layout.placements[target[0]].piece
        start = layout.links.get((offset, steps[0].entry))
        if start is None or start[0] != target[0]:
            raise ValueError("the teardrop's lobe runs through its base layout")
        tails = [port for port in range(len(junction.ports))
                 if port not in (start[1], target[1])]
        if len(tails) != 1:
            raise ValueError("the teardrop's junction has no single tail")
        if not any(exit_port == start[1] for exit_port, _ in junction.transit(tails[0])):
            # The tail leads to where the walk closed, not to where it began: a
            # train off the tail rounds the lobe one way and never comes back.
            raise ValueError(_BRANCH_TAILED)
        lobe = [_Place(junction.id, tails[0], start[1]), *steps]
    if not pieces[lobe[0].piece_id].is_junction:
        raise ValueError("no junction in the teardrop recipe")
    return lobe


_BRANCH_TAILED = ("this teardrop is branch-tailed (a one-way trap); pick the stem-tailed "
                  "variant, e.g. via pick_stem_tailed()")


def _stem_tailed(lobe: list, pieces: Mapping[str, PieceType]) -> bool:
    """Does the train entering the lobe's junction from the tail choose a branch?"""
    return len(pieces[lobe[0].piece_id].transit(lobe[0].entry)) > 1


def is_stem_tailed(teardrop: Solution, pieces: Mapping[str, PieceType]) -> bool:
    """Does this teardrop's tail hang off the switch's stem?

    Teardrops come in two operationally different flavours.  *Stem-tailed*: the lobe
    connects branch to branch, so a train off the tail FACES the points, loops,
    trails back and returns down the tail -- the alternating, reversing classic.
    *Branch-tailed*: the lobe connects the stem to the other branch, forming an
    ordinary one-way circuit; a train entering from the tail is absorbed and never
    comes back.  Only the stem-tailed kind composes into a perfect dogbone.

    Non-reversing solutions (plain loops, junction-free traces) are simply not
    teardrops, and a lobe that cannot be replayed from the steps (transits, or a
    completion's lobe through its base) cannot compose: False, not an error.
    """
    if teardrop.kind != "reversing":
        return False
    try:
        return _stem_tailed(_lobe_recipe(teardrop, pieces), pieces)
    except ValueError:
        return False


def pick_stem_tailed(
    solutions: list[Solution], pieces: Mapping[str, PieceType]
) -> Solution | None:
    """The first stem-tailed teardrop among reversing solutions, if any."""
    for sol in solutions:
        if is_stem_tailed(sol, pieces):
            return sol
    return None


def _stone_variants(
    layout: Layout, stones: Mapping[str, int]
) -> Iterator[Layout]:
    """Sensible direction-stone placements to try on a closed network.

    Buffers make placement forced: every buffer face needs the stone on its
    neighbour's mating face (the reversing-terminator idiom), or the network has a
    doomed start and can never be perfect.  After those, the variants are "no extra
    stone" and "one mid-piece stone on each straight" -- which is what turns a plain
    loop perfect.
    """
    available = stones.get("stone_direction", 0)
    base = layout
    used = 0
    for index, placement in enumerate(layout.placements):
        if not placement.piece.sealed:
            continue  # sealed faces are buffers' bumpers
        connector = next(
            p for p in range(len(placement.piece.ports)) if p not in placement.piece.sealed
        )
        link = layout.links.get((index, connector))
        if link is None:
            return  # not actually closed; nothing to try
        neighbour, port = link
        if layout.placements[neighbour].piece.id not in STONE_MOUNTS:
            return  # cannot guard this buffer: never perfect
        base = base.with_accessory(neighbour, "stone_direction", at_port=port)
        used += 1
    if used > available:
        return
    yield base
    if available > used:
        for index, placement in enumerate(layout.placements):
            if placement.piece.id in STONE_MOUNTS:
                yield base.with_accessory(index, "stone_direction")


def find_perfect_networks(
    inventory: Mapping[str, int],
    pieces: Mapping[str, PieceType],
    stones: Mapping[str, int],
    config: NetworkConfig | None = None,
    *,
    require_complete: bool = False,
) -> PerfectResult:
    """Search closed networks under the documented direction-stone policy.

    Every collision-legal realization is eligible for classification BEFORE its
    curve is deduplicated. This preserves different mountable-piece arrangements
    with the same centreline. Results retain the enumeration statistics; pass
    ``require_complete=True`` to reject node, result or piece-limited searches.
    Exhaustion refers to this search and ``_stone_variants`` policy, not to all
    conceivable placements of multiple optional stones.
    """
    from .networks import enumerate_networks

    accepted: dict[int, tuple[Layout, LoopClassification]] = {}

    def qualifies(layout: Layout) -> bool:
        for variant in _stone_variants(layout, stones):
            verdict = classify(variant)
            if verdict.perfectly_looping:
                accepted[id(layout)] = (variant, verdict)
                return True
        return False

    result = enumerate_networks(inventory, pieces, config, accept=qualifies)
    perfect = PerfectResult((accepted[id(layout)] for layout in result.layouts), result.stats)
    return perfect.require_complete() if require_complete else perfect


def make_dogbone(teardrop: Solution, pieces: Mapping[str, PieceType]) -> Layout:
    """Grow a solver-found teardrop into a dogbone: the stone-free perfect layout.

    The teardrop's open tail gets a bar of two straights, a second switch, and a copy of
    the lobe replayed from the teardrop's own step recipe; the final joint closes the
    walk into the new switch's other branch.  Every connector ends up mated, so the
    result has no ends to fall off and needs no direction stone: the lobes
    themselves turn the train around.

    Requires a *stem-tailed* teardrop (see :func:`is_stem_tailed`); the branch-tailed
    kind would compose into two one-way traps that never exchange the train.
    """
    if teardrop is None:  # what pick_stem_tailed returns when it finds none
        raise ValueError("no teardrop to build from: none of them is stem-tailed")
    if teardrop.kind != "reversing":
        raise ValueError("make_dogbone wants a reversing (teardrop) solution")
    # The teardrop's step trace is tail pieces, then the switch, then the lobe that
    # closes into the switch's other branch.  The lobe recipe -- switch onward -- is
    # self-contained: replayed anywhere it lands back on its own switch.
    lobe = _lobe_recipe(teardrop, pieces)
    if not _stem_tailed(lobe, pieces):
        raise ValueError(_BRANCH_TAILED)
    layout = teardrop.layout
    opens = layout.connectable_ends()
    if len(opens) != 1:
        raise ValueError("the teardrop should have exactly its tail open")

    cursor = opens[0]
    for _ in range(2):
        layout, index = layout.attach(pieces["straight"], 0, cursor)
        cursor = (index, 1)

    layout, switch_index = layout.attach(
        pieces[lobe[0].piece_id], lobe[0].entry, cursor
    )
    cursor = (switch_index, lobe[0].exit)
    for step in lobe[1:]:
        layout, index = layout.attach(pieces[step.piece_id], step.entry, cursor)
        cursor = (index, step.exit)

    # Close into whichever branch of the new switch the walk has come back to.
    cursor_pose = layout.pose_of(cursor)
    for port in range(len(pieces[lobe[0].piece_id].ports)):
        end = (switch_index, port)
        if end in layout.links or end == cursor:
            continue
        if cursor_pose.connects_to(layout.pose_of(end)):
            layout = layout.join(cursor, end)
            break
    else:
        raise ValueError("lobe replay did not land back on the new switch")

    if not layout.is_closed:
        raise ValueError("dogbone construction left connectors open")
    return layout
