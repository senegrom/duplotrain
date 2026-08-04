"""Finding genuinely different layouts: isomorphism and the hunt for perfection.

**Isomorphism.**  Two layouts are considered the same when their track centrelines
trace congruent subsets of space -- the "track as a curve in R^2" view (with z kept,
so parallel layers and bridges distinguish naturally).  This is deliberately coarser
than the solver's piece-level signatures: a straight and a level crossing draw the
same line, and which straight carries the action stone doesn't change the curve at
all.  Congruence is decided by canonicalising the sampled centreline point cloud over
the 24 lattice rotations and reflection.

**Perfection.**  By exhaustive simulation (:func:`duplotrain.drive.classify`), a
perfectly looping layout must be fully mated (any reachable open end or buffer face
admits a doomed start) and must reverse the train somewhere.  That leaves exactly two
families with today's pieces:

* a closed loop carrying a direction-change stone -- every run ping-pongs around the
  ring, sweeping every tile both ways;
* reversing *topology*: the dogbone, two teardrop lobes stem-to-stem, which turns the
  train around at each end with no stone at all.

:func:`find_perfect_loops` enumerates the first family from an inventory;
:func:`make_dogbone` builds the second from a solver-found teardrop.
"""

from __future__ import annotations

from typing import Iterator, Mapping

from .catalog import STONE_MOUNTS
from .drive import LoopClassification, classify
from .geometry import HEADING_STEPS, cos_sin
from .layout import Layout
from .pieces import PieceType
from .solver import SolverConfig, Solution, solve

__all__ = [
    "congruence_key",
    "find_perfect_loops",
    "find_perfect_networks",
    "is_stem_tailed",
    "pick_stem_tailed",
    "make_dogbone",
]


def congruence_key(layout: Layout, spacing: float = 8.0, decimals: int = 1) -> tuple:
    """A key equal for layouts whose track curves are congruent in space.

    The centrelines are sampled uniformly (sampling is congruence-equivariant: the
    same curve yields the same points wherever it lies), centred on their centroid,
    and canonicalised over the 24 lattice rotations x optional reflection by taking
    the lexicographically smallest rounded point multiset.
    """
    points: list[tuple[float, float, float]] = []
    for placement in layout.placements:
        for line in placement.centrelines(spacing):
            points.extend(line)
    if not points:
        return ()

    n = len(points)
    cx = sum(p[0] for p in points) / n
    cy = sum(p[1] for p in points) / n
    cz = sum(p[2] for p in points) / n
    centred = [(x - cx, y - cy, z - cz) for x, y, z in points]

    best: tuple | None = None
    for mirror in (1.0, -1.0):
        for steps in range(HEADING_STEPS):
            c, s = cos_sin(steps)
            fc, fs = float(c), float(s)
            candidate = tuple(
                sorted(
                    (
                        round(fc * x - fs * (mirror * y), decimals),
                        round(fs * x + fc * (mirror * y), decimals),
                        round(z, decimals),
                    )
                    for x, y, z in centred
                )
            )
            if best is None or candidate < best:
                best = candidate
    return best


def find_perfect_loops(
    inventory: Mapping[str, int],
    pieces: Mapping[str, PieceType],
    config: SolverConfig | None = None,
    stone_id: str = "stone_direction",
) -> list[tuple[Layout, LoopClassification]]:
    """Perfectly looping layouts buildable from *inventory* plus one direction stone.

    Runs the loop solver, clips the stone onto the first stone-mountable piece of
    each closed solution (which straight carries it is irrelevant to the curve), and
    keeps the layouts that classify as perfectly looping -- deduplicated up to
    congruence of their track curves, so a loop realised with a level crossing in
    place of a straight does not count twice.
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
        candidate = sol.layout.with_accessory(mount, stone_id)
        verdict = classify(candidate)
        if verdict.perfectly_looping:
            found[key] = (candidate, verdict)
    return list(found.values())


def _lobe_recipe(teardrop: Solution, pieces: Mapping[str, PieceType]) -> list:
    """The self-contained switch-onward part of a teardrop's step trace."""
    steps = [s for s in teardrop.steps if type(s).__name__ == "_Place"]
    if len(steps) != len(teardrop.steps):
        raise ValueError("teardrop recipe with transits is not replayable here")
    switch_pos = next(
        (i for i, s in enumerate(steps) if pieces[s.piece_id].is_junction), None
    )
    if switch_pos is None:
        raise ValueError("no junction in the teardrop recipe")
    return steps[switch_pos:]


def is_stem_tailed(teardrop: Solution, pieces: Mapping[str, PieceType]) -> bool:
    """Does this teardrop's tail hang off the switch's stem?

    Teardrops come in two operationally different flavours.  *Stem-tailed*: the lobe
    connects branch to branch, so a train off the tail FACES the points, loops,
    trails back and returns down the tail -- the alternating, reversing classic.
    *Branch-tailed*: the lobe connects the stem to the other branch, forming an
    ordinary one-way circuit; a train entering from the tail is absorbed and never
    comes back.  Only the stem-tailed kind composes into a perfect dogbone.
    """
    lobe = _lobe_recipe(teardrop, pieces)
    piece = pieces[lobe[0].piece_id]
    options = [exit_port for exit_port, _ in piece.transit(lobe[0].entry)]
    return len(options) > 1


def pick_stem_tailed(
    solutions: list[Solution], pieces: Mapping[str, PieceType]
) -> Solution | None:
    """The first stem-tailed teardrop among reversing solutions, if any."""
    for sol in solutions:
        if sol.kind == "reversing" and is_stem_tailed(sol, pieces):
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
            continue  # only buffers carry sealed faces today
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
    config=None,
) -> list[tuple[Layout, LoopClassification]]:
    """Exhaustively find perfectly looping networks from an inventory.

    Enumerates every closed network (:func:`duplotrain.networks.enumerate_networks`),
    tries the sensible direction-stone placements on each, keeps those that classify
    perfectly looping, and deduplicates by track-curve congruence.  Complete up to
    the enumeration bounds in *config* -- for small inventories this genuinely
    answers "these are ALL the perfect networks you can build".
    """
    from .networks import enumerate_networks

    result = enumerate_networks(inventory, pieces, config)
    found: dict[tuple, tuple[Layout, LoopClassification]] = {}
    for layout in result.layouts:
        key = congruence_key(layout)
        if key in found:
            continue
        for variant in _stone_variants(layout, stones):
            verdict = classify(variant)
            if verdict.perfectly_looping:
                found[key] = (variant, verdict)
                break
    return list(found.values())


def make_dogbone(
    teardrop: Solution,
    pieces: Mapping[str, PieceType],
    bar_straights: int = 2,
) -> Layout:
    """Grow a solver-found teardrop into a dogbone: the stone-free perfect layout.

    The teardrop's open tail gets a straight bar, a second switch, and a mirror
    lobe replayed from the teardrop's own step recipe; the final joint closes the
    walk into the new switch's other branch.  Every connector ends up mated, so the
    result has no ends to fall off and needs no direction stone: the lobes
    themselves turn the train around.

    Requires a *stem-tailed* teardrop (see :func:`is_stem_tailed`); the branch-tailed
    kind would compose into two one-way traps that never exchange the train.
    """
    if teardrop.kind != "reversing":
        raise ValueError("make_dogbone wants a reversing (teardrop) solution")
    if not is_stem_tailed(teardrop, pieces):
        raise ValueError(
            "this teardrop is branch-tailed (a one-way trap); pick the stem-tailed "
            "variant, e.g. via pick_stem_tailed()"
        )
    layout = teardrop.layout
    opens = layout.connectable_ends()
    if len(opens) != 1:
        raise ValueError("the teardrop should have exactly its tail open")

    cursor = opens[0]
    for _ in range(bar_straights):
        layout, index = layout.attach(pieces["straight"], 0, cursor)
        cursor = (index, 1)

    # The teardrop's step trace is tail pieces, then the switch, then the lobe that
    # closes into the switch's other branch.  The lobe recipe -- switch onward -- is
    # self-contained: replayed anywhere it lands back on its own switch.
    lobe = _lobe_recipe(teardrop, pieces)
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
