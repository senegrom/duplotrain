"""Drive a virtual train around a layout, with stateful switches.

The geometry solver proves that track *connects*; this module answers the follow-up
question: if you put a train down and let it go, what actually happens?  That needs
the operational semantics the static model ignores:

**Switches keep state.**  Each junction has a tongue pointing at one of its branch
routes.  A *facing* move (entering a port with a choice of exits -- the stem) follows
the tongue.  A *trailing* move (entering through a branch) pushes through to the stem
and **forces the tongue to the branch the train came from**, as the modern unsprung
DUPLO points do.  This is why a teardrop runs forever while alternating lobes: every
trailing pass re-aims the tongue at the branch just used, so the next facing pass
retraces it in the opposite direction of travel.

**Action stones act per pass.**  A direction-change stone bounces the train back out
of the piece it entered; a stop stone parks it.  The other stones (horn, lights,
refuel) don't affect motion.

**Ends end runs.**  Rolling into a buffer's sealed face is a gentle stop; rolling off
a plain open connector is a derailment.

A run is *endless* when the full state -- current piece, entry port, and every
switch's tongue -- repeats.  State space is finite, so every run either ends or is
provably periodic.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Iterable, Mapping

from .layout import End, Layout

__all__ = ["DriveReport", "drive", "endless_run", "classify", "drivable_universe"]

#: Stones that affect motion.
STOP_STONE = "stone_stop"
DIRECTION_STONE = "stone_direction"

#: Safety cap; unreachable in practice because state space is finite and small.
MAX_STEPS = 100_000


@dataclass(frozen=True, slots=True)
class DriveReport:
    """What happened to the train.

    outcome:
        ``endless`` -- the exact state repeated: the train runs forever;
        ``stopped`` -- a stop stone parked it;
        ``buffered`` -- it rolled up against a buffer's bumper face;
        ``derailed`` -- it rolled off an open connector.
    """

    outcome: str
    steps: tuple[tuple[int, int, int], ...]  # (placement, entered port, exited port)
    cycle_start: int | None  # index into steps where the endless cycle begins
    reversals: int
    visited: frozenset[int]
    final_switch_states: Mapping[int, int]

    @property
    def period(self) -> int | None:
        if self.cycle_start is None:
            return None
        return len(self.steps) - self.cycle_start

    def covers(self, layout: Layout) -> bool:
        """Did the run visit every drivable piece?

        Coverage ranges over track a train can actually traverse: a buffer stop's
        only route runs into its sealed face, so it can terminate a run but never be
        driven through, and it doesn't count against coverage.
        """
        return self.visited >= drivable_universe(layout)


def drivable_universe(layout: Layout) -> frozenset[int]:
    """Placements traversable between two real connectors -- the coverage universe."""
    universe = set()
    for index, placement in enumerate(layout.placements):
        piece = placement.piece
        for route in piece.routes:
            if route.port_a not in piece.sealed and route.port_b not in piece.sealed:
                universe.add(index)
                break
    return frozenset(universe)


def _default_switch_states(layout: Layout) -> dict[int, int]:
    """Tongue positions as a builder would leave them: aimed at the first branch."""
    states: dict[int, int] = {}
    for index, placement in enumerate(layout.placements):
        piece = placement.piece
        if not piece.is_junction:
            continue
        for port in range(len(piece.ports)):
            options = [exit_port for exit_port, _ in piece.transit(port)]
            if len(options) > 1:
                states[index] = min(options)
                break
    return states


def drive(
    layout: Layout,
    start: End | None = None,
    switch_states: Mapping[int, int] | None = None,
) -> DriveReport:
    """Simulate a train from *start* until it stops, derails, or provably loops.

    Args:
        layout: the build, including any clipped-on action stones.
        start: ``(placement, port)`` the train ENTERS its first piece through --
            i.e. it travels from that connector into the piece.  Defaults to the
            first piece's first port.
        switch_states: initial tongue positions, ``placement -> exit port``; defaults
            to every tongue aimed at its lowest-numbered branch.
    """
    if not layout.placements:
        raise ValueError("nothing to drive on")
    if start is None:
        start = (0, layout.placements[0].piece.routes[0].port_a)
    if layout.is_sealed(start):
        raise ValueError("a train cannot enter through a sealed buffer face")

    states = dict(_default_switch_states(layout))
    if switch_states:
        states.update({int(k): int(v) for k, v in switch_states.items()})

    stones_by_placement: dict[int, list[tuple[str, int | None]]] = {}
    for index in range(len(layout.placements)):
        entries = layout.stone_entries_on(index)
        if entries:
            stones_by_placement[index] = entries

    placement, entered = start
    steps: list[tuple[int, int, int]] = []
    seen: dict[tuple, int] = {}
    reversals = 0

    for _ in range(MAX_STEPS):
        key = (placement, entered, tuple(sorted(states.items())))
        if key in seen:
            return DriveReport(
                outcome="endless",
                steps=tuple(steps),
                cycle_start=seen[key],
                reversals=reversals,
                visited=frozenset(p for p, _e, _x in steps),
                final_switch_states=dict(states),
            )
        seen[key] = len(steps)

        piece = layout.placements[placement].piece
        stones = stones_by_placement.get(placement, ())

        def finish(outcome: str) -> DriveReport:
            return DriveReport(
                outcome=outcome,
                steps=tuple(steps),
                cycle_start=None,
                reversals=reversals,
                visited=frozenset(p for p, _e, _x in steps) | {placement},
                final_switch_states=dict(states),
            )

        # Mid-piece stones trigger on every pass.  A stone positioned at a port face
        # only acts on trains RUNNING INTO that face; a train setting off away from
        # it starts past the trigger (DUPLO locos are longer than anything beyond),
        # so entering *via* that port leaves it silent.
        if any(sid == STOP_STONE and pos is None for sid, pos in stones):
            return finish("stopped")

        if any(sid == DIRECTION_STONE and pos is None for sid, pos in stones):
            # One reversal per pass: in, trigger, back out the way it came.
            exit_port = entered
            reversals += 1
        else:
            options = [exit_port for exit_port, _route in piece.transit(entered)]
            if not options:
                return finish("derailed")  # entered a dead route (cannot happen today)
            if len(options) > 1:
                # Facing move: follow the tongue (fall back to the first branch if
                # the recorded state isn't one of these options).
                tongue = states.get(placement, min(options))
                exit_port = tongue if tongue in options else min(options)
            else:
                exit_port = options[0]
                if piece.is_junction and len(
                    [e for e, _ in piece.transit(exit_port)]
                ) > 1:
                    # Trailing move: we are pushing through toward a facing port, so
                    # the tongue is forced to the branch we came from.
                    states[placement] = entered
            # Face stones at the port the train is heading for.
            if any(sid == STOP_STONE and pos == exit_port for sid, pos in stones):
                return finish("stopped")
            if any(
                sid == DIRECTION_STONE and pos == exit_port and pos != entered
                for sid, pos in stones
            ):
                exit_port = entered
                reversals += 1

        steps.append((placement, entered, exit_port))

        if exit_port in piece.sealed:
            return finish("buffered")
        link = layout.links.get((placement, exit_port))
        if link is None:
            return finish("derailed")
        placement, entered = link

    raise RuntimeError("drive() exceeded MAX_STEPS; state space should be finite")


def endless_run(
    layout: Layout,
    starts: Iterable[End] | None = None,
) -> DriveReport | None:
    """The first start that yields an endless run, or None.

    Tries both directions of every piece by default.
    """
    if starts is None:
        starts = _all_starts(layout)
    for start in starts:
        report = drive(layout, start=start)
        if report.outcome == "endless":
            return report
    return None


# --------------------------------------------------------------------------------------
# The looping taxonomy
# --------------------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class LoopClassification:
    """Where a layout sits on the looping ladder.

    * ``locally_looping`` -- SOME train placement (position, direction, tongue
      setting) runs forever.
    * ``looping`` -- EVERY placement runs forever, whatever the tongues say.
    * ``completely_looping`` -- looping, and every run covers the whole track.
    * ``perfectly_looping`` -- completely looping, and every run's eventual cycle
      goes over every tile in both directions (hence each infinitely often).

    Each level implies the ones above it.  ``witness`` is an endless start for the
    local property; ``counterexample`` is the (start, tongue setting, outcome) that
    broke the strongest failed universal property.
    """

    locally_looping: bool
    looping: bool
    completely_looping: bool
    perfectly_looping: bool
    runs: int
    witness: tuple[End, dict[int, int]] | None
    counterexample: tuple[End, dict[int, int], str] | None


def _all_starts(layout: Layout) -> list[End]:
    """Every placement of a train: a drivable tile plus a direction of entry.

    Buffers are not start locations -- at 64 mm they cannot hold a locomotive, and
    any real train "at the buffer" stands on the neighbouring piece.
    """
    universe = drivable_universe(layout)
    return [
        (index, port)
        for index, placement in enumerate(layout.placements)
        if index in universe
        for port in range(len(placement.piece.ports))
        if port not in placement.piece.sealed
    ]


def _tongue_assignments(layout: Layout) -> list[dict[int, int]]:
    """Every way the switch tongues could initially point."""
    choices: list[tuple[int, list[int]]] = []
    for index, placement in enumerate(layout.placements):
        piece = placement.piece
        if not piece.is_junction:
            continue
        for port in range(len(piece.ports)):
            options = [exit_port for exit_port, _ in piece.transit(port)]
            if len(options) > 1:
                choices.append((index, options))
                break
    assignments: list[dict[int, int]] = [{}]
    for index, options in choices:
        assignments = [
            {**assignment, index: option}
            for assignment in assignments
            for option in options
        ]
    return assignments


def _cycle_both_directions(report: DriveReport, layout: Layout) -> bool:
    """Does the eventual cycle traverse every drivable tile in both directions?"""
    assert report.cycle_start is not None
    cycle = report.steps[report.cycle_start :]
    per_placement: dict[int, set[tuple[int, int]]] = {}
    for placement, entered, exited in cycle:
        per_placement.setdefault(placement, set()).add((entered, exited))
    universe = drivable_universe(layout)
    if not universe <= set(per_placement):
        return False
    return all(
        any((x, e) in moves for (e, x) in moves)
        for index, moves in per_placement.items()
        if index in universe
    )


def classify(layout: Layout) -> LoopClassification:
    """Place a layout on the looping ladder by exhaustive simulation.

    Every start (piece and direction of travel) is driven under every initial tongue
    assignment; the state space of each run is finite, so each simulation provably
    terminates or cycles.  Sound and complete for the semantics in this module.
    """
    if not layout.placements:
        raise ValueError("nothing to classify")

    starts = _all_starts(layout)
    assignments = _tongue_assignments(layout)
    everything = drivable_universe(layout)

    locally = False
    looping = True
    completely = True
    perfectly = True
    witness: tuple[End, dict[int, int]] | None = None
    counterexample: tuple[End, dict[int, int], str] | None = None
    runs = 0

    for assignment in assignments:
        for start in starts:
            report = drive(layout, start=start, switch_states=assignment)
            runs += 1
            if report.outcome == "endless":
                if not locally:
                    locally = True
                    witness = (start, dict(assignment))
                if not report.visited >= everything and completely:
                    completely = False
                    perfectly = False
                    counterexample = counterexample or (
                        start,
                        dict(assignment),
                        "endless but does not cover the whole track",
                    )
                elif perfectly and not _cycle_both_directions(report, layout):
                    perfectly = False
                    counterexample = counterexample or (
                        start,
                        dict(assignment),
                        "endless but some tile is never traversed both ways",
                    )
            else:
                looping = False
                completely = False
                perfectly = False
                counterexample = counterexample or (
                    start,
                    dict(assignment),
                    report.outcome,
                )

    return LoopClassification(
        locally_looping=locally,
        looping=looping,
        completely_looping=looping and completely,
        perfectly_looping=looping and completely and perfectly,
        runs=runs,
        witness=witness,
        counterexample=counterexample,
    )
