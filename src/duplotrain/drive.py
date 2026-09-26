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

import math
from collections.abc import Iterator, Mapping
from dataclasses import dataclass
from itertools import product

from .layout import End, Layout

__all__ = [
    "ClassificationLimitError", "DriveLimitError", "DriveReport", "DriveTerminal", "drive",
    "LoopClassification", "classify", "drivable_universe",
]

#: Stones that affect motion.
STOP_STONE = "stone_stop"
DIRECTION_STONE = "stone_direction"

#: Safety cap; unreachable in practice because state space is finite and small.
MAX_STEPS = 100_000

#: Bound exhaustive classification before attempting an exponential number of runs.
DEFAULT_MAX_RUNS = 100_000


class DriveLimitError(RuntimeError):
    """A selected train run reached its explicit step budget; no verdict was made."""


class ClassificationLimitError(RuntimeError):
    """The exhaustive classification exceeds its run budget; no verdict was made."""


@dataclass(frozen=True, slots=True)
class DriveTerminal:
    """A stopping event, not an extra traversal in ``DriveReport.steps``.

    ``entry`` is the inward port of the final pass; ``at_port`` is the reached
    face, or None for a midpoint stop. Reasons are stop_stone, buffer, open_end
    and dead_route. Endless runs have no terminal event.
    """

    placement: int
    entry: int
    at_port: int | None
    reason: str


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
    #: (placement, departure port, reached port). A mid-piece bounce returns to
    #: its departure port; a face bounce starts another pass on the SAME piece.
    steps: tuple[tuple[int, int, int], ...]
    cycle_start: int | None  # index into steps where the endless cycle begins
    reversals: int
    visited: frozenset[int]
    final_switch_states: Mapping[int, int]
    terminal: DriveTerminal | None = None

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


def drive(
    layout: Layout,
    start: End | None = None,
    switch_states: Mapping[int, int] | None = None,
    *, max_steps: int = MAX_STEPS,
) -> DriveReport:
    """Simulate a train from *start* until it stops, derails, or provably loops.

    Args:
        layout: the build, including any clipped-on action stones.
        start: ``(placement, port)`` the train ENTERS its first piece through --
            i.e. it travels from that connector into the piece.  Defaults to the
            first piece's first port.
        switch_states: initial tongue positions, ``placement -> exit port``; defaults
            to every tongue aimed at its lowest-numbered branch.
        max_steps: bounded run length; raises DriveLimitError rather than making
            a verdict when the limit is reached. Defaults to MAX_STEPS.
    """
    if type(max_steps) is not int or not 1 <= max_steps <= MAX_STEPS:
        raise ValueError("max_steps must be an integer from 1 to MAX_STEPS")
    if not layout.placements:
        raise ValueError("nothing to drive on")
    if start is None:
        start = (0, layout.placements[0].piece.routes[0].port_a)
    if (not isinstance(start, tuple) or len(start) != 2
            or any(type(value) is not int for value in start)
            or not 0 <= start[0] < len(layout.placements)
            or not 0 <= start[1] < len(layout.placements[start[0]].piece.ports)):
        # A negative alias would index the right piece and then miss every link.
        raise ValueError(f"start {start!r} is not a port of the layout")
    if layout.is_sealed(start):
        raise ValueError("a train cannot enter through a sealed buffer face")

    # As a builder leaves them: every tongue aimed at its lowest-numbered branch.
    states = {index: min(options) for index, options in _tongue_choices(layout)}
    if switch_states:
        states.update({int(k): int(v) for k, v in switch_states.items()})

    # One pass over the stones, in their order: this runs once per drive() call,
    # and classify or a route analysis drive the same layout thousands of times.
    stones_by_placement: dict[int, list[tuple[str, int | None]]] = {}
    for entry in layout.accessories:
        stones_by_placement.setdefault(entry[0], []).append(
            (entry[1], entry[2] if len(entry) > 2 else None))

    placement, entered = start
    steps: list[tuple[int, int, int]] = []
    seen: dict[tuple, int] = {}
    reversals = 0
    # Every step's state holds all tongues, but they change only on trailing
    # moves: share one tuple between changes rather than build one per step.
    tongues = tuple(states[index] for index in sorted(states))

    def finish(
        outcome: str, here: int, reason: str, at_port: int | None = None,
    ) -> DriveReport:
        return DriveReport(
            outcome=outcome,
            steps=tuple(steps),
            cycle_start=None,
            reversals=reversals,
            visited=frozenset(p for p, _e, _x in steps) | {here},
            final_switch_states=dict(states),
            terminal=DriveTerminal(here, entered, at_port, reason),
        )

    while True:
        key = (placement, entered, tongues)
        if key in seen:
            return DriveReport(
                outcome="endless",
                steps=tuple(steps),
                cycle_start=seen[key],
                reversals=reversals,
                visited=frozenset(p for p, _e, _x in steps),
                final_switch_states=dict(states),
            )
        if len(steps) >= max_steps:
            # A cycle closing exactly at the budget is still recognised above.
            raise DriveLimitError(f"drive() exceeded its {max_steps:,}-step budget; "
                                  "no verdict was made")
        seen[key] = len(steps)

        piece = layout.placements[placement].piece
        stones = stones_by_placement.get(placement, ())

        # Mid-piece stones trigger on every pass.  A stone positioned at a port face
        # only acts on trains RUNNING INTO that face; a train setting off away from
        # it starts past the trigger (DUPLO locos are longer than anything beyond),
        # so entering *via* that port leaves it silent.
        if any(sid == STOP_STONE and pos is None for sid, pos in stones):
            return finish("stopped", placement, "stop_stone")

        if any(sid == DIRECTION_STONE and pos is None for sid, pos in stones):
            # One reversal per pass: in, trigger, back out the way it came.
            exit_port = entered
            reversals += 1
        else:
            options = [exit_port for exit_port, _route in piece.transit(entered)]
            if not options:
                return finish("derailed", placement, "dead_route", entered)
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
                    if states.get(placement) != entered:
                        states[placement] = entered
                        tongues = tuple(states[index] for index in sorted(states))
        # A mid-piece reversal also approaches a connector face, including the
        # one we originally entered through. Only the *initial departure* from
        # that face is silent; a return toward it must encounter its stones.
        if any(sid == STOP_STONE and pos == exit_port for sid, pos in stones):
            return finish("stopped", placement, "stop_stone", exit_port)

        steps.append((placement, entered, exit_port))
        if any(sid == DIRECTION_STONE and pos == exit_port for sid, pos in stones):
            # Reflect at this face, without following its external link. The
            # return is a fresh inward pass on this piece, so it visits the
            # midpoint and the other face in order. Keeping it in the normal
            # state machine detects even cycles wholly inside a single piece.
            reversals += 1
            entered = exit_port
            continue

        if exit_port in piece.sealed:
            return finish("buffered", placement, "buffer", exit_port)
        link = layout.links.get((placement, exit_port))
        if link is None:
            return finish("derailed", placement, "open_end", exit_port)
        placement, entered = link


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
      sweeps every tile, each of its routes end to end, in both directions (hence
      each infinitely often).

    Each level implies the ones above it.  ``counterexample`` is the first (start,
    tongue setting, outcome) that breaks the weakest failed universal property -- the
    first "no" down the ladder, so a layout that is not looping gets a run that
    actually ends. It is None when the layout is perfectly looping, and when it has
    no drivable track to place a train on (no runs at all).
    """

    locally_looping: bool
    looping: bool
    completely_looping: bool
    perfectly_looping: bool
    runs: int
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


def _tongue_choices(layout: Layout) -> list[tuple[int, list[int]]]:
    """The independent switch choices, without expanding their Cartesian product."""
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
    return choices


def _tongue_assignments(layout: Layout) -> Iterator[dict[int, int]]:
    """Yield each tongue setting, retaining only one assignment at a time."""
    choices = _tongue_choices(layout)
    indices = [index for index, _ in choices]
    for setting in product(*(options for _, options in choices)):
        yield dict(zip(indices, setting, strict=True))


def _cycle_both_directions(report: DriveReport, layout: Layout) -> bool:
    """Does the eventual cycle sweep every drivable tile, all of it, both ways?

    Each route of a piece has a half at either port. A move ``e -> x`` drives the
    half at ``e`` inward and the half at ``x`` outward; a mid-piece reversal at
    ``e`` drives the half at ``e`` both ways and never reaches the other half.
    Every half of every route through two real connectors must be driven both
    ways: a junction route the cycle never takes, or a half behind a reversal,
    is track the cycle does not sweep.
    """
    assert report.cycle_start is not None
    driven: dict[int, set[tuple[int, int, bool]]] = {}
    for placement, entered, exited in report.steps[report.cycle_start :]:
        halves = driven.setdefault(placement, set())
        if entered == exited:
            for other, _route in layout.placements[placement].piece.transit(entered):
                halves.update(((entered, other, True), (entered, other, False)))
        else:
            halves.update(((entered, exited, True), (exited, entered, False)))
    for index in drivable_universe(layout):
        piece = layout.placements[index].piece
        halves = driven.get(index, set())
        for route in piece.routes:
            a, b = route.port_a, route.port_b
            if a in piece.sealed or b in piece.sealed:
                continue
            if not all((port, other, inward) in halves for port, other in ((a, b), (b, a))
                       for inward in (True, False)):
                return False
    return True


def classify(
    layout: Layout, *, max_runs: int | None = DEFAULT_MAX_RUNS
) -> LoopClassification:
    """Place a layout on the looping ladder by exhaustive simulation.

    Every start (piece and direction of travel) is driven under every initial tongue
    assignment; the state space of each run is finite, so each simulation provably
    terminates or cycles. Sound and complete for the semantics in this module.
    If the required number of runs exceeds ``max_runs``, raise
    :class:`ClassificationLimitError` before simulation, never return a partial
    verdict. Pass a larger budget (or ``None`` for unbounded enumeration) explicitly.
    A single run longer than :func:`drive`'s step budget raises
    :class:`DriveLimitError`, again instead of a verdict. An empty layout raises
    ValueError; one of buffers alone (a closed network can be two buffers face to
    face) has nowhere to place a train, so it makes no runs and no claim.
    """
    if not layout.placements:
        raise ValueError("nothing to classify")
    if max_runs is not None and (type(max_runs) is not int or max_runs < 1):
        raise ValueError("max_runs must be a positive integer or None")
    starts = _all_starts(layout)
    required_runs = len(starts) * math.prod(
        len(options) for _, options in _tongue_choices(layout)
    )
    if max_runs is not None and required_runs > max_runs:
        raise ClassificationLimitError(
            f"classification needs {required_runs:,} runs, exceeding max_runs={max_runs:,}; "
            "increase max_runs to classify this layout"
        )
    assignments = _tongue_assignments(layout)
    everything = drivable_universe(layout)

    locally = False
    looping = True
    completely = True
    perfectly = True
    # The first run breaking each universal property, weakest property first.
    failures: dict[str, tuple[End, dict[int, int], str]] = {}
    runs = 0

    for assignment in assignments:
        for start in starts:
            report = drive(layout, start=start, switch_states=assignment)
            runs += 1
            if report.outcome == "endless":
                locally = True
                if not report.visited >= everything and completely:
                    completely = False
                    perfectly = False
                    failures.setdefault("completely", (
                        start, dict(assignment), "endless but does not cover the whole track",
                    ))
                elif perfectly and not _cycle_both_directions(report, layout):
                    perfectly = False
                    failures.setdefault("perfectly", (
                        start, dict(assignment),
                        "endless but some tile is never traversed both ways",
                    ))
            else:
                looping = False
                completely = False
                perfectly = False
                failures.setdefault("looping", (start, dict(assignment), report.outcome))
    counterexample = (failures.get("looping") or failures.get("completely")
                      or failures.get("perfectly"))

    return LoopClassification(
        locally_looping=locally,
        looping=locally and looping,
        completely_looping=locally and looping and completely,
        perfectly_looping=locally and looping and completely and perfectly,
        runs=runs,
        counterexample=counterexample,
    )
