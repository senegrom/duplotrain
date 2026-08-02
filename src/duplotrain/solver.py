"""Search for closed loops buildable from an inventory of pieces.

The solver walks track outward from an anchored start, depth-first, in exact
arithmetic.  A candidate is *closed* when the walking end returns to the anchor pose
exactly -- same point, same height, same lattice heading -- so there is no tolerance to
tune and no false loops.  Optionally a *slop budget* admits "forced" fits: layouts
whose ends meet on the right heading and height but a few millimetres apart, which the
designed-in play of real DUPLO joints (about a millimetre each) absorbs.  Those are
reported with their gap, never silently blessed.

Symmetry handling
    Anchoring the first piece at the origin quotients away translation and rotation.
    Reflections and starting-point choices are removed afterwards by canonicalising
    each found loop's step signature over rotation and reversal and deduplicating.

Junctions
    A switch placed mid-loop contributes one of its routes; its third port dangles as
    an *open stub* (reported, and scored elsewhere).  The walk may also re-enter an
    already-placed junction through an open stub it meets exactly, which is how
    figure-eights over a crossing emerge without special-casing.

Pruning (all conservative, so the search stays exhaustive):
    * turn feasibility -- the remaining pieces (plus open stubs) must be able to swing
      the heading back to the anchor's;
    * reach -- the remaining pieces must be long enough to get home;
    * collisions -- a placement overlapping existing track is cut immediately.
"""

from __future__ import annotations

import math
import time
from dataclasses import dataclass
from typing import Mapping, Sequence

from .collision import DEFAULT_CLEARANCE, CollisionField
from .exact import Alg
from .geometry import HEADING_STEPS, ORIGIN, Pose, cos_sin
from .layout import Layout
from .pieces import PieceType

__all__ = ["Move", "SolverConfig", "Solution", "SolveStats", "SolveResult", "solve"]


@dataclass(frozen=True, slots=True)
class Move:
    """One geometrically distinct way of appending one piece type to an open end."""

    piece_id: str
    entry: int
    exit: int
    dx: Alg
    dy: Alg
    dz: Alg
    dheading: int


def _traversal_key(piece: PieceType, entry: int, exit_port: int) -> tuple:
    """Physical identity of one traversal: where the piece lands and where the walk exits.

    Two traversals with equal keys place the piece identically in space and continue
    from the same face -- they are the same action, whatever the port labels say.
    """
    frame = piece.frame_for(entry, ORIGIN)
    placed_ports = [
        frame.then(port.pose.x, port.pose.y, port.pose.z, port.pose.heading)
        for port in piece.ports
    ]
    exit_pose = placed_ports[exit_port]
    return (
        frozenset((p.x, p.y, p.z, p.heading) for p in placed_ports),
        (exit_pose.x, exit_pose.y, exit_pose.z, exit_pose.heading),
    )


def _canonical_traversals(piece: PieceType) -> dict[tuple[int, int], tuple[int, int]]:
    """Map every (entry, exit) traversal to its physically-equivalent canonical one.

    A straight's two directions collapse onto one representative; a curve's do not
    (they are the left and the right turn).  Used both to enumerate search moves and
    to normalise loop signatures, so both sides agree on what "the same move" means.
    """
    canon: dict[tuple[int, int], tuple[int, int]] = {}
    by_key: dict[tuple, tuple[int, int]] = {}
    for entry in range(len(piece.ports)):
        for exit_port, _route in piece.transit(entry):
            key = _traversal_key(piece, entry, exit_port)
            representative = by_key.setdefault(key, (entry, exit_port))
            canon[(entry, exit_port)] = representative
    return canon


def _moves_for(piece: PieceType) -> list[Move]:
    """All geometrically distinct traversals of *piece*, one Move per equivalence class."""
    moves: list[Move] = []
    for (entry, exit_port), representative in _canonical_traversals(piece).items():
        if (entry, exit_port) != representative:
            continue
        dx, dy, dz, dheading = piece.exit_delta(entry, exit_port)
        moves.append(Move(piece.id, entry, exit_port, dx, dy, dz, dheading))
    return moves


def _turn_capacity(piece: PieceType) -> int:
    """Largest |heading swing| any single traversal of this piece can contribute."""
    best = 0
    for route in piece.routes:
        a = piece.ports[route.port_a].pose
        b = piece.ports[route.port_b].pose
        turn = (b.heading - a.heading - HEADING_STEPS // 2) % HEADING_STEPS
        if turn >= HEADING_STEPS // 2:
            turn -= HEADING_STEPS
        best = max(best, abs(turn))
    return best


def _max_span(piece: PieceType) -> float:
    best = 0.0
    for i, a in enumerate(piece.ports):
        for b in piece.ports[i + 1 :]:
            best = max(best, a.pose.distance_to(b.pose))
    return best


# --------------------------------------------------------------------------------------
# Step traces and their canonical signatures
# --------------------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class _Place:
    piece_id: str
    entry: int
    exit: int


@dataclass(frozen=True, slots=True)
class _Transit:
    placement: int  # ordinal of the _Place step that created the piece re-entered
    entry: int
    exit: int


def _canonical_signature(
    steps: Sequence[object],
    canon_for: Mapping[str, Mapping[tuple[int, int], tuple[int, int]]],
) -> tuple:
    """Loop signature invariant to starting piece and traversal direction.

    Reversal also covers mirror images: reflecting a closed curve gives the same
    signature as walking it the other way round.  Two normalisations make the
    comparison sound:

    * every (entry, exit) is mapped through the piece's canonical-traversal table, so
      a reversed straight -- mechanically ``(1, 0)`` -- matches the ``(0, 1)`` the
      forward search emits;
    * pieces visited more than once (a figure-eight's crossing) are identified by a
      per-candidate ordinal of *first appearance*, not by which visit the search
      happened to place them on -- rotation and reversal both move that visit around.
    """
    # (instance, pid, entry, exit): `instance` identifies the physical piece -- the
    # placement ordinal for place steps and the referenced ordinal for transits.
    place_pids = [s.piece_id for s in steps if isinstance(s, _Place)]
    visits: list[tuple[int, str, int, int]] = []
    ordinal = 0
    for s in steps:
        if isinstance(s, _Place):
            visits.append((ordinal, s.piece_id, s.entry, s.exit))
            ordinal += 1
        else:
            visits.append((s.placement, place_pids[s.placement], s.entry, s.exit))

    reversed_visits = [(inst, pid, x, e) for (inst, pid, e, x) in reversed(visits)]

    def normalised_rotations(seq: list[tuple[int, str, int, int]]):
        n = len(seq)
        for start in range(n):
            rotated = seq[start:] + seq[:start]
            fresh: dict[int, int] = {}
            out = []
            for inst, pid, entry, exit_ in rotated:
                if inst not in fresh:
                    fresh[inst] = len(fresh)
                entry, exit_ = canon_for[pid].get((entry, exit_), (entry, exit_))
                out.append((fresh[inst], pid, entry, exit_))
            yield tuple(out)

    return min(
        min(normalised_rotations(visits)), min(normalised_rotations(reversed_visits))
    )


def _replay(
    steps: Sequence[object],
    pieces: Mapping[str, PieceType],
    force_final_join: bool,
) -> Layout:
    """Rebuild a full Layout (placements + link graph) from a step trace."""
    layout = Layout()
    cursor: tuple[int, int] | None = None
    first_entry: tuple[int, int] | None = None
    for step in steps:
        if isinstance(step, _Place):
            piece = pieces[step.piece_id]
            if cursor is None:
                frame = piece.frame_for(step.entry, ORIGIN)
                layout, index = layout.with_piece(piece, frame)
                first_entry = (index, step.entry)
            else:
                layout, index = layout.attach(piece, step.entry, cursor)
            cursor = (index, step.exit)
        else:
            assert isinstance(step, _Transit) and cursor is not None
            layout = layout.join(cursor, (step.placement, step.entry), force=force_final_join)
            cursor = (step.placement, step.exit)
    assert cursor is not None and first_entry is not None
    return layout.join(cursor, first_entry, force=force_final_join)


# --------------------------------------------------------------------------------------
# Configuration and results
# --------------------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class SolverConfig:
    """Knobs for the search."""

    slop: float = 0.0  # total closing gap allowed, mm; 0 = exact closures only
    min_pieces: int = 4
    max_results: int = 100
    max_nodes: int = 2_000_000
    use_all_pieces: bool = False
    clearance: float = DEFAULT_CLEARANCE
    collision_spacing: float = 8.0


@dataclass
class SolveStats:
    nodes: int = 0
    closures_found: int = 0  # before deduplication
    pruned_turn: int = 0
    pruned_reach: int = 0
    pruned_collision: int = 0
    duration_s: float = 0.0
    aborted: bool = False  # stopped by max_nodes


@dataclass
class Solution:
    """One distinct closed layout."""

    layout: Layout
    steps: tuple[object, ...]
    gap: float  # closing gap in mm; 0.0 for exact closures
    exact: bool
    open_stubs: int
    signature: tuple

    @property
    def piece_count(self) -> int:
        return len(self.layout)


@dataclass
class SolveResult:
    solutions: list[Solution]
    stats: SolveStats


# --------------------------------------------------------------------------------------
# The search
# --------------------------------------------------------------------------------------


def solve(
    inventory: Mapping[str, int],
    pieces: Mapping[str, PieceType],
    config: SolverConfig | None = None,
) -> SolveResult:
    """Find closed loops buildable from *inventory*.

    Args:
        inventory: piece id -> available count.
        pieces: the catalogue those ids refer to.
        config: search options; the defaults suit a shoebox of track.

    Returns:
        Distinct solutions (deduplicated up to rotation, reflection and starting
        point), each with a rebuilt :class:`~duplotrain.layout.Layout`, plus counters
        describing how the search went.
    """
    cfg = config or SolverConfig()
    for piece_id in inventory:
        if piece_id not in pieces:
            raise ValueError(f"inventory names unknown piece {piece_id!r}")

    counts: dict[str, int] = {pid: n for pid, n in inventory.items() if n > 0}
    piece_ids = sorted(counts)
    moves_by_piece = {pid: _moves_for(pieces[pid]) for pid in piece_ids}
    canon_for = {pid: _canonical_traversals(pieces[pid]) for pid in piece_ids}
    span_of = {pid: _max_span(pieces[pid]) for pid in piece_ids}
    turn_of = {pid: _turn_capacity(pieces[pid]) for pid in piece_ids}
    total_pieces = sum(counts.values())

    # Collision samples, precomputed per (piece, entry, lattice rotation): the world
    # frame of a placement only ever differs by one of 24 rotations plus a translation,
    # so the trig happens once here and the hot loop just adds offsets.
    sample_cache: dict[tuple[str, int, int], list[tuple[float, float, float]]] = {}

    def placement_samples(pid: str, entry: int, frame: Pose) -> list[tuple[float, float, float]]:
        key = (pid, entry, frame.heading)
        base = sample_cache.get(key)
        if base is None:
            piece = pieces[pid]
            c, s = cos_sin(frame.heading)
            cos_t, sin_t = float(c), float(s)
            base = []
            for line in piece.all_centrelines(cfg.collision_spacing):
                for lx, ly, lz in line:
                    base.append((cos_t * lx - sin_t * ly, sin_t * lx + cos_t * ly, lz))
            sample_cache[key] = base
        fx, fy, fz = frame.xyz()
        return [(fx + x, fy + y, fz + z) for x, y, z in base]

    stats = SolveStats()
    field = CollisionField(clearance=cfg.clearance)
    solutions: dict[tuple, Solution] = {}
    started = time.perf_counter()

    # The anchor: the loop's first connector face sits at the origin facing +x.  The
    # walk is closed when the running end returns to exactly this pose.
    anchor = ORIGIN

    steps: list[object] = []
    stubs: list[tuple[int, int, Pose]] = []  # (placement ordinal, port, world pose)
    placements: list[tuple[str, Pose]] = []  # (piece id, world frame), in order

    remaining_span = sum(span_of[pid] * n for pid, n in counts.items())
    remaining_turn = sum(turn_of[pid] * n for pid, n in counts.items())

    def eligible(used: int) -> bool:
        return used >= cfg.min_pieces and (not cfg.use_all_pieces or used == total_pieces)

    def emit(gap: float) -> None:
        stats.closures_found += 1
        signature = _canonical_signature(steps, canon_for)
        if signature in solutions and solutions[signature].gap <= gap:
            return
        layout = _replay(steps, pieces, force_final_join=gap > 0.0)
        solutions[signature] = Solution(
            layout=layout,
            steps=tuple(steps),
            gap=gap,
            exact=gap == 0.0,
            open_stubs=len(layout.open_ends()),
            signature=signature,
        )

    def near(pose: Pose, target: Pose, budget: float) -> float | None:
        """Gap between *pose* and mating *target*, if a joint could absorb it."""
        if (
            (pose.heading - target.heading) % HEADING_STEPS != HEADING_STEPS // 2
            or pose.z != target.z
        ):
            return None
        gap = pose.distance_to(target)
        return gap if gap <= budget + 1e-12 else None

    def dfs(cursor: Pose, used: int, slack_used: float) -> bool:
        """Depth-first over moves; returns False when global limits say stop."""
        nonlocal remaining_span, remaining_turn
        if len(solutions) >= cfg.max_results:
            return False
        stats.nodes += 1
        if stats.nodes > cfg.max_nodes:
            stats.aborted = True
            return False

        # -- closure ------------------------------------------------------------
        if used > 0 and cursor == anchor:
            # The anchor face is occupied by the first piece; whether or not this
            # counts as a result, nothing can continue through it.
            if eligible(used):
                emit(slack_used)
            return True
        if cfg.slop > 0.0 and eligible(used):
            gap = near(cursor, anchor.reversed(), cfg.slop - slack_used)
            if gap is not None and gap > 0.0:
                emit(slack_used + gap)
                # A forced fit does not occupy the anchor; deeper search may still
                # find an exact closure, so carry on.

        if used == total_pieces and not stubs:
            return True

        # -- pruning ------------------------------------------------------------
        home = cursor.distance_to(anchor)
        stub_reach = sum(span_of[placements[s[0]][0]] for s in stubs)
        if home > remaining_span + stub_reach + (cfg.slop - slack_used) + 1e-6:
            stats.pruned_reach += 1
            return True
        need = min(cursor.heading, HEADING_STEPS - cursor.heading)
        stub_turns = sum(turn_of[placements[s[0]][0]] for s in stubs)
        if need > remaining_turn + stub_turns:
            stats.pruned_turn += 1
            return True

        # -- transit an open stub the walk meets (exactly, or within the slop) ----
        if stubs:
            snapshot = list(stubs)
            for i, (pidx, port, pose) in enumerate(snapshot):
                if cursor.connects_to(pose):
                    joint_gap = 0.0
                else:
                    gap = (
                        near(cursor, pose, cfg.slop - slack_used)
                        if cfg.slop > 0.0
                        else None
                    )
                    if gap is None:
                        continue
                    joint_gap = gap
                piece = pieces[placements[pidx][0]]
                frame = placements[pidx][1]
                for exit_port, _route in piece.transit(port):
                    j = next(
                        (
                            k
                            for k, s in enumerate(snapshot)
                            if s[0] == pidx and s[1] == exit_port
                        ),
                        None,
                    )
                    if j is None:  # that exit is not open
                        continue
                    local = piece.ports[exit_port].pose
                    out_pose = frame.then(local.x, local.y, local.z, local.heading)
                    stubs[:] = [s for k, s in enumerate(snapshot) if k not in (i, j)]
                    steps.append(_Transit(pidx, port, exit_port))
                    keep_going = dfs(out_pose, used, slack_used + joint_gap)
                    steps.pop()
                    stubs[:] = snapshot
                    if not keep_going:
                        return False

        # -- place a new piece -----------------------------------------------------
        for pid in piece_ids:
            if counts[pid] == 0:
                continue
            piece = pieces[pid]
            for move in moves_by_piece[pid]:
                next_cursor = cursor.then(move.dx, move.dy, move.dz, move.dheading)

                frame = piece.frame_for(move.entry, cursor)
                pts = placement_samples(pid, move.entry, frame)
                index = len(placements)
                ignore = {index - 1} if placements else set()
                # A move that closes the loop legitimately butts against the first
                # piece; exempt it from colliding with that piece only.  Likewise a
                # move landing on an open stub butts against that stub's piece.
                if placements and eligible(used + 1):
                    if next_cursor == anchor or (
                        cfg.slop > 0.0
                        and near(next_cursor, anchor.reversed(), cfg.slop - slack_used)
                        is not None
                    ):
                        ignore.add(0)
                for stub_index, stub_port, stub_pose in stubs:
                    if next_cursor.connects_to(stub_pose) or (
                        cfg.slop > 0.0
                        and near(next_cursor, stub_pose, cfg.slop - slack_used) is not None
                    ):
                        ignore.add(stub_index)
                if field.clashes(pts, piece.width / 2.0, ignore):
                    stats.pruned_collision += 1
                    continue

                counts[pid] -= 1
                remaining_span -= span_of[pid]
                remaining_turn -= turn_of[pid]
                placements.append((pid, frame))
                field.add(index, pts, piece.width / 2.0)
                new_stubs = 0
                if piece.is_junction:
                    for port_index in range(len(piece.ports)):
                        if port_index in (move.entry, move.exit):
                            continue
                        local = piece.ports[port_index].pose
                        stub_pose = frame.then(local.x, local.y, local.z, local.heading)
                        stubs.append((index, port_index, stub_pose))
                        new_stubs += 1
                steps.append(_Place(pid, move.entry, move.exit))

                keep_going = dfs(next_cursor, used + 1, slack_used)

                steps.pop()
                for _ in range(new_stubs):
                    stubs.pop()
                field.pop()
                placements.pop()
                counts[pid] += 1
                remaining_span += span_of[pid]
                remaining_turn += turn_of[pid]
                if not keep_going:
                    return False
        return True

    dfs(anchor, 0, 0.0)
    stats.duration_s = time.perf_counter() - started

    ordered = sorted(
        solutions.values(),
        key=lambda s: (not s.exact, s.gap, s.open_stubs, -s.piece_count),
    )
    return SolveResult(solutions=ordered, stats=stats)
