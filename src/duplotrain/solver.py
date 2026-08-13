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
from .lattice import ROT_COS_SIN, LatticePoint, LatticePose, from_alg_xy, z_from_alg
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
    """All geometrically distinct traversals of *piece*, one Move per equivalence class.

    Traversals through a sealed face are excluded: a buffer stop can terminate track
    but can never be part of a route, so the loop search never places one.
    """
    moves: list[Move] = []
    for (entry, exit_port), representative in _canonical_traversals(piece).items():
        if (entry, exit_port) != representative:
            continue
        if entry in piece.sealed or exit_port in piece.sealed:
            continue
        dx, dy, dz, dheading = piece.exit_delta(entry, exit_port)
        moves.append(Move(piece.id, entry, exit_port, dx, dy, dz, dheading))
    return moves


def _mirror_ports(piece: PieceType) -> dict[int, int | None]:
    """Map each port to the port its mirror image lands on, if any.

    Local reflection across the piece's x axis; for the switch this pairs left/right
    and fixes the stem.  ``None`` when the piece has no mirror-symmetric counterpart
    for that port (the crossing's diagonal ports), in which case callers skip the
    mirror candidate rather than mis-pair.
    """
    by_pose = {
        (p.pose.x, p.pose.y, p.pose.z, p.pose.heading): i
        for i, p in enumerate(piece.ports)
    }
    return {
        i: by_pose.get(
            (p.pose.x, -p.pose.y, p.pose.z, (-p.pose.heading) % HEADING_STEPS)
        )
        for i, p in enumerate(piece.ports)
    }


def _mirror_traversals(piece: PieceType) -> dict[tuple[int, int], tuple[int, int] | None]:
    """Map each traversal to the traversal that produces its mirror image, if any.

    Derived from geometry rather than a hand-kept handedness table: a traversal's
    anchored placement is reflected across the axis of approach (y -> -y, heading
    negated) and the traversal of the same piece landing on exactly that reflected
    geometry is looked up.  This automatically pairs a curve's left and right
    readings, a switch's two branches, and even a crossing's two routes; a genuinely
    single-handed piece maps to ``None`` (its loops have no buildable mirror twin).
    """
    by_key: dict[tuple, tuple[int, int]] = {}
    traversals: list[tuple[int, int]] = []
    for entry in range(len(piece.ports)):
        for exit_port, _route in piece.transit(entry):
            key = _traversal_key(piece, entry, exit_port)
            by_key.setdefault(key, (entry, exit_port))
            traversals.append((entry, exit_port))

    canon = _canonical_traversals(piece)
    mirror: dict[tuple[int, int], tuple[int, int] | None] = {}
    for entry, exit_port in traversals:
        ports_key, exit_key = _traversal_key(piece, entry, exit_port)
        mirrored_key = (
            frozenset((x, -y, z, (-h) % HEADING_STEPS) for (x, y, z, h) in ports_key),
            (exit_key[0], -exit_key[1], exit_key[2], (-exit_key[3]) % HEADING_STEPS),
        )
        partner = by_key.get(mirrored_key)
        mirror[(entry, exit_port)] = canon[partner] if partner is not None else None
    return mirror


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
# Pose engines: the same search over two arithmetic backends
#
# The "field" engine is the general one: exact Q(sqrt2, sqrt3) coordinates, any
# 15-degree heading.  The "lattice" engine handles what every real DUPLO piece
# actually needs -- 30-degree turns, twentieth-millimetre lengths -- with pure
# integer arithmetic (see duplotrain.lattice), roughly an order of magnitude faster.
# solve() compiles the catalogue for the lattice engine and silently falls back to
# the field when anything (a user piece, an odd heading) doesn't fit.
# --------------------------------------------------------------------------------------


def _pose_to_lattice(pose: Pose) -> LatticePose | None:
    if pose.heading % 2:
        return None
    point = from_alg_xy(pose.x, pose.y)
    z = z_from_alg(pose.z)
    if point is None or z is None:
        return None
    return LatticePose(point, z, pose.heading // 2)


class _FieldEngine:
    """Pose operations over exact field arithmetic (the original implementation)."""

    name = "field"

    def __init__(
        self,
        anchor: Pose,
        start_cursor: Pose,
        pieces: Mapping[str, PieceType],
        moves_by_piece: Mapping[str, list[Move]],
    ) -> None:
        self.anchor = anchor
        self._mate = anchor.reversed()
        self.start_cursor = start_cursor
        self._pieces = pieces
        ax, ay = anchor.xy()
        theta = math.radians(anchor.degrees)
        # The walk must ARRIVE at the anchor going its way; aim the search heuristic
        # one straight behind it so candidates line up from the approachable side.
        self._approach = (ax - 128.0 * math.cos(theta), ay - 128.0 * math.sin(theta))
        self.moves = {
            pid: [
                (m.entry, m.exit, self._make_apply(m.dx, m.dy, m.dz, m.dheading))
                for m in moves
            ]
            for pid, moves in moves_by_piece.items()
        }
        self._frames0 = {
            (pid, entry): pieces[pid].frame_for(entry, ORIGIN)
            for pid, moves in moves_by_piece.items()
            for entry in {m.entry for m in moves}
        }

    @staticmethod
    def _make_apply(dx: Alg, dy: Alg, dz: Alg, dheading: int):
        def apply(cursor: Pose) -> Pose:
            return cursor.then(dx, dy, dz, dheading)

        return apply

    def convert(self, pose: Pose) -> Pose:
        return pose

    def frame(self, pid: str, entry: int, cursor: Pose) -> Pose:
        f0 = self._frames0.get((pid, entry))
        if f0 is None:
            f0 = self._pieces[pid].frame_for(entry, ORIGIN)
            self._frames0[(pid, entry)] = f0
        return cursor.then(f0.x, f0.y, f0.z, f0.heading)

    def frame_floats(self, frame: Pose) -> tuple[int, float, float, float, float, float]:
        c, s = cos_sin(frame.heading)
        fx, fy, fz = frame.xyz()
        return (frame.heading, fx, fy, fz, float(c), float(s))

    def port_world(self, pid: str, port: int, frame: Pose) -> Pose:
        local = self._pieces[pid].ports[port].pose
        return frame.then(local.x, local.y, local.z, local.heading)

    def closes(self, cursor: Pose) -> bool:
        return cursor == self.anchor

    def near_anchor(self, cursor: Pose, budget: float) -> float | None:
        return self.near_pose(cursor, self._mate, budget)

    def connects(self, cursor: Pose, pose: Pose) -> bool:
        return cursor.connects_to(pose)

    def near_pose(self, cursor: Pose, pose: Pose, budget: float) -> float | None:
        if (
            (cursor.heading - pose.heading) % HEADING_STEPS != HEADING_STEPS // 2
            or cursor.z != pose.z
        ):
            return None
        gap = cursor.distance_to(pose)
        return gap if gap <= budget + 1e-12 else None

    def dist(self, a: Pose, b: Pose) -> float:
        return a.distance_to(b)

    def dist_home(self, cursor: Pose) -> float:
        return cursor.distance_to(self.anchor)

    def heur_dist(self, cursor: Pose) -> float:
        x, y = cursor.xy()
        ax, ay = self._approach
        return math.hypot(x - ax, y - ay) + 2.5 * abs(
            float(cursor.z) - float(self.anchor.z)
        )

    def need_turn24(self, cursor: Pose) -> int:
        gap = (cursor.heading - self.anchor.heading) % HEADING_STEPS
        return min(gap, HEADING_STEPS - gap)

    def stub_need24(self, cursor: Pose, stub_pose: Pose) -> int:
        gap = (cursor.heading - stub_pose.heading - HEADING_STEPS // 2) % HEADING_STEPS
        return min(gap, HEADING_STEPS - gap)


_SQRT3 = math.sqrt(3.0)


def _flat(pose: LatticePose) -> tuple[int, int, int, int, int, int]:
    """LatticePose as a plain int 6-tuple (a, b, c, d, z, heading12)."""
    return (*pose.p.key(), pose.z, pose.heading)


def _flat_xy(pose: tuple) -> tuple[float, float]:
    a, b, c, d, _z, _h = pose
    return (
        (a + (b * _SQRT3 + c) / 2.0) / 20.0,
        (d + (c * _SQRT3 + b) / 2.0) / 20.0,
    )


class _LatticeEngine:
    """Pose operations over the integer 30-degree lattice.

    Poses are plain int 6-tuples ``(a, b, c, d, z, heading12)`` and every move/frame/
    port delta is precomputed for all 12 headings, so the hot path is tuple adds and
    tuple compares -- no objects, no rotation loops.  Built by
    :func:`_compile_lattice`, which returns None (-> field fallback) when the
    catalogue or base layout doesn't fit the lattice.
    """

    name = "lattice"

    def __init__(
        self,
        anchor: LatticePose,
        start_cursor: LatticePose,
        moves: Mapping[str, list[tuple]],
        frames0: Mapping[tuple[str, int], tuple],
        port_locals: Mapping[tuple[str, int], tuple],
    ) -> None:
        self.anchor = _flat(anchor)
        self.start_cursor = _flat(start_cursor)
        self.moves = moves
        self._frames0 = frames0  # (pid, entry) -> (rotated deltas x12, dz, turn)
        self._port_locals = port_locals
        ax, ay = _flat_xy(self.anchor)
        theta = math.radians(self.anchor[5] * 30)
        self._approach = (ax - 128.0 * math.cos(theta), ay - 128.0 * math.sin(theta))

    @staticmethod
    def _advance(cursor: tuple, rotated: tuple, dz: int, turn: int) -> tuple:
        a, b, c, d, z, h = cursor
        da, db, dc, dd = rotated[h]
        return (a + da, b + db, c + dc, d + dd, z + dz, (h + turn) % 12)

    def frame(self, pid: str, entry: int, cursor: tuple) -> tuple:
        rotated, dz, turn = self._frames0[(pid, entry)]
        return self._advance(cursor, rotated, dz, turn)

    def frame_floats(self, frame: tuple) -> tuple[int, float, float, float, float, float]:
        fx, fy = _flat_xy(frame)
        c, s = ROT_COS_SIN[frame[5]]
        return (frame[5], fx, fy, frame[4] / 20.0, c, s)

    def port_world(self, pid: str, port: int, frame: tuple) -> tuple:
        rotated, dz, turn = self._port_locals[(pid, port)]
        return self._advance(frame, rotated, dz, turn)

    def closes(self, cursor: tuple) -> bool:
        return cursor == self.anchor

    def near_anchor(self, cursor: tuple, budget: float) -> float | None:
        anchor = self.anchor
        if cursor[5] != anchor[5] or cursor[4] != anchor[4]:
            return None
        gap = self.dist(cursor, anchor)
        return gap if gap <= budget + 1e-12 else None

    def connects(self, cursor: tuple, pose: tuple) -> bool:
        return (
            cursor[0] == pose[0]
            and cursor[1] == pose[1]
            and cursor[2] == pose[2]
            and cursor[3] == pose[3]
            and cursor[4] == pose[4]
            and (cursor[5] - pose[5]) % 12 == 6
        )

    def near_pose(self, cursor: tuple, pose: tuple, budget: float) -> float | None:
        if (cursor[5] - pose[5]) % 12 != 6 or cursor[4] != pose[4]:
            return None
        gap = self.dist(cursor, pose)
        return gap if gap <= budget + 1e-12 else None

    def dist(self, a: tuple, b: tuple) -> float:
        ax, ay = _flat_xy(a)
        bx, by = _flat_xy(b)
        return math.hypot(ax - bx, ay - by)

    def dist_home(self, cursor: tuple) -> float:
        return self.dist(cursor, self.anchor)

    def heur_dist(self, cursor: tuple) -> float:
        x, y = _flat_xy(cursor)
        ax, ay = self._approach
        return math.hypot(x - ax, y - ay) + 0.125 * abs(cursor[4] - self.anchor[4])

    def need_turn24(self, cursor: tuple) -> int:
        gap = (cursor[5] - self.anchor[5]) % 12
        return 2 * min(gap, 12 - gap)

    def stub_need24(self, cursor: tuple, stub_pose: tuple) -> int:
        gap = (cursor[5] - stub_pose[5] - 6) % 12
        return 2 * min(gap, 12 - gap)


def _compile_lattice(
    anchor: Pose,
    start_cursor: Pose,
    pieces: Mapping[str, PieceType],
    moves_by_piece: Mapping[str, list[Move]],
) -> _LatticeEngine | None:
    anchor_l = _pose_to_lattice(anchor)
    start_l = _pose_to_lattice(start_cursor)
    if anchor_l is None or start_l is None:
        return None

    moves: dict[str, list[tuple]] = {}
    frames0: dict[tuple[str, int], tuple] = {}
    port_locals: dict[tuple[str, int], tuple] = {}

    def rotations_of(point: LatticePoint) -> tuple:
        return tuple(point.rotated(h).key() for h in range(12))

    def as_delta(pose: LatticePose) -> tuple:
        return (rotations_of(pose.p), pose.z, pose.heading)

    def make_apply(rot12: tuple, dz: int, turn: int):
        def apply(cursor: tuple) -> tuple:
            a, b, c, d, z, h = cursor
            da, db, dc, dd = rot12[h]
            return (a + da, b + db, c + dc, d + dd, z + dz, (h + turn) % 12)

        return apply

    for pid, piece in pieces.items():
        for port_index, port in enumerate(piece.ports):
            local = _pose_to_lattice(port.pose)
            if local is None:
                return None
            port_locals[(pid, port_index)] = as_delta(local)
        # Frames for every unsealed entry: the network enumerator attaches pieces
        # (a buffer, say) that contribute no traversal moves at all.
        for entry in range(len(piece.ports)):
            if entry in piece.sealed:
                continue
            f0 = _pose_to_lattice(piece.frame_for(entry, ORIGIN))
            if f0 is None:
                return None
            frames0[(pid, entry)] = as_delta(f0)

    for pid, piece_moves in moves_by_piece.items():
        compiled = []
        for m in piece_moves:
            if m.dheading % 2:
                return None
            delta = from_alg_xy(m.dx, m.dy)
            dz = z_from_alg(m.dz)
            if delta is None or dz is None:
                return None
            compiled.append(
                (m.entry, m.exit, make_apply(rotations_of(delta), dz, m.dheading // 2))
            )
        moves[pid] = compiled

    return _LatticeEngine(anchor_l, start_l, moves, frames0, port_locals)


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
    base_pids: Sequence[str] = (),
    cyclic: bool = True,
    mirror_for: Mapping[str, Mapping[tuple[int, int], tuple[int, int] | None]] | None = None,
    closing_stub: tuple[int, int] | None = None,
    port_mirror_for: Mapping[str, Mapping[int, int | None]] | None = None,
) -> tuple:
    """Loop signature invariant to starting piece, direction, and reflection.

    Three normalisations make the comparison sound:

    * every (entry, exit) is mapped through the piece's canonical-traversal table, so
      a reversed straight -- mechanically ``(1, 0)`` -- matches the ``(0, 1)`` the
      forward search emits;
    * pieces visited more than once (a figure-eight's crossing) are identified by a
      per-candidate ordinal of *first appearance*, not by which visit the search
      happened to place them on -- rotation and reversal both move that visit around;
    * the mirror image is generated explicitly via each piece's mirror-traversal
      table.  (Walking a chiral loop backwards is NOT its mirror image -- reversal
      alone only collapses reflection twins of loops that are themselves symmetric.)

    Completion searches (growing between two fixed ends of an existing layout) pass
    ``cyclic=False``: their step sequences are paths anchored to the base, so
    rotation, reversal and mirroring would all conflate genuinely different
    completions.  ``base_pids`` names the pre-existing placements so transits through
    them resolve to a piece id.
    """
    # (instance, pid, entry, exit): `instance` identifies the physical piece.  Instance
    # ids share one space: base placements keep their layout index; grown pieces get
    # n_base + (placement ordinal); transits reference either kind directly.
    n_base = len(base_pids)
    place_pids = [s.piece_id for s in steps if isinstance(s, _Place)]

    def pid_of(instance: int) -> str:
        return base_pids[instance] if instance < n_base else place_pids[instance - n_base]

    visits: list[tuple[int, str, int, int]] = []
    ordinal = 0
    for s in steps:
        if isinstance(s, _Place):
            visits.append((n_base + ordinal, s.piece_id, s.entry, s.exit))
            ordinal += 1
        else:
            visits.append((s.placement, pid_of(s.placement), s.entry, s.exit))

    def normalise(seq: list[tuple[int, str, int, int]]) -> tuple:
        fresh: dict[int, int] = {}
        out = []
        for inst, pid, entry, exit_ in seq:
            if inst not in fresh:
                fresh[inst] = len(fresh)
            table = canon_for.get(pid)
            if table is not None:
                entry, exit_ = table.get((entry, exit_), (entry, exit_))
            out.append((fresh[inst], pid, entry, exit_))
        return tuple(out)

    def mirror_of(seq: list[tuple[int, str, int, int]]):
        out: list[tuple[int, str, int, int]] = []
        for inst, pid, entry, exit_ in seq:
            partner = mirror_for.get(pid, {}).get((entry, exit_)) if mirror_for else None
            if partner is None:
                return None  # a single-handed piece: no buildable mirror twin
            out.append((inst, pid, partner[0], partner[1]))
        return out

    if closing_stub is not None:
        # A reversing loop is anchored at its open tail and closes into a junction
        # stub: rotation and reversal are not symmetries, only reflection is.  The
        # closing joint is part of the identity, appended as a final token.
        stub_inst, stub_port = closing_stub

        def with_join(seq, port: int) -> tuple:
            fresh: dict[int, int] = {}
            out = []
            for inst, pid, entry, exit_ in seq:
                if inst not in fresh:
                    fresh[inst] = len(fresh)
                table = canon_for.get(pid)
                if table is not None:
                    entry, exit_ = table.get((entry, exit_), (entry, exit_))
                out.append((fresh[inst], pid, entry, exit_))
            ordinal = fresh.setdefault(stub_inst, len(fresh))
            return tuple(out) + (("J", ordinal, port),)

        candidates = [with_join(visits, stub_port)]
        mirrored = mirror_of(visits)
        if mirrored is not None and port_mirror_for is not None:
            stub_pid = pid_of(stub_inst)
            mirrored_port = port_mirror_for.get(stub_pid, {}).get(stub_port)
            if mirrored_port is not None:
                candidates.append(with_join(mirrored, mirrored_port))
        return min(candidates)

    if not cyclic:
        return normalise(visits)

    sequences = [visits, [(inst, pid, x, e) for (inst, pid, e, x) in reversed(visits)]]
    mirrored = mirror_of(visits)
    if mirrored is not None:
        sequences.append(mirrored)
        sequences.append([(inst, pid, x, e) for (inst, pid, e, x) in reversed(mirrored)])

    n = len(visits)
    return min(
        normalise(seq[start:] + seq[:start]) for seq in sequences for start in range(n)
    )


def _replay(
    steps: Sequence[object],
    pieces: Mapping[str, PieceType],
    force_final_join: bool,
    base: Layout | None = None,
    grow_from: tuple[int, int] | None = None,
    close_onto: tuple[int, int] | None = None,
    final_target: tuple[int, int] | None = None,
) -> Layout:
    """Rebuild a full Layout (placements + link graph) from a step trace.

    Loop mode (no *base*): the first placed piece plugs onto a virtual face at the
    origin and the trace must return there.  Completion mode: the trace grows from the
    open end *grow_from* of *base* and finally joins onto *close_onto*.  A reversing
    loop overrides either with *final_target*: the walk's end joins that junction stub
    instead, leaving the anchor face open as the tail.
    """
    layout = base if base is not None else Layout()
    cursor = grow_from
    target: tuple[int, int] | None = close_onto
    for step in steps:
        if isinstance(step, _Place):
            piece = pieces[step.piece_id]
            if cursor is None:
                frame = piece.frame_for(step.entry, ORIGIN)
                layout, index = layout.with_piece(piece, frame)
                target = (index, step.entry)
            else:
                layout, index = layout.attach(piece, step.entry, cursor)
            cursor = (index, step.exit)
        else:
            assert isinstance(step, _Transit) and cursor is not None
            layout = layout.join(cursor, (step.placement, step.entry), force=force_final_join)
            cursor = (step.placement, step.exit)
    if final_target is not None:
        target = final_target
    assert cursor is not None and target is not None
    return layout.join(cursor, target, force=force_final_join)


def _solution_overlaps(
    layout: Layout, n_base: int, clearance: float, spacing: float
) -> bool:
    """Independent overlap audit of a finished solution.

    The search prunes colliding placements as it goes, but its exemption
    bookkeeping is intricate (anchors, stubs, transits, forced fits).  This
    checks the replayed layout against its real link graph: a solution is
    rejected if any piece the search added (index >= *n_base*) overlaps a
    placement it is not directly joined to.  Contact already present inside the
    base layout is the caller's business and stays exempt.
    """
    neighbours: dict[int, set[int]] = {}
    for (ai, _ap), (bi, _bp) in layout.links.items():
        neighbours.setdefault(ai, set()).add(bi)
    check = CollisionField(clearance=clearance)
    for index, placement in enumerate(layout.placements):
        pts = [p for line in placement.centrelines(spacing) for p in line]
        half = placement.piece.width / 2.0
        arch = placement.piece.underpass
        if index >= n_base and check.clashes(
            pts, half, neighbours.get(index, set()), underpass=arch
        ):
            return True
        check.add(index, pts, half, underpass=arch)
    return False


# --------------------------------------------------------------------------------------
# Configuration and results
# --------------------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class SolverConfig:
    """Knobs for the search."""

    slop: float = 0.0  # total closing gap allowed, mm; 0 = exact closures only
    min_pieces: int = 4
    #: Upper bound on pieces placed (loop length / grown completion length).  With a
    #: huge inventory an unbounded depth-first dive is the enemy: a 300 mm gap needs
    #: a dozen pieces, not two hundred.  None = no bound.
    max_pieces: int | None = None
    max_results: int = 100
    max_nodes: int = 2_000_000
    use_all_pieces: bool = False
    clearance: float = DEFAULT_CLEARANCE
    collision_spacing: float = 8.0
    #: Also accept layouts that close into an open junction stub instead of the
    #: anchor -- a teardrop whose walk ends against its own switch's other branch.
    #: The train then always exits through the stem toward the open tail, so running
    #: such a layout endlessly needs a direction-change action stone on that tail
    #: (and switches the train can trail through, which the modern ones are).
    reversing_loops: bool = False
    #: Called with the node count every few thousand nodes -- a liveness heartbeat
    #: for UIs sitting on a long search.  Exceptions from it are the caller's problem.
    progress: object = None
    #: Arithmetic backend: "auto" uses the integer lattice engine whenever the whole
    #: problem fits the 30-degree grid (every built-in piece does) and falls back to
    #: the general field otherwise; "lattice"/"field" force one, for tests.
    engine: str = "auto"


@dataclass
class SolveStats:
    nodes: int = 0
    closures_found: int = 0  # before deduplication
    pruned_turn: int = 0
    pruned_reach: int = 0
    pruned_collision: int = 0
    duration_s: float = 0.0
    aborted: bool = False  # stopped by max_nodes
    engine: str = ""  # which arithmetic backend ran
    #: Solutions rejected by the final independent overlap audit.  Always 0 unless
    #: a search-time exemption let an overlap slip through -- a bug worth reporting.
    dropped_overlap: int = 0


@dataclass
class Solution:
    """One distinct closed layout."""

    layout: Layout
    steps: tuple[object, ...]
    gap: float  # closing gap in mm; 0.0 for exact closures
    exact: bool
    open_stubs: int
    signature: tuple
    #: "loop" -- an ordinary closed circuit; "reversing" -- closes into a junction
    #: stub, drivable endlessly only with a direction-change stone on the open tail.
    kind: str = "loop"

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
    *,
    base: Layout | None = None,
    grow_from: tuple[int, int] | None = None,
    close_onto: tuple[int, int] | None = None,
) -> SolveResult:
    """Find closed loops buildable from *inventory*.

    Loop mode (default): search fresh loops from scratch.

    Completion mode (*base* given): keep every placed piece of *base* where it is and
    search for ways to connect its open end *grow_from* to its open end *close_onto*
    using the inventory -- the "I built this much by hand, close it for me" question.
    When the two ends are omitted they default to the last and first open end of the
    base layout.  Base pieces participate fully: they collide, and open branches of
    base junctions may be transited through.

    Args:
        inventory: piece id -> available count (the *spare* pieces, in completion mode).
        pieces: the catalogue those ids refer to.
        config: search options; the defaults suit a shoebox of track.  In completion
            mode ``min_pieces`` counts only newly grown pieces, so callers closing a
            small gap will want ``min_pieces=1``.
        base: existing layout to complete.
        grow_from: open end of *base* the new track grows out of.
        close_onto: open end of *base* the new track must finally mate with.

    Returns:
        Distinct solutions (loop mode: deduplicated up to rotation, reflection and
        starting point), each with a rebuilt :class:`~duplotrain.layout.Layout`, plus
        counters describing how the search went.
    """
    cfg = config or SolverConfig()
    for piece_id in inventory:
        if piece_id not in pieces:
            raise ValueError(f"inventory names unknown piece {piece_id!r}")

    if base is None:
        if grow_from is not None or close_onto is not None:
            raise ValueError("grow_from/close_onto only make sense with a base layout")
        base_pids: list[str] = []
    else:
        opens = base.open_ends()
        if grow_from is None and close_onto is None and len(opens) >= 2:
            grow_from, close_onto = opens[-1], opens[0]
        if grow_from is None or close_onto is None or grow_from == close_onto:
            raise ValueError("completion needs two distinct open ends of the base layout")
        for end in (grow_from, close_onto):
            if end in base.links:
                raise ValueError(f"end {end} of the base layout is already connected")
        for end in (grow_from, close_onto):
            if base.is_sealed(end):
                raise ValueError(f"end {end} is a sealed buffer face; track cannot grow there")
        if base.pose_of(grow_from).connects_to(base.pose_of(close_onto)):
            raise ValueError(
                "those ends already mate exactly; join them with Layout.join instead"
            )
        base_pids = [p.piece.id for p in base.placements]

    counts: dict[str, int] = {pid: n for pid, n in inventory.items() if n > 0}
    piece_ids = sorted(counts)
    piece_obj: dict[str, PieceType] = {pid: pieces[pid] for pid in piece_ids}
    if base is not None:
        for placement in base.placements:
            piece_obj.setdefault(placement.piece.id, placement.piece)
    moves_by_piece = {pid: _moves_for(pieces[pid]) for pid in piece_ids}
    # Tie-break rank for move ordering: with a broad inventory many moves share a
    # heuristic score (a level crossing "ahead" lands exactly where a straight does);
    # plain running track must win those ties or the search drowns in exotic-piece
    # subtrees.  0 = plain flat track, 1 = flat with quirks (overhang), 2 = junctions
    # and anything that changes elevation.
    def _rank(pid: str) -> int:
        piece = pieces[pid]
        if piece.is_junction:
            return 2
        if any(m.dz for m in moves_by_piece[pid]):
            return 2
        if piece.end_overhang > 0:
            return 1
        return 0

    piece_rank = {pid: _rank(pid) for pid in piece_ids}
    canon_for = {pid: _canonical_traversals(p) for pid, p in piece_obj.items()}
    mirror_for = {pid: _mirror_traversals(p) for pid, p in piece_obj.items()}
    port_mirror_for = {pid: _mirror_ports(p) for pid, p in piece_obj.items()}
    span_of = {pid: _max_span(p) for pid, p in piece_obj.items()}
    turn_of = {pid: _turn_capacity(p) for pid, p in piece_obj.items()}
    overhang_of = {pid: p.end_overhang for pid, p in piece_obj.items()}
    total_pieces = sum(counts.values())

    # Collision samples, precomputed per (piece, entry, frame rotation): the world
    # frame of a placement only ever differs by one of finitely many rotations plus a
    # translation, so the trig happens once here and the hot loop just adds offsets.
    sample_cache: dict[tuple[str, int, int], list[tuple[float, float, float]]] = {}

    def placement_samples(
        pid: str,
        entry: int,
        hkey: int,
        cos_t: float,
        sin_t: float,
        fx: float,
        fy: float,
        fz: float,
    ) -> list[tuple[float, float, float]]:
        key = (pid, entry, hkey)
        base_pts = sample_cache.get(key)
        if base_pts is None:
            piece = pieces[pid]
            base_pts = []
            for line in piece.all_centrelines(cfg.collision_spacing):
                for lx, ly, lz in line:
                    base_pts.append(
                        (cos_t * lx - sin_t * ly, sin_t * lx + cos_t * ly, lz)
                    )
            sample_cache[key] = base_pts
        return [(fx + x, fy + y, fz + z) for x, y, z in base_pts]

    stats = SolveStats()
    field = CollisionField(clearance=cfg.clearance)
    solutions: dict[tuple, Solution] = {}
    started = time.perf_counter()

    # The anchor is the pose the walk must reach to close.  Loop mode: the first
    # connector face sits at the origin facing +x and the walk returns to it.
    # Completion mode: the walk starts at the grow end's outward pose and closes when
    # it faces the target end -- i.e. reaches that end's pose reversed.
    if base is None:
        anchor = ORIGIN
        start_cursor = anchor
        start_prev: int | None = None
        anchor_index = 0  # the first placed piece
    else:
        anchor = base.pose_of(close_onto).reversed()
        start_cursor = base.pose_of(grow_from)
        start_prev = grow_from[0]
        anchor_index = close_onto[0]

    # Pick the arithmetic backend: integer lattice when everything fits, else field.
    if cfg.engine not in ("auto", "lattice", "field"):
        raise ValueError(f"unknown engine {cfg.engine!r}")
    base_stub_poses: dict[tuple[int, int], object] = {}
    eng = None
    if cfg.engine in ("auto", "lattice"):
        eng = _compile_lattice(anchor, start_cursor, piece_obj, moves_by_piece)
        if eng is not None and base is not None:
            # Base stub poses and nothing else still need converting; do it eagerly
            # so a single off-lattice base placement demotes cleanly to the field.
            for index, placement in enumerate(base.placements):
                if not placement.piece.is_junction:
                    continue
                for port in range(len(placement.piece.ports)):
                    converted = _pose_to_lattice(placement.port_pose(port))
                    if converted is None:
                        eng = None
                        break
                    base_stub_poses[(index, port)] = _flat(converted)
                if eng is None:
                    break
    if eng is None:
        if cfg.engine == "lattice":
            raise ValueError("problem does not fit the integer lattice engine")
        eng = _FieldEngine(anchor, start_cursor, piece_obj, moves_by_piece)
        if base is not None:
            base_stub_poses = {
                (index, port): placement.port_pose(port)
                for index, placement in enumerate(base.placements)
                if placement.piece.is_junction
                for port in range(len(placement.piece.ports))
            }
    stats.engine = eng.name

    steps: list[object] = []
    stubs: list[tuple[int, int, object]] = []  # (placement index, port, engine pose)
    placements: list[tuple[str, object]] = []  # (piece id, engine frame), in order

    if base is not None:
        for index, placement in enumerate(base.placements):
            placements.append((placement.piece.id, None))  # base frames never re-used
            pts = [
                p
                for line in placement.centrelines(cfg.collision_spacing)
                for p in line
            ]
            field.add(
                index,
                pts,
                placement.piece.width / 2.0,
                underpass=placement.piece.underpass,
            )
            if placement.piece.is_junction:
                for port in range(len(placement.piece.ports)):
                    end = (index, port)
                    if end in base.links or end in (grow_from, close_onto):
                        continue
                    if port in placement.piece.sealed:
                        continue
                    stubs.append((index, port, base_stub_poses[(index, port)]))

    remaining_span = sum(span_of[pid] * n for pid, n in counts.items())
    remaining_turn = sum(turn_of[pid] * n for pid, n in counts.items())

    # Admissible per-piece bounds for the completion-mode IDA* contour: one piece
    # advances at most max_span_any millimetres and swings at most max_turn_any
    # heading steps, so pieces-needed >= max(dist/span, need/turn).
    max_span_any = max(span_of.values(), default=1.0) or 1.0
    max_turn_any = max(turn_of.values(), default=0)

    def eligible(used: int) -> bool:
        return used >= cfg.min_pieces and (not cfg.use_all_pieces or used == total_pieces)

    def emit(gap: float, reversing_target: tuple[int, int] | None = None) -> None:
        stats.closures_found += 1
        signature = _canonical_signature(
            steps,
            canon_for,
            base_pids,
            cyclic=base is None,
            mirror_for=mirror_for,
            closing_stub=reversing_target,
            port_mirror_for=port_mirror_for,
        )
        if signature in solutions and solutions[signature].gap <= gap:
            return
        layout = _replay(
            steps,
            pieces,
            force_final_join=gap > 0.0,
            base=base,
            grow_from=grow_from,
            close_onto=close_onto,
            final_target=reversing_target,
        )
        if _solution_overlaps(
            layout, len(base_pids), cfg.clearance, cfg.collision_spacing
        ):
            stats.dropped_overlap += 1
            return
        solutions[signature] = Solution(
            layout=layout,
            steps=tuple(steps),
            gap=gap,
            exact=gap == 0.0,
            open_stubs=len(layout.connectable_ends()),
            signature=signature,
            kind="loop" if reversing_target is None else "reversing",
        )

    def dfs(cursor, used: int, slack_used: float, prev_index: int | None) -> bool:
        """Depth-first over moves; returns False when global limits say stop.

        *prev_index* is the placement owning the connector the walk currently stands
        on -- the last piece placed, or the junction just transited -- which the next
        placement legitimately butts against.
        """
        nonlocal remaining_span, remaining_turn
        if len(solutions) >= cfg.max_results:
            return False
        stats.nodes += 1
        if stats.nodes > cfg.max_nodes:
            stats.aborted = True
            return False
        if cfg.progress is not None and stats.nodes % 4096 == 0:
            cfg.progress(stats.nodes)

        # -- closure ------------------------------------------------------------
        def closing_link_legal() -> bool:
            # The final join links the piece the cursor stands on to the anchor piece;
            # two overhanging plates cannot share that joint.
            if prev_index is None or not placements:
                return True
            return not (
                overhang_of[placements[prev_index][0]] > 0
                and overhang_of[placements[anchor_index][0]] > 0
            )

        if used > 0 and eng.closes(cursor):
            # The anchor face is occupied; whether or not this counts as a result,
            # nothing can continue through it.
            if eligible(used) and closing_link_legal():
                emit(slack_used)
            return True
        if cfg.slop > 0.0 and eligible(used) and closing_link_legal():
            gap = eng.near_anchor(cursor, cfg.slop - slack_used)
            if gap is not None and gap > 0.0:
                emit(slack_used + gap)
                # A forced fit does not occupy the anchor; deeper search may still
                # find an exact closure, so carry on.

        if used == total_pieces and not stubs:
            return True

        # -- pruning ------------------------------------------------------------
        # The walk must eventually reach a closing target: the anchor, or -- in
        # reversing mode -- any open junction stub.  Prune only when no target's
        # position or heading is attainable with what remains.
        home = eng.dist_home(cursor)
        need = eng.need_turn24(cursor)
        if cfg.reversing_loops:
            for _pidx, _port, stub_pose in stubs:
                home = min(home, eng.dist(cursor, stub_pose))
                need = min(need, eng.stub_need24(cursor, stub_pose))
        stub_reach = sum(span_of[placements[s[0]][0]] for s in stubs)
        if home > remaining_span + stub_reach + (cfg.slop - slack_used) + 1e-6:
            stats.pruned_reach += 1
            return True
        stub_turns = sum(turn_of[placements[s[0]][0]] for s in stubs)
        if need > remaining_turn + stub_turns:
            stats.pruned_turn += 1
            return True
        # IDA* contour (completion mode): at least this many more pieces are needed.
        # Transits through open stubs advance the walk without costing a piece, so
        # the admissible estimate must discount what the stubs could contribute
        # (mirroring the plain reach/turn prunes above).
        slack_left = max(0.0, cfg.slop - slack_used)
        h_dist = int(
            (max(0.0, home - slack_left - stub_reach) + max_span_any - 1e-6)
            // max_span_any
        )
        need_beyond_stubs = max(0, need - stub_turns)
        if need_beyond_stubs > 0:
            if max_turn_any == 0:
                stats.pruned_turn += 1
                return True
            h_turn = -(-need_beyond_stubs // max_turn_any)
        else:
            h_turn = 0
        if used + max(h_dist, h_turn) > f_limit:
            stats.pruned_reach += 1
            return True

        # -- transit an open stub the walk meets (exactly, or within the slop) ----
        if stubs:
            snapshot = list(stubs)
            for i, (pidx, port, pose) in enumerate(snapshot):
                if (
                    prev_index is not None
                    and overhang_of[placements[prev_index][0]] > 0
                    and overhang_of[placements[pidx][0]] > 0
                ):
                    continue  # two overhanging plates cannot share the joint
                if eng.connects(cursor, pose):
                    joint_gap = 0.0
                else:
                    gap = (
                        eng.near_pose(cursor, pose, cfg.slop - slack_used)
                        if cfg.slop > 0.0
                        else None
                    )
                    if gap is None:
                        continue
                    joint_gap = gap
                if cfg.reversing_loops and used > 0 and eligible(used):
                    # Closing INTO the stub (rather than driving through) makes a
                    # reversing loop: the walk's end mates this branch, and the train
                    # thereafter shuttles out through the junction's other route.
                    emit(slack_used + joint_gap, reversing_target=(pidx, port))
                stub_pid = placements[pidx][0]
                piece = pieces[stub_pid]
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
                    if frame is None:  # a base placement: its poses were precomputed
                        out_pose = base_stub_poses[(pidx, exit_port)]
                    else:
                        out_pose = eng.port_world(stub_pid, exit_port, frame)
                    stubs[:] = [s for k, s in enumerate(snapshot) if k not in (i, j)]
                    steps.append(_Transit(pidx, port, exit_port))
                    keep_going = dfs(out_pose, used, slack_used + joint_gap, pidx)
                    steps.pop()
                    stubs[:] = snapshot
                    if not keep_going:
                        return False

        # -- place a new piece -----------------------------------------------------
        if used >= depth_limit:
            return True
        candidates: list[tuple[float, str, int, int, object]] = []
        cursor_overhangs = (
            prev_index is not None and overhang_of[placements[prev_index][0]] > 0
        )
        for pid in piece_ids:
            if counts[pid] == 0:
                continue
            if cursor_overhangs and overhang_of[pid] > 0:
                continue  # the joint would stack two overhanging plates
            for entry, exit_port, apply_move in eng.moves[pid]:
                child = apply_move(cursor)
                heuristic = eng.heur_dist(child) + 64.0 * eng.need_turn24(child)
                if cfg.reversing_loops:
                    for _pidx, _port, stub_pose in stubs:
                        heuristic = min(
                            heuristic,
                            eng.dist(child, stub_pose)
                            + 64.0 * eng.stub_need24(child, stub_pose),
                        )
                candidates.append((heuristic, piece_rank[pid], pid, entry, exit_port, child))
        # Try homeward moves first: irrelevant to completeness, decisive for how fast
        # the obvious completion of a small gap is found.
        candidates.sort(key=lambda c: (c[0], c[1], c[2], c[3], c[4]))
        for _heuristic, _rank_, pid, entry, exit_port, next_cursor in candidates:
            piece = pieces[pid]
            frame = eng.frame(pid, entry, cursor)
            hkey, fx, fy, fz, cos_t, sin_t = eng.frame_floats(frame)
            pts = placement_samples(pid, entry, hkey, cos_t, sin_t, fx, fy, fz)
            index = len(placements)
            ignore = {prev_index} if prev_index is not None else set()
            # A move that closes the loop legitimately butts against the anchor
            # piece; exempt it from colliding with that piece only.  Likewise a
            # move landing on an open stub butts against that stub's piece.
            if placements and eligible(used + 1):
                if eng.closes(next_cursor) or (
                    cfg.slop > 0.0
                    and eng.near_anchor(next_cursor, cfg.slop - slack_used) is not None
                ):
                    ignore.add(anchor_index)
            for stub_index, _stub_port, stub_pose in stubs:
                if eng.connects(next_cursor, stub_pose) or (
                    cfg.slop > 0.0
                    and eng.near_pose(next_cursor, stub_pose, cfg.slop - slack_used)
                    is not None
                ):
                    ignore.add(stub_index)
            if field.clashes(pts, piece.width / 2.0, ignore, underpass=piece.underpass):
                stats.pruned_collision += 1
                continue

            counts[pid] -= 1
            remaining_span -= span_of[pid]
            remaining_turn -= turn_of[pid]
            placements.append((pid, frame))
            field.add(index, pts, piece.width / 2.0, underpass=piece.underpass)
            new_stubs = 0
            if piece.is_junction:
                for port_index in range(len(piece.ports)):
                    if port_index in (entry, exit_port):
                        continue
                    stubs.append((index, port_index, eng.port_world(pid, port_index, frame)))
                    new_stubs += 1
            steps.append(_Place(pid, entry, exit_port))

            keep_going = dfs(next_cursor, used + 1, slack_used, index)

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

    depth_limit = total_pieces
    if cfg.max_pieces is not None:
        depth_limit = min(depth_limit, cfg.max_pieces)
    if base is None:
        # Loop mode enumerates everything reachable; one full-depth pass.
        f_limit = depth_limit
        dfs(eng.start_cursor, 0, 0.0, start_prev)
    else:
        # Completion mode runs IDA*: grow the pieces-needed contour until closures
        # appear.  Uninformed depth-first dies here whenever the inventory is broad
        # (it exhausts gigantic fruitless subtrees before ever backtracking), while
        # each admissible contour stays small and finds the SHORTEST completions
        # first.  Plain iterative deepening without the heuristic was tried and is
        # equally hopeless -- the contour bound is what tames the tree.
        for f_limit in range(1, depth_limit + 1):
            if not dfs(eng.start_cursor, 0, 0.0, start_prev):
                break
            if len(solutions) >= cfg.max_results or stats.aborted:
                break
    stats.duration_s = time.perf_counter() - started

    ordered = sorted(
        solutions.values(),
        key=lambda s: (
            not s.exact,
            s.kind != "loop",
            s.gap,
            s.open_stubs,
            s.piece_count if base is not None else -s.piece_count,
        ),
    )
    return SolveResult(solutions=ordered, stats=stats)
