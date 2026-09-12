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
    * exact completion reachability -- short tails must reach the target on the grid;
    * collisions -- a placement overlapping existing track is cut immediately.
"""

from __future__ import annotations

import math
import time
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from functools import lru_cache

from .collision import DEFAULT_CLEARANCE, CollisionField
from .exact import Alg
from .geometry import HEADING_STEPS, ORIGIN, Pose, cos_sin
from .lattice import ROT_COS_SIN, LatticePoint, LatticePose, from_alg_xy, z_from_alg
from .layout import Layout
from .pieces import PieceType
from .symmetry import placement_key, pose_key
from .validation import check_inventory

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


def _traversal_key(
    piece: PieceType, entry: int, exit_port: int, *, mirror: bool = False
) -> tuple:
    """Full placed geometry, route incidence, and the chosen outward exit pose."""
    frame = piece.frame_for(entry, ORIGIN)
    port = piece.ports[exit_port].pose
    exit_pose = frame.then(port.x, port.y, port.z, port.heading)
    return placement_key(piece, frame, mirror), pose_key(exit_pose, mirror)


def _canonical_traversals(piece: PieceType) -> dict[tuple[int, int], tuple[int, int]]:
    """Map every (entry, exit) traversal to its physically-equivalent canonical one.

    A straight's two directions collapse onto one representative; a curve's do not
    (they are the left and the right turn).  Used both to enumerate search moves and
    to normalise loop signatures, so both sides agree on what "the same move" means.
    """
    return dict(_cached_canonical_traversals(piece))


@lru_cache(maxsize=128)
def _cached_canonical_traversals(
    piece: PieceType,
) -> tuple[tuple[tuple[int, int], tuple[int, int]], ...]:
    canon: dict[tuple[int, int], tuple[int, int]] = {}
    by_key: dict[tuple, tuple[int, int]] = {}
    for entry in range(len(piece.ports)):
        for exit_port, _route in piece.transit(entry):
            key = _traversal_key(piece, entry, exit_port)
            representative = by_key.setdefault(key, (entry, exit_port))
            canon[(entry, exit_port)] = representative
    return tuple(canon.items())


def _moves_for(piece: PieceType) -> list[Move]:
    """All geometrically distinct traversals of *piece*, one Move per equivalence class.

    Traversals through a sealed face are excluded: a buffer stop can terminate track
    but can never be part of a route, so the loop search never places one.
    """
    return list(_cached_moves(piece))


@lru_cache(maxsize=128)
def _cached_moves(piece: PieceType) -> tuple[Move, ...]:
    """Retain only bounded immutable catalogue metadata, never solver state."""
    moves: list[Move] = []
    for (entry, exit_port), representative in _canonical_traversals(piece).items():
        if (entry, exit_port) != representative:
            continue
        if entry in piece.sealed or exit_port in piece.sealed:
            continue
        dx, dy, dz, dheading = piece.exit_delta(entry, exit_port)
        moves.append(Move(piece.id, entry, exit_port, dx, dy, dz, dheading))
    return tuple(moves)


def _mirror_ports(piece: PieceType) -> dict[int, int | None]:
    """Map each port to the port its mirror image lands on, if any.

    Local reflection across the piece's x axis; for the switch this pairs left/right
    and fixes the stem.  ``None`` when the piece has no mirror-symmetric counterpart
    for that port (the crossing's diagonal ports), in which case callers skip the
    mirror candidate rather than mis-pair.
    """
    return dict(_cached_mirror_ports(piece))


@lru_cache(maxsize=128)
def _cached_mirror_ports(piece: PieceType) -> tuple[tuple[int, int | None], ...]:
    by_pose = {
        (p.pose.x, p.pose.y, p.pose.z, p.pose.heading): i
        for i, p in enumerate(piece.ports)
    }
    return tuple({
        i: by_pose.get(
            (p.pose.x, -p.pose.y, p.pose.z, (-p.pose.heading) % HEADING_STEPS)
        )
        for i, p in enumerate(piece.ports)
    }.items())


def _mirror_traversals(piece: PieceType) -> dict[tuple[int, int], tuple[int, int] | None]:
    """Map each traversal to the traversal that produces its mirror image, if any.

    Derived from geometry rather than a hand-kept handedness table: a traversal's
    anchored placement is reflected across the axis of approach (y -> -y, heading
    negated) and the traversal of the same piece landing on exactly that reflected
    geometry is looked up.  This automatically pairs a curve's left and right
    readings, a switch's two branches, and even a crossing's two routes; a genuinely
    single-handed piece maps to ``None`` (its loops have no buildable mirror twin).
    """
    return dict(_cached_mirror_traversals(piece))


@lru_cache(maxsize=128)
def _cached_mirror_traversals(
    piece: PieceType,
) -> tuple[tuple[tuple[int, int], tuple[int, int] | None], ...]:
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
        mirrored_key = _traversal_key(piece, entry, exit_port, mirror=True)
        partner = by_key.get(mirrored_key)
        mirror[(entry, exit_port)] = canon[partner] if partner is not None else None
    return tuple(mirror.items())


@lru_cache(maxsize=128)
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


@lru_cache(maxsize=128)
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

    @staticmethod
    def reverse(pose: Pose) -> Pose:
        return pose.reversed()

    @staticmethod
    def level(pose: Pose) -> Pose:
        return Pose(pose.x, pose.y, 0, pose.heading)

    @staticmethod
    def height(pose: Pose) -> Alg:
        return pose.z

    def retarget(self, cursor: Pose, target: Pose) -> Pose:
        """Move target onto the anchor, applying the same rigid motion to cursor."""
        turn = self.anchor.heading - target.heading
        c, s = cos_sin(turn)
        dx, dy = cursor.x - target.x, cursor.y - target.y
        return Pose(
            self.anchor.x + c * dx - s * dy,
            self.anchor.y + s * dx + c * dy,
            self.anchor.z + cursor.z - target.z,
            cursor.heading + turn,
        )

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

    @staticmethod
    def reverse(pose: tuple) -> tuple:
        return (*pose[:5], (pose[5] + 6) % 12)

    @staticmethod
    def level(pose: tuple) -> tuple:
        return (*pose[:4], 0, pose[5])

    @staticmethod
    def height(pose: tuple) -> int:
        return pose[4]

    def retarget(self, cursor: tuple, target: tuple) -> tuple:
        """Exact SE(2) change of target, with an independent height translation."""
        anchor = self.anchor
        turn = (anchor[5] - target[5]) % 12
        a, b, c, d = (cursor[i] - target[i] for i in range(4))
        for _ in range(turn):
            a, b, c, d = -d, a, b + d, c
        return (anchor[0] + a, anchor[1] + b, anchor[2] + c, anchor[3] + d,
                anchor[4] + cursor[4] - target[4], (cursor[5] + turn) % 12)

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
# Exact short-tail reachability, followed by step traces and their signatures
# --------------------------------------------------------------------------------------


class _CompletionBounds:
    """Exact linear envelopes, indexed by heading and maximum tail length.

    A move adds a fixed displacement at a given heading. Minimum/maximum linear
    projections therefore compose without enumerating positions: translate every
    interval, then take the union's bounds. Intervals may describe different walks,
    so membership is only necessary. This stays useful beyond the short exact table.
    """

    def __init__(self, eng) -> None:
        if eng.name == "lattice":
            self.project = self._lattice_projection
            self.heading = lambda pose: pose[5]
            zeros = [(0, 0, 0, 0, 0, heading) for heading in range(12)]
        else:
            self.project = self._field_projection
            self.heading = lambda pose: pose.heading
            zeros = [Pose.make(heading=heading) for heading in range(HEADING_STEPS)]
        # Include full 3D deltas and every preplaced route, not only spare pieces.
        moves = {apply_move(zeros[0]): apply_move
                 for routes in eng.moves.values() for _entry, _exit, apply_move in routes}
        self.deltas = []
        for zero in zeros:
            predecessors = (eng.reverse(move(eng.reverse(zero))) for move in moves.values())
            self.deltas.append(tuple({
                (self.heading(pose), self.project(pose)) for pose in predecessors
            }))
        coords = self.project(eng.anchor)
        self.layers = [{self.heading(eng.anchor): (coords, coords)}]
        self.saturated = False

    @staticmethod
    def _lattice_projection(pose) -> tuple:
        a, b, c, d, _z, _heading = pose
        # 26/15 approximates sqrt(3), making these projections nearly horizontal
        # and vertical. They are EXACT integer linear forms, not rounded positions:
        # the same forms bound moves and query cursors, so no tolerance is needed.
        x, y = 30 * a + 26 * b + 15 * c, 15 * b + 26 * c + 30 * d
        return (*pose[:5], x, y, x + y, x - y)

    @staticmethod
    def _field_projection(pose: Pose) -> tuple:
        # Rational surrogates for 1, sqrt(2), sqrt(3), sqrt(6), scaled by 60.
        # As above, any fixed rational linear forms are conservative. Retain all
        # individual coefficients too, including exact height coefficients.
        weights = (60, 85, 104, 147)
        x = sum(w * c for w, c in zip(weights, pose.x.coeffs(), strict=True))
        y = sum(w * c for w, c in zip(weights, pose.y.coeffs(), strict=True))
        return (*pose.x.coeffs(), *pose.y.coeffs(), *pose.z.coeffs(), x, y, x + y, x - y)

    def extend(self, traversals: int, max_work: int) -> int:
        """Publish only complete layers and return the move expansions spent."""
        spent = 0
        while len(self.layers) <= traversals and not self.saturated:
            previous = self.layers[-1]
            work = sum(len(self.deltas[heading]) for heading in previous)
            if work > max_work - spent:
                break
            spent += work
            layer = dict(previous)  # at most k traversals also includes k - 1
            for heading, (low, high) in previous.items():
                for next_heading, delta in self.deltas[heading]:
                    next_low = tuple(a + b for a, b in zip(low, delta, strict=True))
                    next_high = tuple(a + b for a, b in zip(high, delta, strict=True))
                    if next_heading in layer:
                        old_low, old_high = layer[next_heading]
                        next_low = tuple(map(min, old_low, next_low))
                        next_high = tuple(map(max, old_high, next_high))
                    layer[next_heading] = next_low, next_high
            if layer == previous:
                # Empty/zero-motion move pools can stabilize without spending any
                # work. Reuse this fixed point for all depths instead of allocating
                # unbounded identical layers for a large inventory.
                self.saturated = True
            else:
                self.layers.append(layer)
        return spent

    def allows(self, cursor, traversals: int) -> bool:
        if traversals >= len(self.layers) and not self.saturated:
            return True  # the shared preprocessing budget could not finish this depth
        layer = self.layers[min(traversals, len(self.layers) - 1)]
        interval = layer.get(self.heading(cursor))
        return interval is not None and all(
            low <= value <= high
            for low, value, high in zip(interval[0], self.project(cursor), interval[1], strict=True)
        )


class _CompletionReachability:
    """Bounded reverse reachability for planar poses and heights independently.

    Each complete layer contains ALL projections of cursors that can reach the
    anchor in at most that many traversals. Separating height from planar geometry
    avoids multiplying states for bridge routes. The two projections may use
    different routes; that only enlarges the set allowed by this check.

    Reversing a physical route is always another legal route,
    so reversing the cursor, taking a move, and reversing again enumerates every
    predecessor. Ignoring placement constraints makes this an overapproximation:
    absence proves impossibility, while membership still needs the full DFS audit.

    Never use a partly built layer. If the preprocessing budget runs out, retain
    the completed shorter layers and let DFS handle the rest normally.
    """

    def __init__(self, eng, horizon: int, max_work: int) -> None:
        self.eng = eng
        self.horizon = horizon
        self.work_left = max_work
        self.work_limit = max_work
        # Different geometries can share an endpoint transform. Geometry is not a
        # constraint here, so expand each distinct transform only once.
        endpoints = [
            (apply_move(eng.anchor), apply_move)
            for moves in eng.moves.values()
            for _entry, _exit, apply_move in moves
        ]
        unique = {eng.level(pose): move for pose, move in endpoints}
        self.moves = tuple(unique.values())
        self.rises = {eng.height(pose) - eng.height(eng.anchor) for pose, _ in endpoints}
        self.layers = [frozenset((eng.level(eng.anchor),))]
        self.frontier = self.layers[0]
        self.height_layers = [frozenset((eng.height(eng.anchor),))]
        self.height_frontier = self.height_layers[0]
        self.bounds = _CompletionBounds(eng)

    def allows(self, cursor, traversals: int) -> bool:
        self.work_left -= self.bounds.extend(traversals, self.work_left)
        if not self.bounds.allows(cursor, traversals):
            return False
        if traversals > self.horizon:
            return True
        while len(self.layers) <= traversals:
            work = (len(self.frontier) * len(self.moves)
                    + len(self.height_frontier) * len(self.rises))
            if work > self.work_left:
                return True
            self.work_left -= work
            previous = self.layers[-1]
            frontier = set()
            for pose in self.frontier:
                backwards = self.eng.reverse(pose)
                for apply_move in self.moves:
                    predecessor = self.eng.level(self.eng.reverse(apply_move(backwards)))
                    if predecessor not in previous:
                        frontier.add(predecessor)
            previous_heights = self.height_layers[-1]
            height_frontier = {
                height + rise for height in self.height_frontier for rise in self.rises
            } - previous_heights
            self.frontier = frontier
            self.height_frontier = height_frontier
            self.layers.append(previous | frontier)
            self.height_layers.append(previous_heights | height_frontier)
        return (self.eng.level(cursor) in self.layers[traversals]
                and self.eng.height(cursor) in self.height_layers[traversals])


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
    them resolve to a piece id. Their placement indices remain fixed, including
    the closing stub: distinct junctions in a fixed base are not interchangeable.
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
        fresh: dict[int, int] = {} if cyclic else {i: i for i in range(n_base)}
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
        # A fresh reversing loop is anchored at its open tail: only reflection
        # is a symmetry. A completion is anchored to the entire fixed base, so
        # even reflection can change the resulting layout. In both modes the
        # closing joint is part of the identity, appended as a final token.
        stub_inst, stub_port = closing_stub

        def with_join(seq, port: int) -> tuple:
            fresh: dict[int, int] = {} if cyclic else {i: i for i in range(n_base)}
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
        mirrored = mirror_of(visits) if cyclic else None
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
    #: Newly placed pieces in completion mode; zero permits existing-junction
    #: transits without spending inventory (an empty fresh loop is never emitted).
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
    #: Exact reverse reachability for this many final traversals in completion
    #: mode, supplemented by longer linear bounds. Zero disables both; they share
    #: a preprocessing cap of 4096 moves (and at most max_nodes // 8). Slop fits
    #: bypass both exact checks.
    completion_lookahead: int = 6

    def __post_init__(self) -> None:
        for name in ("slop", "clearance", "collision_spacing"):
            value = getattr(self, name)
            if not math.isfinite(value) or value < 0:
                raise ValueError(f"{name} must be finite and non-negative")
        if self.collision_spacing == 0:
            raise ValueError("collision_spacing must be positive")
        for name, minimum in (("min_pieces", 0), ("max_results", 1), ("max_nodes", 1)):
            value = getattr(self, name)
            if type(value) is not int or value < minimum:
                raise ValueError(f"{name} must be an integer >= {minimum}")
        if self.max_pieces is not None and (
            type(self.max_pieces) is not int or self.max_pieces < 1
        ):
            raise ValueError("max_pieces must be a positive integer or None")
        if type(self.completion_lookahead) is not int or not 0 <= self.completion_lookahead <= 6:
            raise ValueError("completion_lookahead must be an integer from 0 to 6")


@dataclass
class SolveStats:
    nodes: int = 0
    closures_found: int = 0  # before deduplication
    pruned_turn: int = 0
    pruned_reach: int = 0
    pruned_collision: int = 0
    pruned_completion: int = 0
    completion_states: int = 0  # planar states in the largest complete reverse layer
    duration_s: float = 0.0
    aborted: bool = False  # stopped by max_nodes
    engine: str = ""  # which arithmetic backend ran
    #: Candidates rejected by the final actual-link overlap audit. A potential
    #: future joint exempted during search may not be realized in the final trace;
    #: these overlapping candidates are counted here, never returned.
    dropped_overlap: int = 0
    #: True only after exhausting the entire inventory, not a capped search.
    complete: bool = False
    stop_reason: str = "not_started"
    max_pieces_searched: int = 0
    completion_height_states: int = 0
    completion_work: int = 0
    completion_bound_depth: int = 0
    completion_bound_states: int = 0  # retained heading envelopes across all depths


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
    check_inventory(inventory, pieces)

    if base is None:
        if grow_from is not None or close_onto is not None:
            raise ValueError("grow_from/close_onto only make sense with a base layout")
        base_pids: list[str] = []
    else:
        opens = base.connectable_ends()
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
    # Reverse reachability also needs routes through preplaced junctions, including
    # types absent from the spare inventory. Only piece_ids may be newly placed.
    moves_by_piece = {pid: _moves_for(piece) for pid, piece in piece_obj.items()}
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

    def placement_groups(
        pid: str,
        entry: int,
        hkey: int,
        cos_t: float,
        sin_t: float,
        fx: float,
        fy: float,
        fz: float,
    ):
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
        return field._prepare(base_pts, offset=(fx, fy, fz))

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
    completion = (
        _CompletionReachability(eng, cfg.completion_lookahead, min(4096, cfg.max_nodes // 8))
        if base is not None and cfg.slop == 0 and cfg.completion_lookahead
        else None
    )
    stub_capacity = {
        pid: max(0, len(pieces[pid].ports) - len(pieces[pid].sealed) - 2)
        if pieces[pid].is_junction else 0
        for pid in piece_ids
    }

    def transit_bound(piece: PieceType, ports: set[int]) -> int:
        # Only ports with an available route partner can participate in a transit.
        # Each transit consumes two ports; this is an upper bound even when routes
        # share a stem. In particular, separate switches' lone stubs cannot pair.
        eligible_ports = {
            port for route in piece.routes
            if route.port_a in ports and route.port_b in ports
            for port in (route.port_a, route.port_b)
        }
        return len(eligible_ports) // 2

    future_transits: dict[str, int] = {}
    reversing_queries: dict[str, tuple] = {}
    if completion is not None:
        for pid in piece_ids:
            piece = pieces[pid]
            capacity = 0
            queries = set()
            if piece.is_junction:
                for entry, exit_port, apply_move in eng.moves[pid]:
                    free = set(range(len(piece.ports))) - piece.sealed - {entry, exit_port}
                    capacity = max(capacity, transit_bound(piece, free))
                    if cfg.reversing_loops:
                        frame = eng.frame(pid, entry, eng.anchor)
                        out = apply_move(eng.anchor)
                        queries.update(
                            eng.retarget(out, eng.reverse(eng.port_world(pid, port, frame)))
                            for port in free
                        )
            future_transits[pid] = capacity
            reversing_queries[pid] = tuple(queries)

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

    # These queries describe a future junction's own geometry, independent of the
    # growing path. Cap the per-search cache now that bounds can check longer tails.
    future_closure: dict[tuple[str, int], bool] = {}

    def tail_possible(cursor, used: int, extra_pid: str | None = None) -> bool:
        if completion is None:
            return True
        slots = min(total_pieces, depth_limit, f_limit) - used
        if extra_pid and cfg.reversing_loops and stub_capacity[extra_pid]:
            # Its new targets do not have frames yet. The recursive call checks
            # them after placement; do not guess their positions in this early test.
            return True
        free_by_placement: dict[int, set[int]] = {}
        for index, port, _pose in stubs:
            free_by_placement.setdefault(index, set()).add(port)
        transits = sum(
            transit_bound(piece_obj[placements[index][0]], ports)
            for index, ports in free_by_placement.items()
        )
        if extra_pid:
            transits += future_transits[extra_pid]
        capacity = max((future_transits[pid] for pid in piece_ids if counts[pid]), default=0)
        transits += min(slots * capacity, sum(
            counts[pid] * future_transits[pid] for pid in piece_ids
        ))
        traversals = slots + transits
        if completion.allows(cursor, traversals):
            return True
        if cfg.reversing_loops:
            for _index, _port, pose in stubs:
                query = eng.retarget(cursor, eng.reverse(pose))
                if completion.allows(query, traversals):
                    return True
            if slots:
                # A future reversing target is created by one placement. Whatever
                # precedes that placement, its exit must reach one of its free ports
                # in at most the remaining traversals. Ignore all stock/geometry
                # constraints here, retaining an overapproximation of every target.
                for pid in piece_ids:
                    if not counts[pid] or not reversing_queries[pid]:
                        continue
                    key = (pid, traversals - 1)
                    possible = future_closure.get(key)
                    if possible is None:
                        possible = any(completion.allows(query, traversals - 1)
                                       for query in reversing_queries[pid])
                        if len(future_closure) < 4096:
                            future_closure[key] = possible
                    if possible:
                        return True
        return False

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

        if steps and eng.closes(cursor):
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
            if any(counts[pid] and stub_capacity[pid] for pid in piece_ids):
                # A junction not placed yet can create a closing target anywhere
                # along the walk. Distance/heading to only today's targets cannot
                # rule that out. The exact tail check includes these future targets.
                home = need = 0
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

        if not tail_possible(cursor, used):
            stats.pruned_completion += 1
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
                if cfg.reversing_loops and steps and eligible(used):
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
        if used >= min(depth_limit, f_limit):
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
        for _heuristic, _prio, pid, entry, exit_port, next_cursor in candidates:
            # Reject an impossible endpoint before sampling collision geometry or
            # spending a DFS node. Leaving this piece in counts only enlarges the
            # reachability bound, so this early check remains conservative.
            if not tail_possible(next_cursor, used + 1, pid):
                stats.pruned_completion += 1
                continue
            piece = pieces[pid]
            frame = eng.frame(pid, entry, cursor)
            hkey, fx, fy, fz, cos_t, sin_t = eng.frame_floats(frame)
            grouped_pts = placement_groups(
                pid, entry, hkey, cos_t, sin_t, fx, fy, fz
            )
            index = len(placements)
            ignore = {prev_index} if prev_index is not None else set()
            # Every free connector can become a later joint, not just the exit
            # used by this traversal. A crossing's other route may already mate
            # the target and only be linked after re-entry. Exempt these possible
            # neighbours now; the final audit still requires actual links.
            free_poses = [next_cursor]
            free_poses.extend(
                eng.port_world(pid, port, frame)
                for port in range(len(piece.ports))
                if port not in (entry, exit_port) and port not in piece.sealed
            )
            slack_left = cfg.slop - slack_used
            if placements and not (
                overhang_of[pid] > 0 and overhang_of[placements[anchor_index][0]] > 0
            ):
                if any(eng.closes(pose) or (
                    cfg.slop > 0.0 and eng.near_anchor(pose, slack_left) is not None
                ) for pose in free_poses):
                    ignore.add(anchor_index)
            for stub_index, _stub_port, stub_pose in stubs:
                if overhang_of[pid] > 0 and overhang_of[placements[stub_index][0]] > 0:
                    continue
                if any(eng.connects(pose, stub_pose) or (
                    cfg.slop > 0.0 and eng.near_pose(pose, stub_pose, slack_left) is not None
                ) for pose in free_poses):
                    ignore.add(stub_index)
            if field._clashes_prepared(
                grouped_pts, piece.width / 2.0, ignore, underpass=piece.underpass
            ):
                stats.pruned_collision += 1
                continue

            counts[pid] -= 1
            remaining_span -= span_of[pid]
            remaining_turn -= turn_of[pid]
            placements.append((pid, frame))
            field._add_prepared(
                index, grouped_pts, piece.width / 2.0, underpass=piece.underpass
            )
            new_stubs = 0
            if piece.is_junction:
                for port_index in range(len(piece.ports)):
                    if port_index in (entry, exit_port) or port_index in piece.sealed:
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
        stats.max_pieces_searched = f_limit
        dfs(eng.start_cursor, 0, 0.0, start_prev)
    else:
        # Completion mode runs IDA*: grow the pieces-needed contour until closures
        # appear.  Uninformed depth-first dies here whenever the inventory is broad
        # (it exhausts gigantic fruitless subtrees before ever backtracking), while
        # each admissible contour stays small and finds the SHORTEST completions
        # first.  Plain iterative deepening without the heuristic was tried and is
        # equally hopeless -- the contour bound is what tames the tree.
        # A completion may only join/transit preplaced junctions. It still has
        # a nonempty step trace, but uses no inventory and needs contour zero.
        first_limit = 0 if cfg.min_pieces == 0 else 1
        for f_limit in range(first_limit, depth_limit + 1):
            stats.max_pieces_searched = f_limit
            if not dfs(eng.start_cursor, 0, 0.0, start_prev):
                break
            if len(solutions) >= cfg.max_results or stats.aborted:
                break
    if stats.aborted:
        stats.stop_reason = "node_limit"
    elif len(solutions) >= cfg.max_results:
        stats.stop_reason = "result_limit"
    elif depth_limit < total_pieces:
        stats.stop_reason = "piece_limit"
    else:
        stats.complete = True
        stats.stop_reason = "exhausted"
    stats.duration_s = time.perf_counter() - started
    if completion is not None:
        stats.completion_states = len(completion.layers[-1])
        stats.completion_height_states = len(completion.height_layers[-1])
        stats.completion_work = completion.work_limit - completion.work_left
        stats.completion_bound_depth = len(completion.bounds.layers) - 1
        stats.completion_bound_states = sum(map(len, completion.bounds.layers))

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
