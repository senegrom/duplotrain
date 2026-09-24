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
    * reverse reachability -- the traversals left must be able to bring the walk back
      to its closing target (the origin face of a fresh loop, the selected end of a
      completion) within the remaining slop;
    * collisions -- a placement overlapping existing track is cut immediately.
"""

from __future__ import annotations

import math
import time
from bisect import bisect_left, bisect_right
from collections import OrderedDict
from collections.abc import Generator, Mapping, Sequence
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache

from .collision import DEFAULT_CLEARANCE, CollisionField, bounds_of
from .exact import Alg
from .geometry import HEADING_STEPS, ORIGIN, Pose, cos_sin
from .lattice import ROT_COS_SIN, SCALE, LatticePoint, LatticePose, from_alg_xy, z_from_alg
from .layout import Layout, Placement
from .pieces import PieceType
from .symmetry import placement_key, pose_key
from .validation import check_inventory

__all__ = ["Move", "SolverConfig", "Solution", "SolveStats", "SolveResult",
           "SearchLimits", "solve", "solve_steps"]


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


def _completion_moves(
    pieces: Mapping[str, PieceType],
    stock: Mapping[str, int],
    base: Layout | None,
    grow_from: tuple[int, int] | None,
    close_onto: tuple[int, int] | None,
) -> dict[str, list[Move]]:
    """Relax only traversals the search can actually use.

    Stock types may be placed in any orientation. A base-only type contributes
    only routes whose two ports are still free on ONE preplaced junction, not a
    union of free ports from different instances. Occupied ports, sealed faces
    and the two selected endpoints never become transit entries. Transits consume
    ports and never reopen them, so this initial superset stays conservative.

    Keep all types in the result (possibly with no moves): the engines still need
    their port geometry for targets, and collision/replay use the complete base.
    Canonical representatives retain the exact endpoint transform of a route.
    """
    available: dict[str, set[tuple[int, int]]] = {}
    if base is not None:
        for index, placement in enumerate(base):
            piece = placement.piece
            if stock.get(piece.id, 0) > 0 or not piece.is_junction:
                continue
            free = {
                port for port in range(len(piece.ports))
                if port not in piece.sealed and (index, port) not in base.links
                and (index, port) not in (grow_from, close_onto)
            }
            if len(free) < 2:
                continue
            canon = _canonical_traversals(piece)
            available.setdefault(piece.id, set()).update(
                canon[entry, exit_port]
                for entry in free for exit_port, _route in piece.transit(entry)
                if exit_port in free
            )
    return {
        pid: [move for move in _moves_for(piece)
              if stock.get(pid, 0) > 0
              or (move.entry, move.exit) in available.get(pid, ())]
        for pid, piece in pieces.items()
    }


def _stock_span_budget(
    counts: Mapping[str, int], spans: Sequence[tuple[float, str]], slots: int,
    consumed: str | None = None,
) -> float:
    """Sum the longest available spans fitting *slots* (spans sorted descending)."""
    reach = 0.0
    for span, pid in spans:
        take = min(slots, counts[pid] - (pid == consumed))
        reach += take * span
        slots -= take
        if slots == 0:
            break
    return reach


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
def _spare_passes(piece: PieceType) -> int:
    """Further traversals a junction still offers once the walk has passed through it.

    Each such pass turns the walk again, at most by :func:`_turn_capacity`, without
    spending a piece. (Its displacement needs no extra budget: entering at one port
    and finally leaving at another nets at most the piece's own span.)
    """
    if not piece.is_junction:
        return 0
    best = 0
    for route in piece.routes:
        free = set(range(len(piece.ports))) - piece.sealed - {route.port_a, route.port_b}
        usable = {port for other in piece.routes
                  if other.port_a in free and other.port_b in free
                  for port in (other.port_a, other.port_b)}
        best = max(best, len(usable) // 2)
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

    @staticmethod
    def to_pose(frame: Pose) -> Pose:
        return frame

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

    @staticmethod
    def stub_refs(stubs: list) -> tuple:
        return tuple(pose for _index, _port, pose in stubs)

    def candidate_score(self, child: Pose, stub_refs: tuple) -> float:
        """Move-ordering score: distance plus turn penalty to the nearest target."""
        score = self.heur_dist(child) + 64.0 * self.need_turn24(child)
        for stub_pose in stub_refs:
            score = min(
                score, self.dist(child, stub_pose) + 64.0 * self.stub_need24(child, stub_pose)
            )
        return score


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


# Exact multiplication by each of the twelve lattice rotations. These expand
# R(a, b, c, d) = (-d, a, b + d, c), avoiding a rotation loop on every target query.
_RETARGET_ROTATIONS = (
    lambda a, b, c, d: (a, b, c, d),
    lambda a, b, c, d: (-d, a, b + d, c),
    lambda a, b, c, d: (-c, -d, a + c, b + d),
    lambda a, b, c, d: (-b - d, -c, b, a + c),
    lambda a, b, c, d: (-a - c, -b - d, a, b),
    lambda a, b, c, d: (-b, -a - c, -d, a),
    lambda a, b, c, d: (-a, -b, -c, -d),
    lambda a, b, c, d: (d, -a, -b - d, -c),
    lambda a, b, c, d: (c, d, -a - c, -b - d),
    lambda a, b, c, d: (b + d, c, -b, -a - c),
    lambda a, b, c, d: (a + c, b + d, -a, -b),
    lambda a, b, c, d: (b, a + c, d, -a),
)


@lru_cache(maxsize=4096)
def _lattice_pose(frame: tuple) -> Pose:
    """The exact field pose of a lattice pose: the inverse of _pose_to_lattice.

    Equal frames give the same object, so the placements assembled from them
    hit the sample and primitive caches by identity instead of comparing
    twelve exact coefficients.
    """
    a, b, c, d, z, heading = frame
    return Pose(
        Alg(Fraction(2 * a + c, 2 * SCALE), 0, Fraction(b, 2 * SCALE), 0),
        Alg(Fraction(2 * d + b, 2 * SCALE), 0, Fraction(c, 2 * SCALE), 0),
        Alg(Fraction(z, SCALE)),
        2 * heading,
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

    to_pose = staticmethod(_lattice_pose)

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
        a, b, c, d = _RETARGET_ROTATIONS[turn](
            cursor[0] - target[0], cursor[1] - target[1],
            cursor[2] - target[2], cursor[3] - target[3],
        )
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


    def need_turn24(self, cursor: tuple) -> int:
        gap = (cursor[5] - self.anchor[5]) % 12
        return 2 * min(gap, 12 - gap)

    def stub_need24(self, cursor: tuple, stub_pose: tuple) -> int:
        gap = (cursor[5] - stub_pose[5] - 6) % 12
        return 2 * min(gap, 12 - gap)

    @staticmethod
    def stub_refs(stubs: list) -> tuple:
        # Float positions and headings of the open stubs, converted once per node.
        return tuple((*_flat_xy(pose), pose[5]) for _index, _port, pose in stubs)

    def candidate_score(self, child: tuple, stub_refs: tuple) -> float:
        """Move-ordering score, combining approach distance and turn cost
        but converting the child pose to floats once per candidate."""
        a, b, c, d, z, h = child
        x = (a + (b * _SQRT3 + c) / 2.0) / 20.0
        y = (d + (c * _SQRT3 + b) / 2.0) / 20.0
        anchor = self.anchor
        ax, ay = self._approach
        gap = (h - anchor[5]) % 12
        score = (
            math.hypot(x - ax, y - ay) + 0.125 * abs(z - anchor[4])
            + 64.0 * (2 * min(gap, 12 - gap))
        )
        for sx, sy, sh in stub_refs:
            gap = (h - sh - 6) % 12
            score = min(score, math.hypot(x - sx, y - sy) + 64.0 * (2 * min(gap, 12 - gap)))
        return score


def _compile_lattice(
    anchor: Pose,
    start_cursor: Pose,
    pieces: Mapping[str, PieceType],
    moves_by_piece: Mapping[str, list[Move]],
) -> _LatticeEngine | None:
    anchor_l = _pose_to_lattice(anchor)
    start_l = _pose_to_lattice(start_cursor)
    if (anchor_l is None or start_l is None
            or not _packable(_flat(anchor_l)) or not _packable(_flat(start_l))):
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
# Bounded completion reachability, followed by step traces and their signatures
# --------------------------------------------------------------------------------------


# Outward rational enclosures of physical millimetres. Unlike the exact search's
# coefficient projections, these remain valid when a tiny real gap has large,
# cancelling radical coefficients. Integer arithmetic keeps rounding one-sided.
_MM_SCALE = 10**9
#: Reverse-table preprocessing is paid for progressively: every search gets a
#: small base allowance, each DFS node spent earns more, and a hard cap bounds
#: the total. Short searches never pay for deep tables; long ones earn them.
_TABLE_WORK_PER_NODE = 24
_TABLE_WORK_CAP = 1 << 18
#: A query a few moves beyond the deepest built layer is decided by expanding
#: the queried pose forward that many moves and testing the frontier against
#: that layer; this bounds the depth and the poses one probe may expand.
_PROBE_DEPTH = 3
_PROBE_WORK = 1024


def _slack_padding(slack: float) -> int:
    """Outward integer enclosure of a millimetre budget, in physical units."""
    numerator, denominator = slack.as_integer_ratio()
    return -(-numerator * _MM_SCALE // denominator) + 2


def _completion_budget(nodes: int, max_nodes: int, base: int | None = None) -> int:
    """Table expansions a search may have spent after *nodes* DFS nodes."""
    if base is None:
        base = min(4096, max_nodes // 8)
    return min(_TABLE_WORK_CAP, base + _TABLE_WORK_PER_NODE * nodes)
_ROOT_BOUNDS = tuple((math.isqrt(n * _MM_SCALE**2), math.isqrt(n * _MM_SCALE**2) + 1)
                     for n in (2, 3, 6))
_SLIP_AXES = ((1, 0), (0, 1), (1, 1), (1, -1), (2, 1), (2, -1), (1, 2), (1, -2))
_SLIP_NORMS = tuple(math.isqrt((a * a + b * b) * _MM_SCALE**2) + 1
                    for a, b in _SLIP_AXES)


def _alg_interval(value: Alg) -> tuple[int, int]:
    # The same enclosure as summing Fraction coefficients times the radical
    # bounds, over one common denominator in integers: floor and ceiling of the
    # exact rational sums, then the outward guard. Fraction arithmetic would
    # normalise by a gcd at every step.
    fractions = value.coeffs()
    denominator = 1
    for coefficient in fractions:
        denominator = denominator * coefficient.denominator // math.gcd(
            denominator, coefficient.denominator)
    numerators = [coefficient.numerator * (denominator // coefficient.denominator)
                  for coefficient in fractions]
    low = high = numerators[0] * _MM_SCALE
    for numerator, (a, b) in zip(numerators[1:], _ROOT_BOUNDS, strict=True):
        if numerator >= 0:
            low += numerator * a
            high += numerator * b
        else:
            low += numerator * b
            high += numerator * a
    low, high = low // denominator, -(-high // denominator)
    guard = (abs(low) + abs(high)) // 2**40 + 2
    return low - guard, high + guard


def _physical_envelope(x, y, height) -> tuple[tuple, tuple]:
    return (tuple(a * x[0] + b * y[0 if b >= 0 else 1] for a, b in _SLIP_AXES) + height,
            tuple(a * x[1] + b * y[1 if b >= 0 else 0] for a, b in _SLIP_AXES) + height)


class _CompletionBounds:
    """Conservative linear envelopes, indexed by heading and maximum tail length.

    A move adds a fixed displacement at a given heading. Minimum/maximum linear
    projections therefore compose without enumerating positions: translate every
    interval, then take the union's bounds. Intervals may describe different walks,
    so membership is only necessary. Exact searches project coefficients; slippage
    searches enclose physical distances. Both remain useful beyond the short table.
    """

    def __init__(self, eng, *, slippage: bool = False) -> None:
        if eng.name == "lattice":
            self.project = self._lattice_projection
            physical = self._lattice_envelope
            self.heading = lambda pose: pose[5]
            zeros = [(0, 0, 0, 0, 0, heading) for heading in range(12)]
        else:
            self.project = self._field_projection
            physical = self._field_envelope
            self.heading = lambda pose: pose.heading
            zeros = [Pose.make(heading=heading) for heading in range(HEADING_STEPS)]
        self.enclose = physical if slippage else lambda pose: (self.project(pose),) * 2
        # Include full 3D deltas of stock and usable preplaced routes.
        moves = {apply_move(zeros[0]): apply_move
                 for routes in eng.moves.values() for _entry, _exit, apply_move in routes}
        self.deltas = []
        for zero in zeros:
            predecessors = (eng.reverse(move(eng.reverse(zero))) for move in moves.values())
            self.deltas.append(tuple({
                (self.heading(pose), *self.enclose(pose)) for pose in predecessors
            }))
        self.layers = [{self.heading(eng.anchor): self.enclose(eng.anchor)}]
        self.saturated = False
        self._paddings: dict[int, tuple] = {}

    @staticmethod
    def _lattice_envelope(pose) -> tuple[tuple, tuple]:
        # The same arithmetic as _outward and _physical_envelope over the lattice
        # coordinates x = (2a + c + b*sqrt3) / 40 and y = (2d + b + c*sqrt3) / 40,
        # written out flat: this runs once for every pose of every slippage layer.
        a, b, c, d, z, _heading = pose
        root_low, root_high = _ROOT_BOUNDS[1]
        rational = (2 * a + c) * _MM_SCALE
        if b >= 0:
            low, high = rational + b * root_low, rational + b * root_high
        else:
            low, high = rational + b * root_high, rational + b * root_low
        # Avoid float division, including for very large integer coefficients.
        low, high = low // 40, -(-high // 40)
        guard = (abs(low) + abs(high)) // 2**40 + 2
        x0, x1 = low - guard, high + guard
        rational = (2 * d + b) * _MM_SCALE
        if c >= 0:
            low, high = rational + c * root_low, rational + c * root_high
        else:
            low, high = rational + c * root_high, rational + c * root_low
        low, high = low // 40, -(-high // 40)
        guard = (abs(low) + abs(high)) // 2**40 + 2
        y0, y1 = low - guard, high + guard
        return (
            (x0, y0, x0 + y0, x0 - y1, 2 * x0 + y0, 2 * x0 - y1, x0 + 2 * y0, x0 - 2 * y1, z),
            (x1, y1, x1 + y1, x1 - y0, 2 * x1 + y1, 2 * x1 - y0, x1 + 2 * y1, x1 - 2 * y0, z),
        )

    @staticmethod
    def _field_envelope(pose: Pose) -> tuple[tuple, tuple]:
        return _physical_envelope(_alg_interval(pose.x), _alg_interval(pose.y), pose.z.coeffs())

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
                for next_heading, delta_low, delta_high in self.deltas[heading]:
                    next_low = tuple(a + b for a, b in zip(low, delta_low, strict=True))
                    next_high = tuple(a + b for a, b in zip(high, delta_high, strict=True))
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

    def allows_near(self, cursor, traversals: int, slack: int) -> bool:
        if traversals >= len(self.layers) and not self.saturated:
            return True
        interval = self.layers[min(traversals, len(self.layers) - 1)].get(self.heading(cursor))
        if interval is None:
            return False
        low, high = self.enclose(cursor)
        padding = self._paddings.get(slack)
        if padding is None:
            padding = tuple(-(-slack * norm // _MM_SCALE) for norm in _SLIP_NORMS)
            padding += (0,) * (len(low) - len(_SLIP_AXES))
            self._paddings[slack] = padding
        return all(a - pad <= d and c <= b + pad
                   for a, b, c, d, pad in zip(*interval, low, high, padding, strict=True))


# A planar lattice pose packed into one int: the four coordinates, offset by
# _PACK_BIAS, in 32-bit fields above the heading. Keys are equal exactly when the
# planar poses are, and a move adds a constant per heading, so a reverse layer
# grows by one int addition per pose and move instead of building a tuple.
# Coordinates beyond 2^31 lattice units (107 km) would not fit; no layout comes
# near, and the search's own poses stay within its horizon of the base.
_PACK_BIAS = 1 << 31
_PACK_MASK = (1 << 32) - 1
#: A problem whose anchor, start or base junction lies beyond this many lattice
#: units (53 km) runs on the field engine: the search reaches only metres from
#: them, so its packed poses keep clear of the 2^31 field limit.
_PACK_LIMIT = 1 << 30


def _packable(pose: tuple) -> bool:
    return all(-_PACK_LIMIT < value < _PACK_LIMIT for value in pose[:4])


def _pack_lattice(pose: tuple) -> int:
    """The key of a lattice pose's planar part, whatever its height."""
    a, b, c, d, _z, heading = pose
    return (((a + _PACK_BIAS) << 100) + ((b + _PACK_BIAS) << 68)
            + ((c + _PACK_BIAS) << 36) + ((d + _PACK_BIAS) << 4) + heading)


def _unpack_lattice(key: int) -> tuple:
    """The planar lattice pose of a key: the inverse of :func:`_pack_lattice`."""
    return ((key >> 100) - _PACK_BIAS, ((key >> 68) & _PACK_MASK) - _PACK_BIAS,
            ((key >> 36) & _PACK_MASK) - _PACK_BIAS, ((key >> 4) & _PACK_MASK) - _PACK_BIAS,
            0, key & 15)


class _CompletionReachability:
    """Bounded reverse reachability for planar poses and heights independently.

    Each complete layer contains ALL projections of cursors that can reach the
    anchor in at most that many traversals. The anchor is the closing target of
    either search mode: a fresh loop must return to the origin face exactly as a
    completion must reach its selected end. Separating height from planar geometry
    avoids multiplying states for bridge routes. The two projections may use
    different routes; that only enlarges the set allowed by this check.

    Reversing a physical route is always another legal route,
    so reversing the cursor, taking a move, and reversing again enumerates every
    predecessor. Ignoring placement constraints makes this an overapproximation:
    absence proves impossibility, while membership still needs the full DFS audit.

    Never use a partly built layer. Preprocessing is paid for progressively: a
    small base allowance, more for every DFS node spent, a hard cap. A depth not
    yet affordable stays permissive and is asked again later, so short searches
    never pay for deep tables while long ones earn them.

    The same layers bound the loop a walk must drive before it can pass through
    a junction it places itself: ``transit_floor`` proves how many traversals such
    a return loop needs at least, and a free transit through a junction still in
    stock is only granted when the remaining placements can fit both.
    """

    def __init__(self, eng, horizon: int, max_work: int, *, slippage: bool = False,
                 slop: float = 0.0, budget=None) -> None:
        self.eng = eng
        self.horizon = horizon
        #: In slippage mode the return-loop floors ask with the whole gap budget.
        self.padding = _slack_padding(slop) if slippage and slop > 0 else None
        #: *max_work* caps the total; *budget*, when given, is called for the
        #: allowance currently earned (it only grows during one search).
        self.work_limit = max_work
        self.work_used = 0
        self._budget = budget
        #: Whether the latest answer is final. A rejection always is, and so is a
        #: membership found in a published layer; an answer that is permissive only
        #: because a layer was not yet affordable must be asked again later.
        self.decided = True
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
        # Lattice tables hold packed planar poses (see _pack_lattice) and key()
        # maps a cursor into them; the field keeps exact levelled Pose objects.
        self._lattice = eng.name == "lattice"
        self.key = _pack_lattice if self._lattice else eng.level
        self.layers = [frozenset((self.key(eng.anchor),))]
        self.frontier = self.layers[0]
        self.frontiers = [self.frontier]  # the poses each layer added
        self.height_layers = [frozenset((eng.height(eng.anchor),))]
        self.height_frontier = self.height_layers[0]
        self.bounds = _CompletionBounds(eng, slippage=slippage)
        self.near_indices: dict[int, dict] = {}
        self._boxes: dict = {}  # pose -> physical box, computed once per pose
        # Slippage reads a table entry's heading and box through its key; a
        # queried cursor keeps its own entry under its own tuple.
        if self._lattice:
            enclose = self.bounds.enclose
            self._heading = lambda key: key & 15
            self._enclose = lambda key: enclose(_unpack_lattice(key))
        else:
            self._heading, self._enclose = self.bounds.heading, self.bounds.enclose
        # Moves are rigid, so a predecessor is the pose plus a delta that depends
        # only on the heading. Tabulate it once instead of reversing, moving and
        # reversing again for every expansion. A lattice delta is the difference
        # of two packed poses, so one int addition applies it; the field keeps
        # exact Pose deltas.
        headings = range(12) if self._lattice else range(HEADING_STEPS)
        zero = ((lambda h: (0, 0, 0, 0, 0, h)) if self._lattice
                else (lambda h: Pose.make(heading=h)))
        self.predecessors = []
        self.successors = []
        for heading in headings:
            pose = zero(heading)
            deltas = set()
            forward = set()
            for apply_move in self.moves:
                predecessor = eng.level(eng.reverse(apply_move(eng.reverse(pose))))
                successor = eng.level(apply_move(pose))
                if self._lattice:
                    origin = _pack_lattice(pose)
                    deltas.add(_pack_lattice(predecessor) - origin)
                    forward.add(_pack_lattice(successor) - origin)
                else:
                    deltas.add((predecessor.x, predecessor.y, predecessor.heading))
                    forward.add((successor.x, successor.y, successor.heading))
            self.predecessors.append(tuple(deltas))
            self.successors.append(tuple(forward))
        self.probes = 0
        #: DFS nodes spent by earlier searches that reused these tables; the
        #: progressive allowance keeps counting from there.
        self.nodes_spent = 0
        # Geometry-only answers are independent of stock, stubs, and collisions.
        # Keep this cache on the search object; keys contain only immutable poses.
        self.cache: OrderedDict[tuple, bool] = OrderedDict()
        self.cache_hits = 0
        self.checks = 0
        #: Per junction type the solver may place: from the exit of each of its
        #: routes, the reversed pose of every spare port a later transit could
        #: enter, retargeted onto the anchor.
        self.return_queries: dict[str, tuple] = {}
        self._floors: dict[str, tuple[int, int, bool]] = {}

    @property
    def work_left(self) -> int:
        allowance = self.work_limit
        if self._budget is not None:
            allowance = min(allowance, self._budget())
        return allowance - self.work_used

    def transit_floor(self, pid: str) -> int:
        """Traversals proven too few for a loop back to a junction of type *pid*.

        No return query lies in any complete layer up to the returned depth, so
        such a loop needs more traversals than that. Grows as layers are published
        until the first layer containing a return query fixes it for good.
        """
        queries = self.return_queries.get(pid)
        if not queries:
            return -1
        known, floor, final = self._floors.get(pid, (0, -1, False))
        depth = len(self.layers)
        if final or known >= depth:
            return floor
        key, height = self.key, self.eng.height
        for k in range(known, depth):
            layer, heights = self.layers[k], self.height_layers[k]
            if any(
                height(query) in heights and (
                    key(query) in layer if self.padding is None
                    else self._near_layer(query, k, self.padding)
                )
                for query in queries
            ):
                floor, final = k - 1, True
                break
            floor = k
        self._floors[pid] = (depth, floor, final)
        return floor

    def allows(self, cursor, traversals: int, slack: float | None = None) -> bool:
        # Published layers never change, so a decided answer is exactly what a
        # fresh evaluation would return; only decided answers are cached.
        key = (cursor, traversals) if slack is None else (cursor, traversals, slack)
        result = self.cache.get(key)
        if result is not None:
            self.cache_hits += 1
            self.cache.move_to_end(key)
            self.decided = True
            return result
        result = self._allows(cursor, traversals, slack)
        if self.decided:
            if len(self.cache) >= 4096:
                self.cache.popitem(last=False)
            self.cache[key] = result
        return result

    def _ensure_heights(self, traversals: int) -> bool:
        """Publish height layers up to *traversals*; they stay small and cheap."""
        while len(self.height_layers) <= traversals:
            work = len(self.height_frontier) * len(self.rises)
            if work > self.work_left:
                return False
            self.work_used += work
            previous = self.height_layers[-1]
            frontier = {
                height + rise for height in self.height_frontier for rise in self.rises
            } - previous
            self.height_frontier = frontier
            self.height_layers.append(previous | frontier)
        return True

    def _ensure_layers(self, traversals: int) -> bool:
        """Publish planar layers up to *traversals*; False leaves the query permissive."""
        predecessors = self.predecessors
        while len(self.layers) <= traversals:
            work = len(self.frontier) * len(self.moves)
            if work > self.work_left:
                return False
            self.work_used += work
            previous = self.layers[-1]
            frontier = set()
            if self._lattice:
                for key in self.frontier:
                    for delta in predecessors[key & 15]:
                        predecessor = key + delta
                        if predecessor not in previous:
                            frontier.add(predecessor)
            else:
                for pose in self.frontier:
                    x, y = pose.x, pose.y
                    for dx, dy, next_heading in predecessors[pose.heading]:
                        predecessor = Pose(x + dx, y + dy, 0, next_heading)
                        if predecessor not in previous:
                            frontier.add(predecessor)
            self.frontier = frontier
            self.frontiers.append(frontier)
            self.layers.append(previous | frontier)
        return True

    def _probe(self, cursor, depth: int, gap: int, padding: int | None) -> bool | None:
        """Decide membership in the layer *gap* beyond *depth* by expanding forward.

        A pose reaches the anchor within depth + gap moves exactly when some pose
        at most gap forward moves ahead of it lies in the layer of depth: a route
        of at least gap moves passes such a pose after gap moves, and a shorter
        route ends at the anchor, which every layer contains. Slippage translates
        the remainder of a route, never its first moves, so the near test at the
        built depth serves the same purpose. None means the work cap was hit.
        """
        layer = self.layers[depth]
        successors = self.successors
        lattice = self._lattice
        boxes, enclose, heading_of = self._boxes, self._enclose, self._heading
        near_group = self._near_group
        frontier = {self.key(cursor)}
        expanded = 0
        for step in range(gap + 1):
            if step:
                grown = set()
                if lattice:
                    for key in frontier:
                        for delta in successors[key & 15]:
                            grown.add(key + delta)
                else:
                    for pose in frontier:
                        x, y = pose.x, pose.y
                        for dx, dy, next_heading in successors[pose.heading]:
                            grown.add(Pose(x + dx, y + dy, 0, next_heading))
                frontier = grown
                expanded += len(grown)
                self.probes += len(grown)
                if expanded > _PROBE_WORK:
                    return None
            if padding is None:
                if not frontier.isdisjoint(layer):
                    return True
                continue
            index = self.near_indices.get(depth)
            if index is None:
                index = self._near_index(depth)
            for pose in frontier:
                group = index.get(heading_of(pose))
                if group is None:
                    continue
                box = boxes.get(pose)
                if box is None:
                    low, high = enclose(pose)
                    box = boxes[pose] = (low[0], high[0], low[1], high[1])
                if near_group(box, group, padding):
                    return True
        return False

    def _allows(self, cursor, traversals: int, slack: float | None = None) -> bool:
        self.checks += 1
        self.decided = True
        self.work_used += self.bounds.extend(traversals, self.work_left)
        # One accumulated budget covers every remaining forced transit and the
        # final joint. Translations add; heading and height never acquire tolerance.
        padding = None if slack is None else _slack_padding(slack)
        if padding is None:
            possible = self.bounds.allows(cursor, traversals)
        else:
            possible = self.bounds.allows_near(cursor, traversals, padding)
        if not possible:
            return False
        # An envelope depth not yet affordable leaves its permissive answer open.
        envelope_decided = traversals < len(self.bounds.layers) or self.bounds.saturated
        if traversals > self.horizon + _PROBE_DEPTH:
            self.decided = envelope_decided
            return True
        if not self._ensure_heights(traversals):
            self.decided = False
            return True
        if self.eng.height(cursor) not in self.height_layers[traversals]:
            return False
        # A pose the exact table reaches lies inside every envelope of that depth,
        # so a membership answer is final whether or not the envelope was built.
        if self._ensure_layers(min(traversals, self.horizon)) and traversals <= self.horizon:
            if padding is None:
                return self.key(cursor) in self.layers[traversals]
            return self._near_layer(cursor, traversals, padding)
        depth = len(self.layers) - 1
        gap = traversals - depth
        if gap > _PROBE_DEPTH:
            self.decided = False
            return True
        answer = self._probe(cursor, depth, gap, padding)
        if answer is None:
            self.decided = False
            return True
        return answer

    def _near_index(self, traversals: int) -> dict:
        """Boxes of a layer by heading, sorted by their left edge.

        Layers are cumulative, so the index of depth k is the index of depth k-1
        plus the boxes of the poses that depth added; each pose's box is computed
        once and shared by every depth that contains it.
        """
        boxes, enclose, heading_of = self._boxes, self._enclose, self._heading
        start = max(k for k in range(traversals + 1) if k in self.near_indices or k == 0)
        grouped: dict[int, list] = {}
        if start in self.near_indices:
            grouped = {heading: list(group[0])
                       for heading, group in self.near_indices[start].items()}
            start += 1
        for depth in range(start, traversals + 1):
            for pose in self.frontiers[depth] if depth else self.layers[0]:
                box = boxes.get(pose)
                if box is None:
                    low, high = enclose(pose)
                    box = boxes[pose] = (low[0], high[0], low[1], high[1])
                grouped.setdefault(heading_of(pose), []).append(box)
            index = {}
            for heading, group in grouped.items():
                group.sort()
                index[heading] = (group, tuple(box[0] for box in group),
                                  max(box[1] - box[0] for box in group),
                                  (group[0][0], max(box[1] for box in group),
                                   min(box[2] for box in group), max(box[3] for box in group)))
            self.near_indices[depth] = index
            grouped = {heading: list(group) for heading, group in grouped.items()}
        return self.near_indices[traversals]

    def _near_layer(self, cursor, traversals: int, slack: int) -> bool:
        """Query a complete short layer by physical bounding boxes, not coefficients.

        Sorted x intervals avoid scanning the whole layer for every candidate.
        Box-to-box distance bounds the Euclidean gap from below. The DFS still
        decides the actual fit and audits all of its links and collisions.
        """
        index = self.near_indices.get(traversals)
        if index is None:
            index = self._near_index(traversals)
        group = index.get(self.bounds.heading(cursor))
        if group is None:
            return False
        box = self._boxes.get(cursor)
        if box is None:
            low, high = self.bounds.enclose(cursor)
            box = self._boxes[cursor] = (low[0], high[0], low[1], high[1])
        return self._near_group(box, group, slack)

    @staticmethod
    def _near_group(box: tuple, group: tuple, slack: int) -> bool:
        """Is *box*, grown by *slack*, within reach of some box of one heading group?

        The group's extremes reject most far-away queries with four comparisons;
        the sorted scan then decides the rest exactly as before.
        """
        x0, x1, y0, y1 = box
        left, right = x0 - slack, x1 + slack
        bottom, top = y0 - slack, y1 + slack
        boxes, starts, width, (gx0, gx1, gy0, gy1) = group
        if gx1 < left or gx0 > right or gy1 < bottom or gy0 > top:
            return False
        for i in range(bisect_left(starts, left - width), bisect_right(starts, right)):
            b = boxes[i]
            if b[1] >= left and b[2] <= top and b[3] >= bottom:
                dx = max(0, b[0] - x1, x0 - b[1])
                dy = max(0, b[2] - y1, y0 - b[3])
                if dx * dx + dy * dy <= slack * slack:
                    return True
        return False


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
    exact: bool = False,
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

        walks = [(visits, stub_port)]
        # The lobe after the closing junction can be driven either way round:
        # entering the junction the same way, the walk leaves by the stub port
        # instead and closes into the old exit. An exact closure builds the same
        # layout both ways; a forced fit has its misfit at the closing joint, so
        # its two walks are different layouts.
        first = next((k for k, visit in enumerate(visits) if visit[0] == stub_inst), None)
        if exact and first is not None:
            inst, pid, entry, exit_ = visits[first]
            if (entry, stub_port) in canon_for.get(pid, {}):
                lobe = [(i, p, x, e) for (i, p, e, x) in reversed(visits[first + 1:])]
                walks.append((visits[:first] + [(inst, pid, entry, stub_port)] + lobe, exit_))
        candidates = []
        for walk, port in walks:
            candidates.append(with_join(walk, port))
            mirrored = mirror_of(walk) if cyclic else None
            if mirrored is not None and port_mirror_for is not None:
                stub_pid = pid_of(stub_inst)
                mirrored_port = port_mirror_for.get(stub_pid, {}).get(port)
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
    # The lexicographic minimum over every rotation of every sequence, built
    # one element at a time: only the rotations still tied on the prefix are
    # extended, so a rotation that loses on an early element is never
    # normalised in full. The result is exactly min(normalise(rotation)).
    live = [(seq, start, {}) for seq in sequences for start in range(n)]
    prefix = []
    for k in range(n):
        best = None
        keep = []
        for candidate in live:
            seq, start, fresh = candidate
            inst, pid, entry, exit_ = seq[(start + k) % n]
            ordinal = fresh.get(inst)
            if ordinal is None:
                ordinal = fresh[inst] = len(fresh)
            table = canon_for.get(pid)
            if table is not None:
                entry, exit_ = table.get((entry, exit_), (entry, exit_))
            element = (ordinal, pid, entry, exit_)
            if best is None or element < best:
                best = element
                keep = [candidate]
            elif element == best:
                keep.append(candidate)
        prefix.append(best)
        live = keep
    return tuple(prefix)


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
        pts = placement.centreline_points(spacing)
        half = placement.piece.width / 2.0
        arch = placement.piece.underpass
        if index >= n_base and check.clashes(
            pts, half, neighbours.get(index, set()), underpass=arch
        ):
            return True
        check.add(index, pts, half, underpass=arch)
    return False


_NO_LINKS: frozenset[int] = frozenset()


class _OverlapAudit:
    """The overlap audit of :func:`_solution_overlaps` over one fixed base.

    A closing problem audits every candidate over the same base placements, so
    they are sampled and binned once. Consecutive candidates of one search
    share their first placements, so the field keeps a candidate's placements
    and the next candidate pops only those it does not share. A placement's
    verdict depends on the placements before it, its own samples and the
    indices it is linked to, so a kept placement, identified by its piece and
    frame objects and an unchanged link set, has already seen exactly the point
    tests the standalone audit runs. A layout that does not start with the base
    is audited standalone.
    """

    def __init__(self, base: Layout | None, clearance: float, spacing: float) -> None:
        self.base = base.placements if base is not None else ()
        self.clearance, self.spacing = clearance, spacing
        self.field = CollisionField(clearance=clearance)
        for index, placement in enumerate(self.base):
            self.field.add(index, placement.centreline_points(spacing),
                           placement.piece.width / 2.0, underpass=placement.piece.underpass)
        #: The placements beyond the base in the field, with the links they were
        #: checked under, in field order.
        self.pushed: list[tuple[Placement, frozenset[int] | set[int]]] = []

    def overlaps(self, layout: Layout) -> bool:
        placements = layout.placements
        n_base = len(self.base)
        # Assembled and expanded layouts carry the base's own placement objects,
        # so identity settles the prefix without comparing exact frames.
        if len(placements) < n_base or (
            any(p is not q for p, q in zip(placements, self.base, strict=False))
            and placements[:n_base] != self.base
        ):
            return _solution_overlaps(layout, n_base, self.clearance, self.spacing)
        linked: dict[int, set[int]] = {}
        for (ai, _ap), (bi, _bp) in layout.links.items():
            if ai >= n_base:
                linked.setdefault(ai, set()).add(bi)
        field, spacing, pushed = self.field, self.spacing, self.pushed
        keep = 0
        for placement, (kept, ignore) in zip(placements[n_base:], pushed, strict=False):
            if placement is not kept and (
                placement.piece is not kept.piece or placement.frame is not kept.frame
            ):
                break
            if linked.get(n_base + keep, _NO_LINKS) != ignore:
                break
            keep += 1
        while len(pushed) > keep:
            field.pop()
            pushed.pop()
        for index in range(n_base + keep, len(placements)):
            placement = placements[index]
            pts = placement.centreline_points(spacing)
            half = placement.piece.width / 2.0
            arch = placement.piece.underpass
            ignore = linked.get(index, _NO_LINKS)
            if field.clashes(pts, half, ignore, underpass=arch):
                return True
            field.add(index, pts, half, underpass=arch)
            pushed.append((placement, ignore))
        return False


# --------------------------------------------------------------------------------------
# Configuration and results
# --------------------------------------------------------------------------------------

#: Placements a search stacks at most: far beyond any real box, and well inside
#: Python's default recursion limit with transits and callers on the stack too.
_MAX_SEARCH_DEPTH = 400


@dataclass(frozen=True, slots=True)
class SolverConfig:
    """Knobs for the search."""

    slop: float = 0.0  # total closing gap allowed, mm; 0 = exact closures only
    #: Newly placed pieces in completion mode; zero permits existing-junction
    #: transits without spending inventory (an empty fresh loop is never emitted).
    min_pieces: int = 4
    #: Upper bound on pieces placed (loop length / grown completion length).  With a
    #: huge inventory an unbounded depth-first dive is the enemy: a 300 mm gap needs
    #: a dozen pieces, not two hundred.  None = no bound beyond the recursive search's
    #: own ``_MAX_SEARCH_DEPTH``; either limit reports ``stop_reason="piece_limit"``.
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
    #: Exact reverse reachability for this many final placements of a loop or a
    #: completion, supplemented by longer linear bounds. Zero disables both; they share
    #: a preprocessing allowance of min(4096, max_nodes // 8) expansions plus 24
    #: per DFS node spent, capped at 262,144, so only long searches pay for deep
    #: tables. Slop fits use physical distance enclosures with the remaining
    #: total gap budget.
    completion_lookahead: int = 10
    #: The table allowance a search starts with, instead of min(4096, max_nodes // 8):
    #: a short probe that is part of a larger search keeps the larger one's tables.
    completion_base_work: int | None = None
    #: Optional extra acceptance audit, applied BEFORE the result limit. Rejected
    #: candidates do not consume result slots. Used to validate expanded bridge
    #: assemblies against their actual component joints, not macro exemptions.
    solution_filter: object = None

    def __post_init__(self) -> None:
        if self.solution_filter is not None and not callable(self.solution_filter):
            raise ValueError("solution_filter must be callable or None")
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
        if type(self.completion_lookahead) is not int or not 0 <= self.completion_lookahead <= 12:
            raise ValueError("completion_lookahead must be an integer from 0 to 12")
        if self.completion_base_work is not None and (
            type(self.completion_base_work) is not int or self.completion_base_work < 0
        ):
            raise ValueError("completion_base_work must be a non-negative integer or None")


@dataclass
class SolveStats:
    nodes: int = 0
    closures_found: int = 0  # before deduplication
    pruned_turn: int = 0
    pruned_reach: int = 0
    pruned_collision: int = 0
    pruned_mirror: int = 0  # right-handed first turns skipped in loop mode
    pruned_completion: int = 0
    completion_states: int = 0  # planar states in the largest complete reverse layer
    duration_s: float = 0.0
    aborted: bool = False  # stopped by max_nodes
    engine: str = ""  # which arithmetic backend ran
    #: Candidates rejected by the final actual-link overlap audit. A potential
    #: future joint exempted during search may not be realized in the final trace;
    #: these overlapping candidates are counted here, never returned.
    dropped_overlap: int = 0
    dropped_filter: int = 0  # candidates rejected by the optional acceptance audit
    #: True only after exhausting the entire inventory, not a capped search.
    complete: bool = False
    stop_reason: str = "not_started"
    max_pieces_searched: int = 0
    completion_height_states: int = 0
    completion_work: int = 0
    completion_bound_depth: int = 0
    completion_bound_states: int = 0  # retained heading envelopes across all depths
    completion_checks: int = 0  # geometric queries actually evaluated
    completion_probes: int = 0  # poses expanded by forward probes beyond the built layers
    completion_cache_hits: int = 0  # repeated queries answered by the per-search cache


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


@dataclass
class SearchLimits:
    """Mutable budgets for one explicitly owned, resumable completion iterator.

    Increasing these limits does not restart DFS. ``close()`` the iterator when
    abandoning it; retained geometry belongs to this problem, never to a global
    session cache. Checkpoints bound nodes between yields, not wall-clock latency.
    """

    max_nodes: int = 250_000
    max_results: int = 50
    max_pieces: int = 26
    quantum: int = 32

    def validate(self) -> None:
        for name in ("max_nodes", "max_results", "max_pieces", "quantum"):
            if type(getattr(self, name)) is not int or getattr(self, name) < 1:
                raise ValueError(f"{name} must be a positive integer")


def solve(
    inventory: Mapping[str, int],
    pieces: Mapping[str, PieceType],
    config: SolverConfig | None = None,
    *,
    base: Layout | None = None,
    grow_from: tuple[int, int] | None = None,
    close_onto: tuple[int, int] | None = None,
    tables: dict | None = None,
) -> SolveResult:
    """Run the exact solver to its configured limits (see :func:`solve_steps`).

    The traditional synchronous API and its traversal/counter semantics are kept.
    Interactive callers use ``solve_steps(..., limits=SearchLimits(...))`` instead.
    """
    iterator = solve_steps(inventory, pieces, config, base=base,
                           grow_from=grow_from, close_onto=close_onto, tables=tables)
    try:
        while True:
            next(iterator)
    except StopIteration as done:
        return done.value
    finally:
        iterator.close()


def solve_steps(
    inventory: Mapping[str, int],
    pieces: Mapping[str, PieceType],
    config: SolverConfig | None = None,
    *,
    base: Layout | None = None,
    grow_from: tuple[int, int] | None = None,
    close_onto: tuple[int, int] | None = None,
    tables: dict | None = None,
    limits: SearchLimits | None = None,
) -> Generator[dict, None, SolveResult]:
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
        tables: a dict the caller keeps while it searches one problem repeatedly
            (the same *base* and catalogue, possibly with other ends, stock or
            budgets): the reverse reachability tables one search builds serve the
            next search of the same ends and stock, and keep growing with it.

    Yields:
        With mutable limits, progress/solution/limit checkpoints. Increase a
        budget and advance to continue, or close to release retained state.
        Piece-depth continuation applies to completion mode; fresh-loop mode
        retains its configured full-depth traversal. The return value is a
        SolveResult containing distinct solutions (loop mode: deduplicated up
        to rotation, reflection and starting point), each with a rebuilt
        :class:`~duplotrain.layout.Layout`, plus counters describing how the search went.
    """
    cfg = config or SolverConfig()
    if limits is not None:
        limits.validate()
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
            # Later code compares indices literally: a negative alias of a real
            # port would pass the lookups below and then never match itself.
            if (not isinstance(end, tuple) or len(end) != 2
                    or any(type(value) is not int for value in end)
                    or not 0 <= end[0] < len(base.placements)
                    or not 0 <= end[1] < len(base.placements[end[0]].piece.ports)):
                raise ValueError(f"end {end!r} is not a port of the base layout")
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
    # Closed base pieces are obstacles, not spare traversal moves. Base-only
    # junctions contribute just their still-usable free routes to the relaxation.
    moves_by_piece = _completion_moves(piece_obj, counts, base, grow_from, close_onto)
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

    # Loop mode explores one handedness only. The mirror image of every loop is
    # another loop with the same canonical signature, so a walk whose first
    # turning move is right-handed can only repeat what its left-handed twin
    # finds. That needs every stock traversal to have a buildable mirror twin; a
    # single-handed piece would leave the twin loop unconstructible and its
    # signature distinct. A base breaks the symmetry, so completion mode never does this.
    def _move_sign(move: Move) -> int:
        turn = move.dheading % HEADING_STEPS
        if turn and turn != HEADING_STEPS // 2:
            return 1 if turn < HEADING_STEPS // 2 else -1
        if move.dy == 0:
            return 0
        return 1 if move.dy > 0 else -1

    chirality = {
        (move.piece_id, move.entry, move.exit): _move_sign(move)
        for pid in piece_ids for move in moves_by_piece[pid]
    }
    one_handed = base is None and all(
        twin is not None for pid in piece_ids for twin in mirror_for[pid].values()
    )
    port_mirror_for = {pid: _mirror_ports(p) for pid, p in piece_obj.items()}
    span_of = {pid: _max_span(p) for pid, p in piece_obj.items()}
    turn_of = {pid: _turn_capacity(p) for pid, p in piece_obj.items()}
    overhang_of = {pid: p.end_overhang for pid, p in piece_obj.items()}
    total_pieces = sum(counts.values())

    # Collision samples, precomputed per (piece, entry, frame rotation): the world
    # frame of a placement only ever differs by one of finitely many rotations plus a
    # translation, so the trig happens once here and the hot loop just adds offsets.
    sample_cache: dict[tuple[str, int, int], tuple[list[tuple[float, float, float]], tuple]] = {}

    def placement_samples(pid: str, entry: int, hkey: int, cos_t: float, sin_t: float):
        """Rotated local samples and their bounds; the hot loop only adds offsets."""
        key = (pid, entry, hkey)
        cached = sample_cache.get(key)
        if cached is None:
            piece = pieces[pid]
            base_pts = []
            for line in piece.all_centrelines(cfg.collision_spacing):
                for lx, ly, lz in line:
                    base_pts.append(
                        (cos_t * lx - sin_t * ly, sin_t * lx + cos_t * ly, lz)
                    )
            cached = (base_pts, bounds_of(base_pts))
            sample_cache[key] = cached
        return cached

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
                    if converted is None or not _packable(_flat(converted)):
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
    # Free transits only ever traverse a junction's own routes: those of a base
    # junction with open ports, or of a junction still in stock. The allowance
    # cap bounds every transit count the search can ask for, one extra for the
    # candidate junction a query may add before its stock is consumed.
    # A fresh loop closes onto the origin face exactly as a completion closes onto
    # its target, so the same reverse tables prune walks that cannot return with
    # the traversals left in either mode.
    completion = None
    if cfg.completion_lookahead:
        # The tables depend on the anchor, the move pool and the slop mode only,
        # so a repeated search of the same ends and stock can keep the previous
        # search's tables and the allowance they earned.
        key = (grow_from, close_onto, tuple(sorted(counts.items())), cfg.slop,
               cfg.completion_lookahead, eng.name)
        if tables is not None:
            completion = tables.get(key)
            if completion is not None and completion.eng.anchor != eng.anchor:
                completion = None
        if completion is None:
            completion = _CompletionReachability(eng, cfg.completion_lookahead, _TABLE_WORK_CAP,
                                                 slippage=cfg.slop > 0, slop=cfg.slop)
            if tables is not None:
                tables[key] = completion
        else:
            completion.eng = eng
        spent = completion.nodes_spent
        completion._budget = lambda: _completion_budget(
            spent + stats.nodes, limits.max_nodes if limits else cfg.max_nodes,
            cfg.completion_base_work)
    before = (
        (completion.work_used, completion.checks, completion.probes, completion.cache_hits)
        if completion is not None else (0, 0, 0, 0)
    )
    stub_capacity = {
        pid: max(0, len(pieces[pid].ports) - len(pieces[pid].sealed) - 2)
        if pieces[pid].is_junction else 0
        for pid in piece_ids
    }

    eligible_cache: dict[tuple[str, frozenset[int]], frozenset[int]] = {}

    def eligible_ports(piece: PieceType, ports) -> frozenset[int]:
        # Only ports with an available route partner can participate in a transit.
        key = (piece.id, frozenset(ports))
        eligible = eligible_cache.get(key)
        if eligible is None:
            eligible = eligible_cache[key] = frozenset(
                port for route in piece.routes
                if route.port_a in ports and route.port_b in ports
                for port in (route.port_a, route.port_b)
            )
        return eligible

    def transit_bound(piece: PieceType, ports) -> int:
        # Each transit consumes two ports; this is an upper bound even when routes
        # share a stem. In particular, separate switches' lone stubs cannot pair.
        return len(eligible_ports(piece, ports)) // 2

    future_transits: dict[str, int] = {}
    reversing_queries: dict[str, tuple] = {}
    if completion is not None:
        for pid in piece_ids:
            piece = pieces[pid]
            capacity = 0
            queries = set()
            returns = set()
            if piece.is_junction:
                for entry, exit_port, apply_move in eng.moves[pid]:
                    free = set(range(len(piece.ports))) - piece.sealed - {entry, exit_port}
                    capacity = max(capacity, transit_bound(piece, free))
                    frame = eng.frame(pid, entry, eng.anchor)
                    out = apply_move(eng.anchor)
                    if cfg.reversing_loops:
                        queries.update(
                            eng.retarget(out, eng.reverse(eng.port_world(pid, port, frame)))
                            for port in free
                        )
                    # A later free transit enters a spare port that still has a
                    # route partner; the walk must first loop back to it.
                    returns.update(
                        eng.retarget(out, eng.reverse(eng.port_world(pid, port, frame)))
                        for port in eligible_ports(piece, free)
                    )
            future_transits[pid] = capacity
            reversing_queries[pid] = tuple(queries)
            if capacity:
                completion.return_queries[pid] = tuple(returns)

    steps: list[object] = []
    stubs: list[tuple[int, int, object]] = []  # (placement index, port, engine pose)
    placements: list[tuple[str, object]] = []  # (piece id, engine frame), in order

    if base is not None:
        for index, placement in enumerate(base.placements):
            placements.append((placement.piece.id, None))  # base frames never re-used
            field.add(
                index,
                placement.centreline_points(cfg.collision_spacing),
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
    # A junction from stock may be re-entered once placed and turn the walk again
    # without spending a piece. The quick turn prunes below add that whole
    # potential up front; the tail tables budget these passes exactly.
    pass_turns = sum(turn_of[pid] * n * _spare_passes(piece_obj[pid])
                     for pid, n in counts.items())

    # Admissible per-piece bounds for the completion-mode IDA* contour: one piece
    # advances at most max_span_any millimetres and swings at most max_turn_any
    # heading steps, so pieces-needed >= max(dist/span, need/turn).
    max_span_any = max(span_of.values(), default=1.0) or 1.0
    max_turn_any = max(turn_of.values(), default=0)
    # Without new junctions, each remaining placement contributes at most one
    # stock span. The global longest piece is too optimistic once a scarce bridge
    # has been spent. Take the longest ACTUALLY remaining pieces that fit this
    # contour; existing free transits are discounted separately with stub_reach.
    stock_spans = sorted(((span_of[pid], pid) for pid in piece_ids), reverse=True)
    simple_stock = base is not None and all(
        not piece_obj[pid].is_junction for pid in piece_ids
    )

    def eligible(used: int) -> bool:
        return used >= cfg.min_pieces and (not cfg.use_all_pieces or used == total_pieces)

    # These queries describe a future junction's own geometry, independent of the
    # growing path. Cap the per-search cache now that bounds can check longer tails.
    future_closure: dict[tuple, bool] = {}

    def tail_context(cursor, used: int, slack: float | None):
        # All candidate moves at this DFS node share these allowances and targets.
        # Recursive visits build their own context after consuming stock/stubs;
        # backtracking restores this node's state before the next candidate.
        free_by_placement: dict[int, set[int]] = {}
        for index, port, _pose in stubs:
            free_by_placement.setdefault(index, set()).add(port)
        slots = min(total_pieces, depth_limit, f_limit) - used
        owned = []  # (placement, piece id, transit count, ports with a partner)
        loose = slots
        for index, ports in free_by_placement.items():
            if len(ports) < 2:
                continue
            pid = placements[index][0]
            eligible = eligible_ports(piece_obj[pid], ports)
            count = len(eligible) // 2
            if count:
                owned.append((index, pid, count, eligible))
                loose += count
        max_turn = 0
        future_items = []
        future_targets = []
        for pid in piece_ids:
            count = counts[pid]
            if not count:
                continue
            max_turn = max(max_turn, turn_of[pid])
            free = future_transits[pid]
            if free:
                future_items.append((pid, free, count))
                loose += count * free
            if reversing_queries[pid]:
                future_targets.append(pid)
        # A transit through a junction the walk already owns needs the walk to
        # reach one of that junction's spare entries first. Ask with the loosest
        # traversal count; a candidate one move on can reach no more than this.
        reverse, retarget, allows = eng.reverse, eng.retarget, completion.allows
        entries = [(index, port, reverse(pose)) for index, port, pose in stubs]
        transits = transit_turns = 0
        for index, pid, count, eligible in owned:
            if any(
                allows(retarget(cursor, entry), loose, slack)
                for stub_index, port, entry in entries
                if stub_index == index and port in eligible
            ):
                transits += count
                transit_turns += count * turn_of[pid]
        targets = (tuple(entry for _index, _port, entry in entries)
                   if cfg.reversing_loops else ())
        return (transits, transit_turns, targets, future_targets, max_turn, future_items)

    def tail_budget(context, used: int) -> tuple:
        """The allowances every query with this many pieces used shares."""
        transits, transit_turns, _targets, _future_targets, max_turn, future_items = context
        slots = min(total_pieces, depth_limit, f_limit) - used
        capacity = future = max_free_turn = future_turns = 0
        for pid, free, count in future_items:
            # Placing this junction and looping back to it must fit the remaining
            # placements (existing free transits may shorten the loop); otherwise
            # the tail cannot pass through it and it lends no traversal.
            if slots - 1 + transits <= completion.transit_floor(pid):
                continue
            turn = turn_of[pid]
            capacity = max(capacity, free)
            future += count * free
            max_free_turn = max(max_free_turn, free * turn)
            future_turns += count * free * turn
        transits += min(slots * capacity, future)
        transit_turns += min(slots * max_free_turn, future_turns)
        # A free crossing traversal advances the path but cannot turn it. Keep
        # its actual turning capacity separate from the relaxed traversal count.
        return (slots, slots + transits, transit_turns, min(slots * max_turn, remaining_turn))

    def tail_possible(cursor, budget, context, slack: float | None,
                      extra_pid: str | None = None) -> bool:
        # Callers only ask with reverse tables built (completion is not None).
        if extra_pid and cfg.reversing_loops and stub_capacity[extra_pid]:
            # Its new targets need the placement frame. The recursive visit checks
            # them after placement, with its own updated context.
            return True
        slots, traversals, transit_turns, base_turns = budget
        if extra_pid:
            free = future_transits[extra_pid]
            # This move places the junction; the loop back to it must still fit
            # the placements left after it.
            if free and slots + context[0] > completion.transit_floor(extra_pid):
                traversals += free
                transit_turns += free * turn_of[extra_pid]
        turns = base_turns + transit_turns
        allows = completion.allows
        need_turn24 = eng.need_turn24
        if need_turn24(cursor) <= turns and allows(cursor, traversals, slack):
            return True
        if cfg.reversing_loops:
            targets, future_targets, max_turn = context[2], context[3], context[4]
            retarget = eng.retarget
            for target in targets:
                query = retarget(cursor, target)
                if need_turn24(query) <= turns and allows(query, traversals, slack):
                    return True
            if slots:
                # A future reversing target is created by one placement. Whatever
                # precedes that placement, its exit must reach one of its free ports
                # in at most the remaining traversals. Ignoring the prefix's stock
                # consumption and geometry keeps an overapproximation of every tail.
                for pid in future_targets:
                    # The junction creating this target consumes one placement
                    # and its stock allowance before the tail starts.
                    tail_turns = min((slots - 1) * max_turn,
                                     remaining_turn - turn_of[pid]) + transit_turns
                    key = (pid, traversals - 1, tail_turns, slack)
                    possible = future_closure.get(key)
                    if possible is None:
                        possible = any(need_turn24(query) <= tail_turns
                                       and allows(query, traversals - 1, slack)
                                       for query in reversing_queries[pid])
                        # Rejections are final; a positive is only worth keeping
                        # once the table has decided it rather than deferred it.
                        if (not possible or completion.decided) and len(future_closure) < 4096:
                            future_closure[key] = possible
                    if possible:
                        return True
        return False

    def assemble(reversing_target: tuple[int, int] | None) -> Layout:
        """The layout of the current step trace, from the engine's exact frames.

        Both engines keep exact frames and the trace records every joint, so this
        is what ``_replay`` builds, without re-deriving frames or re-checking
        joints the search has verified; ``_replay`` remains the reference.
        """
        placed = list(base.placements) if base is not None else []
        links = dict(base.links) if base is not None else {}
        cursor, target = grow_from, close_onto
        index = len(base_pids)
        for step in steps:
            if isinstance(step, _Place):
                pid, frame = placements[index]
                placed.append(Placement(pieces[pid], eng.to_pose(frame)))
                if cursor is None:
                    target = (index, step.entry)
                else:
                    links[cursor] = (index, step.entry)
                    links[(index, step.entry)] = cursor
                cursor = (index, step.exit)
                index += 1
            else:
                joint = (step.placement, step.entry)
                links[cursor] = joint
                links[joint] = cursor
                cursor = (step.placement, step.exit)
        if reversing_target is not None:
            target = reversing_target
        links[cursor] = target
        links[target] = cursor
        return Layout(placed, links, base.accessories if base is not None else ())

    ready: list[Solution] = []
    audit: list = []  # one _OverlapAudit over the base, built on the first closure

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
            exact=gap == 0.0,
        )
        if signature in solutions and solutions[signature].gap <= gap:
            return
        layout = assemble(reversing_target)
        if not audit:
            audit.append(_OverlapAudit(base, cfg.clearance, cfg.collision_spacing))
        if audit[0].overlaps(layout):
            stats.dropped_overlap += 1
            return
        candidate = Solution(
            layout=layout,
            steps=tuple(steps),
            gap=gap,
            exact=gap == 0.0,
            open_stubs=len(layout.connectable_ends()),
            signature=signature,
            kind="loop" if reversing_target is None else "reversing",
        )
        if cfg.solution_filter is not None and not cfg.solution_filter(candidate):
            stats.dropped_filter += 1
            return
        solutions[signature] = candidate
        if limits is not None:
            ready.append(candidate)

    def dfs(cursor, used: int, slack_used: float, prev_index: int | None,
            handed: bool) -> Generator[dict, None, bool]:
        """Depth-first over moves; returns False when global limits say stop.

        *prev_index* is the placement owning the connector the walk currently stands
        on -- the last piece placed, or the junction just transited -- which the next
        placement legitimately butts against. *handed* is False only while a
        one-handed loop search has not yet placed a turning move.
        """
        nonlocal remaining_span, remaining_turn
        if limits is not None:
            # Suspended generator frames own the exact DFS/backtracking state.
            # A caller may raise a limit and resume without revisiting any node.
            while len(solutions) >= limits.max_results or stats.nodes >= limits.max_nodes:
                reason = ("result_limit" if len(solutions) >= limits.max_results
                          else "node_limit")
                yield {"kind": reason, "nodes": stats.nodes, "depth": f_limit}
            if stats.nodes % limits.quantum == 0:
                yield {"kind": "progress", "nodes": stats.nodes, "depth": f_limit}
        elif len(solutions) >= cfg.max_results:
            return False
        stats.nodes += 1
        if limits is None and stats.nodes > cfg.max_nodes:
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
                while ready:
                    yield {"kind": "solution", "solution": ready.pop(), "nodes": stats.nodes}
            return True
        if cfg.slop > 0.0 and eligible(used) and closing_link_legal():
            gap = eng.near_anchor(cursor, cfg.slop - slack_used)
            if gap is not None and gap > 0.0:
                emit(slack_used + gap)
                while ready:
                    yield {"kind": "solution", "solution": ready.pop(), "nodes": stats.nodes}
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
        stub_turns = sum(turn_of[placements[s[0]][0]] for s in stubs) + pass_turns
        if need > remaining_turn + stub_turns:
            stats.pruned_turn += 1
            return True
        if simple_stock:
            slots = min(total_pieces, depth_limit, f_limit) - used
            reach = _stock_span_budget(counts, stock_spans, slots)
            if home > reach + stub_reach + (cfg.slop - slack_used) + 1e-6:
                stats.pruned_reach += 1
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

        query_slack = slack_left if cfg.slop > 0 else None
        context = tail_context(cursor, used, query_slack) if completion is not None else None
        if completion is not None and not tail_possible(
            cursor, tail_budget(context, used), context, query_slack
        ):
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
                    while ready:
                        yield {"kind": "solution", "solution": ready.pop(), "nodes": stats.nodes}
                stub_pid = placements[pidx][0]
                piece = piece_obj[stub_pid]  # base-only types are absent from *pieces*
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
                    keep_going = yield from dfs(
                        out_pose, used, slack_used + joint_gap, pidx, handed)
                    steps.pop()
                    stubs[:] = snapshot
                    if not keep_going:
                        return False

        # -- place a new piece -----------------------------------------------------
        if used >= min(depth_limit, f_limit):
            return True
        candidates: list[tuple[float, int, str, int, int, object]] = []
        cursor_overhangs = (
            prev_index is not None and overhang_of[placements[prev_index][0]] > 0
        )
        stub_refs = eng.stub_refs(stubs) if cfg.reversing_loops and stubs else ()
        candidate_score = eng.candidate_score
        for pid in piece_ids:
            if counts[pid] == 0:
                continue
            if cursor_overhangs and overhang_of[pid] > 0:
                continue  # the joint would stack two overhanging plates
            rank = piece_rank[pid]
            for entry, exit_port, apply_move in eng.moves[pid]:
                if not handed and chirality[(pid, entry, exit_port)] < 0:
                    stats.pruned_mirror += 1
                    continue
                child = apply_move(cursor)
                candidates.append(
                    (candidate_score(child, stub_refs), rank, pid, entry, exit_port, child)
                )
        # Try homeward moves first: irrelevant to completeness, decisive for how fast
        # the obvious completion of a small gap is found. (pid, entry, exit) is
        # unique per candidate, so the sort never has to compare the poses.
        candidates.sort()
        child_budget = tail_budget(context, used + 1) if completion is not None else None
        # With no free junctions or reversing targets, reject an out-of-reach
        # child before exact tail queries, collision work, or another DFS node.
        child_reach = None
        if simple_stock and not stubs and not cfg.reversing_loops:
            slots = min(total_pieces, depth_limit, f_limit) - used - 1
            child_reach = {
                pid: _stock_span_budget(counts, stock_spans, slots, consumed=pid)
                for pid in piece_ids if counts[pid]
            }
        for _heuristic, _prio, pid, entry, exit_port, next_cursor in candidates:
            if (child_reach is not None
                    and eng.dist_home(next_cursor) > child_reach[pid] + slack_left + 1e-6):
                stats.pruned_reach += 1
                continue
            # Reject an impossible endpoint before sampling collision geometry or
            # spending a DFS node. Leaving this piece in counts only enlarges the
            # reachability bound, so this early check remains conservative.
            if completion is not None and not tail_possible(
                next_cursor, child_budget, context, query_slack, pid
            ):
                stats.pruned_completion += 1
                continue
            piece = pieces[pid]
            frame = eng.frame(pid, entry, cursor)
            hkey, fx, fy, fz, cos_t, sin_t = eng.frame_floats(frame)
            base_pts, local_bounds = placement_samples(pid, entry, hkey, cos_t, sin_t)
            bounds = (
                local_bounds[0] + fx, local_bounds[1] + fx,
                local_bounds[2] + fy, local_bounds[3] + fy,
                local_bounds[4] + fz, local_bounds[5] + fz,
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
            half_width = piece.width / 2.0
            offset = (fx, fy, fz)
            # Bin and test sample points only when some placement's bounds come
            # within reach; a piece laid clear of everything is deferred as-is.
            grouped_pts = None
            if field.near(bounds, half_width, ignore):
                grouped_pts = field._prepare(base_pts, offset=offset)
                if field._clashes_prepared(
                    grouped_pts, half_width, ignore, underpass=piece.underpass
                ):
                    stats.pruned_collision += 1
                    continue

            counts[pid] -= 1
            remaining_span -= span_of[pid]
            remaining_turn -= turn_of[pid]
            placements.append((pid, frame))
            if grouped_pts is None:
                field.add_deferred(
                    index, base_pts, offset, half_width, bounds, underpass=piece.underpass
                )
            else:
                field._add_prepared(
                    index, grouped_pts, half_width, underpass=piece.underpass, bounds=bounds
                )
            new_stubs = 0
            if piece.is_junction:
                for port_index in range(len(piece.ports)):
                    if port_index in (entry, exit_port) or port_index in piece.sealed:
                        continue
                    stubs.append((index, port_index, eng.port_world(pid, port_index, frame)))
                    new_stubs += 1
            steps.append(_Place(pid, entry, exit_port))

            keep_going = yield from dfs(next_cursor, used + 1, slack_used, index,
                             handed or chirality[(pid, entry, exit_port)] != 0)

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

    # One Python frame per placement or transit: stay well inside the default
    # recursion limit, and report the cut like any other piece limit.
    depth_limit = min(total_pieces, _MAX_SEARCH_DEPTH)
    if cfg.max_pieces is not None:
        depth_limit = min(depth_limit, cfg.max_pieces)
    try:
        if base is None:
            # Loop mode enumerates everything reachable; one full-depth pass.
            f_limit = depth_limit
            stats.max_pieces_searched = f_limit
            yield from dfs(eng.start_cursor, 0, 0.0, start_prev, not one_handed)
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
            f_limit = first_limit
            while True:
                if limits is not None:
                    # A raised piece bound still stays within the recursion cap.
                    depth_limit = min(total_pieces, _MAX_SEARCH_DEPTH, limits.max_pieces)
                    while f_limit > depth_limit and depth_limit < total_pieces:
                        yield {"kind": "piece_limit", "nodes": stats.nodes,
                               "depth": depth_limit}
                        depth_limit = min(total_pieces, _MAX_SEARCH_DEPTH, limits.max_pieces)
                if f_limit > depth_limit:
                    break
                stats.max_pieces_searched = f_limit
                if not (yield from dfs(eng.start_cursor, 0, 0.0, start_prev, not one_handed)):
                    break
                if limits is None and (len(solutions) >= cfg.max_results or stats.aborted):
                    break
                f_limit += 1
    finally:
        # The recursive function owns a cell pointing to itself. Break that
        # cycle once the stack has unwound, so collision fields, geometry and
        # callbacks do not linger until cyclic GC between editor search stages.
        dfs = None
        ready.clear()
        audit.clear()
        if completion is not None:
            completion.nodes_spent += stats.nodes
            if tables is None:
                # Per-search answers are disposable, including on callback
                # errors. Explicitly retained tables keep their answers.
                completion.cache.clear()
                completion.near_indices.clear()
    if stats.aborted:
        stats.stop_reason = "node_limit"
    elif limits is None and len(solutions) >= cfg.max_results:
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
        # Reused tables report only what this search added.
        stats.completion_work = completion.work_used - before[0]
        stats.completion_checks = completion.checks - before[1]
        stats.completion_probes = completion.probes - before[2]
        stats.completion_cache_hits = completion.cache_hits - before[3]
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
