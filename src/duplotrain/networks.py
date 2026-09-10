"""Enumerate closed track *networks* -- every connector mated or sealed.

The loop solver walks one train path; a network is more general: switches may have
all three branches connected (passing loops, dogbones), buffers may cap sidings, and
no single walk needs to cover everything.  The enumerator grows a layout by always
extending its **canonically smallest open end** -- either attaching a new piece there,
or joining it to another open end that mates exactly.  Acting only on the smallest
end removes permutation blow-up without losing completeness: any target network can
be assembled in exactly that order.

Collision handling is two-phase. During search, already attached neighbours and
placements with exactly mating open connectors are exempt: they can still become
directly linked. No fixed distance or piece width is assumed. Every completed
network then passes a strict check with only actually linked neighbours exempt.

Results are deduplicated by curve congruence (:func:`duplotrain.explore.congruence_key`),
i.e. up to rotation, translation and reflection of the embedded track.
"""

from __future__ import annotations

import time
from collections.abc import Callable, Mapping
from dataclasses import dataclass

from .collision import DEFAULT_CLEARANCE, CollisionField
from .explore import congruence_key
from .geometry import ORIGIN
from .layout import End, Layout
from .pieces import PieceType
from .solver import (
    Move,
    SolverConfig,
    _compile_lattice,
    _FieldEngine,
    _moves_for,
    _solution_overlaps,
    _traversal_key,
)
from .validation import check_inventory

__all__ = ["NetworkConfig", "NetworkStats", "NetworkResult", "enumerate_networks"]


@dataclass(frozen=True, slots=True)
class NetworkConfig:
    min_pieces: int = 2
    max_pieces: int = 18
    max_results: int = 200
    max_nodes: int = 2_000_000
    use_all_pieces: bool = False
    clearance: float = DEFAULT_CLEARANCE
    collision_spacing: float = 8.0
    progress: object = None

    def __post_init__(self) -> None:
        # Keep the two public search configurations on the same numeric contract.
        if type(self.max_pieces) is not int or self.max_pieces < 1:
            raise ValueError("max_pieces must be a positive integer")
        SolverConfig(
            min_pieces=self.min_pieces, max_pieces=self.max_pieces,
            max_results=self.max_results, max_nodes=self.max_nodes,
            clearance=self.clearance, collision_spacing=self.collision_spacing,
        )


@dataclass
class NetworkStats:
    nodes: int = 0
    closed_found: int = 0  # before dedup / final validation
    rejected_collision: int = 0
    duration_s: float = 0.0
    aborted: bool = False
    engine: str = ""
    #: Entire inventory exhausted, not merely the configured piece bound.
    complete: bool = False
    stop_reason: str = "not_started"
    max_pieces_searched: int = 0


@dataclass
class NetworkResult:
    layouts: list[Layout]
    stats: NetworkStats


def _attach_orientations(piece: PieceType) -> list[int]:
    """Entry ports giving geometrically distinct placements against a fixed end."""
    seen: set = set()
    entries: list[int] = []
    for entry in range(len(piece.ports)):
        if entry in piece.sealed:
            continue
        exits = piece.transit(entry)
        exit_port = exits[0][0] if exits else entry
        signature = _traversal_key(piece, entry, exit_port)[0]
        if signature in seen:
            continue
        seen.add(signature)
        entries.append(entry)
    return entries


def enumerate_networks(
    inventory: Mapping[str, int],
    pieces: Mapping[str, PieceType],
    config: NetworkConfig | None = None,
    *,
    accept: Callable[[Layout], bool] | None = None,
) -> NetworkResult:
    """All closed networks buildable from *inventory*, up to congruence.

    A network is closed when no connectable end remains: every port is mated to
    another or is a sealed face (buffer bumper). Collision-legal by construction.
    Optional *accept* filters collision-legal realizations BEFORE congruence dedup:
    rejecting one must not hide a different, eligible realization of that curve.
    ``max_results`` counts accepted distinct curves. Inspect ``stats.complete``
    and ``stats.stop_reason`` before interpreting a result as exhaustive.
    """
    cfg = config or NetworkConfig()
    check_inventory(inventory, pieces)

    counts = {pid: n for pid, n in inventory.items() if n > 0}
    piece_ids = sorted(counts)
    piece_obj = {pid: pieces[pid] for pid in piece_ids}
    moves_by_piece: dict[str, list[Move]] = {pid: _moves_for(pieces[pid]) for pid in piece_ids}
    orientations = {pid: _attach_orientations(pieces[pid]) for pid in piece_ids}
    overhang_of = {pid: pieces[pid].end_overhang for pid in piece_ids}
    total = sum(counts.values())

    eng = _compile_lattice(ORIGIN, ORIGIN, piece_obj, moves_by_piece)
    if eng is None:
        eng = _FieldEngine(ORIGIN, ORIGIN, piece_obj, moves_by_piece)
    stats = NetworkStats(
        engine=eng.name, max_pieces_searched=min(total, cfg.max_pieces)
    )

    # Per-placement sample clouds (world floats) for the two collision phases.
    sample_cache: dict[tuple[str, int, int], list[tuple[float, float, float]]] = {}

    def samples_for(pid: str, entry: int, frame) -> list[tuple[float, float, float]]:
        hkey, fx, fy, fz, cos_t, sin_t = eng.frame_floats(frame)
        key = (pid, entry, hkey)
        base = sample_cache.get(key)
        if base is None:
            base = []
            for line in pieces[pid].all_centrelines(cfg.collision_spacing):
                for lx, ly, lz in line:
                    base.append((cos_t * lx - sin_t * ly, sin_t * lx + cos_t * ly, lz))
            sample_cache[key] = base
        return [(fx + x, fy + y, fz + z) for x, y, z in base]

    placements: list[tuple[str, object, int]] = []  # (pid, engine frame, entry used)
    field = CollisionField(clearance=cfg.clearance)
    links: dict[tuple[int, int], tuple[int, int]] = {}
    open_ends: dict[tuple[int, int], object] = {}  # end -> engine pose
    found: dict[tuple, Layout] = {}
    started = time.perf_counter()

    def potential_neighbours(port_poses: Mapping[int, object], target: End) -> set[int]:
        """Owners that could become directly linked to the new, fixed placement.

        The final audit exempts whole linked pieces, not just points near a joint.
        A future direct joint must already have exactly mating open ports: neither
        placement moves during search. Matching owners is therefore conservative
        for wide, bent and multi-path pieces alike; a radius around a joint is not.
        Merely nearby ends, wrong headings and different heights are not exempt.
        """
        return {target[0]} | {
            end[0] for end, pose in open_ends.items()
            if end != target and any(eng.connects(new, pose) for new in port_poses.values())
        }

    # Layout reconstruction: replay placements in order.  Each placement after the
    # first was attached at a specific open end recorded during search.
    attach_trace: list[tuple[str, int, tuple[int, int] | None]] = []
    join_trace_all: list[list[tuple[tuple[int, int], tuple[int, int]]]] = []

    def rebuild() -> Layout:
        layout = Layout()
        for (pid, entry, at), joins in zip(attach_trace, join_trace_all, strict=True):
            piece = pieces[pid]
            if at is None:
                layout, _ = layout.with_piece(piece, piece.frame_for(entry, ORIGIN))
            else:
                layout, _ = layout.attach(piece, entry, at)
            for a, b in joins:
                layout = layout.join(a, b)
        return layout

    def emit() -> None:
        stats.closed_found += 1
        layout = rebuild()
        key = congruence_key(layout)
        if key in found:
            return
        if _solution_overlaps(layout, 0, cfg.clearance, cfg.collision_spacing):
            stats.rejected_collision += 1
            return
        if accept is not None and not accept(layout):
            return  # Do not reserve the curve key for an ineligible realization.
        found[key] = layout

    def dfs(used: int) -> bool:
        if len(found) >= cfg.max_results:
            return False
        stats.nodes += 1
        if stats.nodes > cfg.max_nodes:
            stats.aborted = True
            return False
        if cfg.progress is not None and stats.nodes % 4096 == 0:
            cfg.progress(stats.nodes)

        if not open_ends:
            if used >= cfg.min_pieces and (not cfg.use_all_pieces or used == total):
                emit()
            return True

        target = min(open_ends)  # the canonical end everything must go through
        target_pose = open_ends[target]
        target_pid = placements[target[0]][0]

        # -- move 1: join the target end to another open end that mates exactly ----
        for other, pose in sorted(open_ends.items()):
            if other == target:
                continue
            if not eng.connects(target_pose, pose):
                continue
            if overhang_of[target_pid] > 0 and overhang_of[placements[other[0]][0]] > 0:
                continue
            del open_ends[target]
            del open_ends[other]
            links[target] = other
            links[other] = target
            join_trace_all[-1].append((target, other))
            keep = dfs(used)
            join_trace_all[-1].pop()
            del links[target]
            del links[other]
            open_ends[target] = target_pose
            open_ends[other] = pose
            if not keep:
                return False

        # -- move 2: attach a new piece at the target end ---------------------------
        if used < cfg.max_pieces:
            for pid in piece_ids:
                if counts[pid] == 0:
                    continue
                piece = pieces[pid]
                if overhang_of[target_pid] > 0 and overhang_of[pid] > 0:
                    continue
                for entry in orientations[pid]:
                    frame = eng.frame(pid, entry, target_pose)
                    pts = samples_for(pid, entry, frame)
                    port_poses = {
                        port: eng.port_world(pid, port, frame)
                        for port in range(len(piece.ports))
                        if port != entry and port not in piece.sealed
                    }
                    if field.clashes(
                        pts, piece.width / 2.0, potential_neighbours(port_poses, target),
                        underpass=piece.underpass,
                    ):
                        continue
                    index = len(placements)
                    placements.append((pid, frame, entry))
                    field.add(index, pts, piece.width / 2.0, underpass=piece.underpass)
                    counts[pid] -= 1
                    del open_ends[target]
                    links[target] = (index, entry)
                    links[(index, entry)] = target
                    new_ends = []
                    for port, pose in port_poses.items():
                        open_ends[(index, port)] = pose
                        new_ends.append((index, port))
                    attach_trace.append((pid, entry, target))
                    join_trace_all.append([])

                    keep = dfs(used + 1)

                    attach_trace.pop()
                    join_trace_all.pop()
                    for end in new_ends:
                        del open_ends[end]
                    del links[target]
                    del links[(index, entry)]
                    open_ends[target] = target_pose
                    counts[pid] += 1
                    field.pop()
                    placements.pop()
                    if not keep:
                        return False
        return True

    # Root: each distinct piece type starts the network once, anchored at the origin.
    for pid in piece_ids:
        piece = pieces[pid]
        entry = orientations[pid][0]
        frame = eng.frame(pid, entry, eng.start_cursor)
        placements.append((pid, frame, entry))
        pts = samples_for(pid, entry, frame)
        field.add(0, pts, piece.width / 2.0, underpass=piece.underpass)
        counts[pid] -= 1
        for port in range(len(piece.ports)):
            if port in piece.sealed:
                continue
            open_ends[(0, port)] = eng.port_world(pid, port, frame)
        attach_trace.append((pid, entry, None))
        join_trace_all.append([])

        keep = dfs(1)

        attach_trace.pop()
        join_trace_all.pop()
        open_ends.clear()
        counts[pid] += 1
        field.pop()
        placements.pop()
        if not keep:
            break

    if stats.aborted:
        stats.stop_reason = "node_limit"
    elif len(found) >= cfg.max_results:
        stats.stop_reason = "result_limit"
    elif cfg.max_pieces < total:
        stats.stop_reason = "piece_limit"
    else:
        stats.complete = True
        stats.stop_reason = "exhausted"
    stats.duration_s = time.perf_counter() - started
    return NetworkResult(layouts=list(found.values()), stats=stats)
