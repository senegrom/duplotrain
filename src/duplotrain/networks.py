"""Enumerate closed track *networks* -- every connector mated or sealed.

The loop solver walks one train path; a network is more general: switches may have
all three branches connected (passing loops, dogbones), buffers may cap sidings, and
no single walk needs to cover everything.  The enumerator grows a layout by always
extending its **canonically smallest open end** -- either attaching a new piece there,
or joining it to another open end that mates exactly.  Acting only on the smallest
end removes permutation blow-up without losing completeness: any target network can
be assembled in exactly that order.

Collision handling is two-phase.  During search, an overlap only prunes when it
happens *away from every open end* (contact near ends may legitimately become a
joint later -- conservative, never cuts a valid network).  Every completed network
then passes a strict pairwise check with only linked neighbours exempt.

Results are deduplicated by curve congruence (:func:`duplotrain.explore.congruence_key`),
i.e. up to rotation, translation and reflection of the embedded track.
"""

from __future__ import annotations

import time
from collections.abc import Mapping
from dataclasses import dataclass

from .explore import congruence_key
from .geometry import ORIGIN
from .layout import Layout
from .pieces import PieceType
from .solver import (
    Move,
    _compile_lattice,
    _FieldEngine,
    _moves_for,
    _traversal_key,
)

__all__ = ["NetworkConfig", "NetworkStats", "NetworkResult", "enumerate_networks"]

#: Contact within this range of an open end may become a legal joint; never prune on it.
JOINT_RADIUS = 70.0


@dataclass(frozen=True, slots=True)
class NetworkConfig:
    min_pieces: int = 2
    max_pieces: int = 18
    max_results: int = 200
    max_nodes: int = 2_000_000
    use_all_pieces: bool = False
    clearance: float = 120.0
    collision_spacing: float = 8.0
    progress: object = None


@dataclass
class NetworkStats:
    nodes: int = 0
    closed_found: int = 0  # before dedup / final validation
    rejected_collision: int = 0
    duration_s: float = 0.0
    aborted: bool = False
    engine: str = ""


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
) -> NetworkResult:
    """All closed networks buildable from *inventory*, up to congruence.

    A network is closed when no connectable end remains: every port is mated to
    another or is a sealed face (buffer bumper).  Collision-legal by construction.
    """
    cfg = config or NetworkConfig()
    for pid in inventory:
        if pid not in pieces:
            raise ValueError(f"inventory names unknown piece {pid!r}")

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
    stats = NetworkStats(engine=eng.name)

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
    clouds: list[tuple[list[tuple[float, float, float]], float]] = []
    links: dict[tuple[int, int], tuple[int, int]] = {}
    open_ends: dict[tuple[int, int], object] = {}  # end -> engine pose
    found: dict[tuple, Layout] = {}
    started = time.perf_counter()

    def end_xy(pose) -> tuple[float, float]:
        if isinstance(pose, tuple):  # lattice flat pose
            from .solver import _flat_xy

            return _flat_xy(pose)
        return pose.xy()

    def conservatively_clashes(pts: list, half_width: float, owner_exempt: int | None) -> bool:
        """Overlap that cannot be excused by any future joint."""
        end_positions = [end_xy(p) for p in open_ends.values()]
        for index, (cloud, other_hw) in enumerate(clouds):
            if index == owner_exempt:
                continue
            limit = half_width + other_hw - 2.0
            limit_sq = limit * limit
            for x, y, z in pts:
                near_end = any(
                    (x - ex) * (x - ex) + (y - ey) * (y - ey) < JOINT_RADIUS * JOINT_RADIUS
                    for ex, ey in end_positions
                )
                if near_end:
                    continue
                for px, py, pz, in cloud:
                    if abs(z - pz) >= cfg.clearance:
                        continue
                    if (x - px) * (x - px) + (y - py) * (y - py) < limit_sq:
                        return True
        return False

    def strictly_valid(layout: Layout) -> bool:
        """Final pairwise check: only linked neighbours may touch."""
        placement_clouds = []
        for placement in layout:
            pts = [p for line in placement.centrelines(cfg.collision_spacing) for p in line]
            placement_clouds.append((pts, placement.piece.width / 2.0))
        linked = {tuple(sorted((a[0], b[0]))) for a, b in layout.links.items()}
        for i, (pa, ha) in enumerate(placement_clouds):
            for j in range(i + 1, len(placement_clouds)):
                if (i, j) in linked:
                    continue
                pb, hb = placement_clouds[j]
                limit = ha + hb - 2.0
                limit_sq = limit * limit
                for x, y, z in pa:
                    for px, py, pz in pb:
                        if abs(z - pz) >= cfg.clearance:
                            continue
                        if (x - px) * (x - px) + (y - py) * (y - py) < limit_sq:
                            return False
        return True

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
        if not strictly_valid(layout):
            stats.rejected_collision += 1
            return
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
                    if conservatively_clashes(pts, piece.width / 2.0, target[0]):
                        continue
                    index = len(placements)
                    placements.append((pid, frame, entry))
                    clouds.append(([(x, y, z) for x, y, z in pts], piece.width / 2.0))
                    counts[pid] -= 1
                    del open_ends[target]
                    links[target] = (index, entry)
                    links[(index, entry)] = target
                    new_ends = []
                    for port in range(len(piece.ports)):
                        if port == entry or port in piece.sealed:
                            continue
                        pose = eng.port_world(pid, port, frame)
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
                    clouds.pop()
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
        clouds.append(([(x, y, z) for x, y, z in pts], piece.width / 2.0))
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
        clouds.pop()
        placements.pop()
        if not keep:
            break

    stats.duration_s = time.perf_counter() - started
    return NetworkResult(layouts=list(found.values()), stats=stats)