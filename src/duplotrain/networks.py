"""Enumerate closed track *networks* -- every connector mated or sealed.

The loop solver walks one train path; a network is more general: switches may have
all three branches connected (passing loops, dogbones), buffers may cap sidings, and
no single walk needs to cover everything.  The enumerator grows a layout by always
extending its **canonically smallest open end** -- either attaching a new piece there,
or joining it to another open end that mates exactly.  Acting only on the smallest
end removes permutation blow-up without losing completeness: any target network can
be assembled in exactly that order.  Each piece type roots the search once; a pass
withdraws the types whose passes came earlier, since every network containing one of
them was found by then and the withdrawn subtrees could only rediscover them.

Collision handling is two-phase. During search, already attached neighbours and
placements with exactly mating open connectors are exempt: they can still become
directly linked. No fixed distance or piece width is assumed. Every completed
network then passes a strict check with only actually linked neighbours exempt.

Pruning reuses the loop solver's reverse reachability tables. In a closed
network every open end of the current layout is mated, so some walk over the
new pieces leads from it to another current open end, or to a spare port of a
junction the walk itself placed; with the pieces left that walk must fit, or the
subtree holds no closed network. A buffer in stock could cap any end instead,
so the check is skipped while a piece with a sealed or route-less port remains.

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
from .layout import End, Layout, Placement
from .pieces import PieceType
from .solver import (
    _MAX_SEARCH_DEPTH,
    _TABLE_WORK_CAP,
    Move,
    SolverConfig,
    _compile_lattice,
    _completion_budget,
    _CompletionReachability,
    _FieldEngine,
    _moves_for,
    _placement_samples,
    _solution_overlaps,
)
from .symmetry import placement_key
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
    #: Exact reverse reachability for this many final placements, as
    #: ``SolverConfig.completion_lookahead``; zero disables the pruning.
    lookahead: int = 10

    def __post_init__(self) -> None:
        # Keep the two public search configurations on the same numeric contract.
        if type(self.max_pieces) is not int or self.max_pieces < 1:
            raise ValueError("max_pieces must be a positive integer")
        SolverConfig(
            min_pieces=self.min_pieces, max_pieces=self.max_pieces,
            max_results=self.max_results, max_nodes=self.max_nodes,
            clearance=self.clearance, collision_spacing=self.collision_spacing,
            completion_lookahead=self.lookahead,
        )


@dataclass
class NetworkStats:
    nodes: int = 0
    pruned_reachability: int = 0  # subtrees whose open ends can no longer all mate
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
        signature = placement_key(piece, piece.frame_for(entry, ORIGIN))
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
    # The recursive search places at most the solver's depth of pieces; a larger
    # bound would overflow the stack instead of reporting the piece limit.
    max_pieces = min(cfg.max_pieces, _MAX_SEARCH_DEPTH)

    eng = _compile_lattice(ORIGIN, ORIGIN, piece_obj, moves_by_piece)
    if eng is None:
        eng = _FieldEngine(ORIGIN, ORIGIN, piece_obj, moves_by_piece)
    stats = NetworkStats(
        engine=eng.name, max_pieces_searched=min(total, max_pieces)
    )

    # Reverse reachability, anchored at the origin like the loop solver's: a
    # query asks whether one pose can reach another within so many traversals
    # of stock routes, after the rigid motion that puts the target on the anchor.
    completion = (
        _CompletionReachability(eng, cfg.lookahead, _TABLE_WORK_CAP,
                                budget=lambda: _completion_budget(stats.nodes, cfg.max_nodes))
        if cfg.lookahead else None
    )
    # A piece with a sealed port, or a connectable port no route serves, can
    # terminate a walk without mating another end: each such port caps one
    # open end, so stranded ends are only impossible beyond the stock's caps.
    caps = {
        pid: len(pieces[pid].sealed) + sum(
            not pieces[pid].transit(port)
            for port in range(len(pieces[pid].ports)) if port not in pieces[pid].sealed
        )
        for pid in piece_ids
    }
    caps = {pid: capacity for pid, capacity in caps.items() if capacity}
    # A walk may also end at a spare port of a junction it placed itself. From
    # that junction's exit the spare ports' reversed poses, retargeted onto the
    # anchor, describe the loop back regardless of where the junction stands.
    closing_queries: dict[str, tuple] = {}
    for pid in piece_ids:
        piece = pieces[pid]
        if pid in caps or not piece.is_junction:
            continue
        queries = set()
        for entry, exit_port, apply_move in eng.moves[pid]:
            frame = eng.frame(pid, entry, eng.anchor)
            out = apply_move(eng.anchor)
            queries.update(
                eng.retarget(out, eng.reverse(eng.port_world(pid, port, frame)))
                for port in range(len(piece.ports))
                if port not in (entry, exit_port) and port not in piece.sealed
            )
        closing_queries[pid] = tuple(queries)

    # Types withdrawn from the current root pass (see the root loop below),
    # and the pieces the pass can still place.
    withdrawn: dict[str, int] = {}
    pass_total = [total]

    def closable(used: int) -> bool:
        """False proves that no closed network extends the current layout."""
        if completion is None:
            return True
        budget = min(pass_total[0], max_pieces) - used
        allows = completion.allows
        if budget and any(
            counts[pid] and allows(query, budget - 1)
            for pid, queries in closing_queries.items() for query in queries
        ):
            return True
        # Any cap in stock could end a walk anywhere, and two walks can trail
        # into one new junction whose third port a single cap then closes: with
        # a cap left, no end is provably stranded.
        if any(counts[pid] for pid in caps):
            return True
        reverse, retarget = eng.reverse, eng.retarget
        ends = list(open_ends.values())
        mates = [reverse(pose) for pose in ends]
        return all(
            any(allows(retarget(pose, mate), budget) for j, mate in enumerate(mates) if j != i)
            for i, pose in enumerate(ends)
        )

    # The field bins a candidate's samples once some placement's bounds come within reach.
    samples_for = _placement_samples(eng, pieces, cfg.collision_spacing)

    placements: list[tuple[str, object]] = []  # (pid, engine frame)
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

    def rebuild() -> Layout:
        # Both engines keep exact frames, and the link map is the search's own
        # symmetric one, so the layout is assembled directly rather than replaying
        # every attachment and join through Layout's checked constructors.
        return Layout(
            [Placement(pieces[pid], eng.to_pose(frame)) for pid, frame in placements],
            dict(links),
        )

    def emit() -> None:
        layout = rebuild()
        key = congruence_key(layout)
        if key in found:
            return
        if _solution_overlaps(layout, 0, cfg.clearance, cfg.collision_spacing):
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

        if not open_ends:
            if used >= cfg.min_pieces and (not cfg.use_all_pieces or used == total):
                emit()
            return True
        if not closable(used):
            stats.pruned_reachability += 1
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
            keep = dfs(used)
            del links[target]
            del links[other]
            open_ends[target] = target_pose
            open_ends[other] = pose
            if not keep:
                return False

        # -- move 2: attach a new piece at the target end ---------------------------
        if used < max_pieces:
            for pid in piece_ids:
                if counts[pid] == 0:
                    continue
                piece = pieces[pid]
                if overhang_of[target_pid] > 0 and overhang_of[pid] > 0:
                    continue
                for entry in orientations[pid]:
                    frame = eng.frame(pid, entry, target_pose)
                    base_pts, offset, bounds = samples_for(pid, frame)
                    port_poses = {
                        port: eng.port_world(pid, port, frame)
                        for port in range(len(piece.ports))
                        if port != entry and port not in piece.sealed
                    }
                    exempt = potential_neighbours(port_poses, target)
                    index = len(placements)
                    if not field.place(index, base_pts, offset, piece.width / 2.0, bounds,
                                       exempt, underpass=piece.underpass):
                        continue
                    placements.append((pid, frame))
                    counts[pid] -= 1
                    del open_ends[target]
                    links[target] = (index, entry)
                    links[(index, entry)] = target
                    new_ends = []
                    for port, pose in port_poses.items():
                        open_ends[(index, port)] = pose
                        new_ends.append((index, port))

                    keep = dfs(used + 1)

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

    # Root: each distinct piece type starts the network once, anchored at the
    # origin. A network is found by the pass of every type it contains, so a
    # pass withdraws every type whose own pass came earlier: those passes found
    # each network containing it already, and the withdrawn subtrees could only
    # rediscover them. The classes found, and the order they are found in, are
    # therefore unchanged. When every piece is required, only the first pass can
    # use the whole inventory.
    try:
        for pid in piece_ids:
            if withdrawn and cfg.use_all_pieces:
                break
            piece = pieces[pid]
            entry = orientations[pid][0]
            frame = eng.frame(pid, entry, eng.start_cursor)
            placements.append((pid, frame))
            base_pts, offset, bounds = samples_for(pid, frame)
            field._add_prepared(
                0, field._prepare(base_pts, offset=offset), piece.width / 2.0,
                underpass=piece.underpass, bounds=bounds,
            )
            counts[pid] -= 1
            for port in range(len(piece.ports)):
                if port in piece.sealed:
                    continue
                open_ends[(0, port)] = eng.port_world(pid, port, frame)

            keep = dfs(1)

            open_ends.clear()
            counts[pid] += 1
            field.pop()
            placements.pop()
            if not keep:
                break
            withdrawn[pid] = counts[pid]
            counts[pid] = 0
            pass_total[0] = total - sum(withdrawn.values())
    finally:
        # The recursive function owns a cell pointing to itself. Break that
        # cycle, so the collision field and the reachability tables do not
        # linger until cyclic GC.
        dfs = None

    if stats.aborted:
        stats.stop_reason = "node_limit"
    elif len(found) >= cfg.max_results:
        stats.stop_reason = "result_limit"
    elif max_pieces < total:
        stats.stop_reason = "piece_limit"
    else:
        stats.complete = True
        stats.stop_reason = "exhausted"
    stats.duration_s = time.perf_counter() - started
    return NetworkResult(layouts=list(found.values()), stats=stats)
