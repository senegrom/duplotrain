"""Bounded, floor-level bridge completions for the editor.

This is a heuristic stage, not an exhaustive search: it tries at most one complete
ramp/span/span/ramp assembly plus ordinary track. The general solver remains the
fallback. Every macro is expanded and audited with the real pieces before publication.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import replace

from .catalog import default_catalog
from .collision import DEFAULT_CLEARANCE
from .exact import ZERO
from .geometry import ORIGIN
from .layout import End, Layout, Placement, build_chain
from .pieces import Path, PieceType, Port, Ramp, Route
from .solver import Solution, SolverConfig, SolveResult, _solution_overlaps, solve

_BRIDGE_ID = "_completion_bridge"
_RECIPE = (("ramp", 0, 1), ("span", 0, 1), ("span", 1, 0), ("ramp", 1, 0))


def _bridge(catalog: Mapping[str, PieceType]) -> tuple[PieceType, Layout] | None:
    """Build the macro from the actual standard geometry, never an approximate line.

    A custom catalogue may change widths, overhangs, port order or clearance flags.
    Defer to the general solver in that case instead of misrepresenting its pieces.
    """
    standard = default_catalog()
    if _BRIDGE_ID in catalog or any(
        catalog.get(pid) != standard[pid] for pid in ("ramp", "span")
    ):
        return None
    ramp = catalog["ramp"].paths[0].segments[0]
    span = catalog["span"].paths[0].segments[0]
    path = Path(ORIGIN, (ramp, span, Ramp(span.run, -span.rise), Ramp(ramp.run, -ramp.rise)))
    macro = PieceType(
        id=_BRIDGE_ID, name="Complete standard bridge", category="bridge",
        paths=(path,), ports=(Port("in", ORIGIN.reversed()), Port("out", path.end())),
        routes=(Route(0, 1, 0),), width=catalog["ramp"].width,
        underpass=catalog["ramp"].underpass and catalog["span"].underpass,
    )
    parts = build_chain((catalog[pid], entry, exit_) for pid, entry, exit_ in _RECIPE)
    return macro, parts


def _expand(layout: Layout, parts: Layout) -> Layout:
    """Replace macros without changing any original placement, link or action stone."""
    placements: list[Placement] = []
    ends: dict[End, End] = {}
    links: dict[End, End] = {}
    indices: dict[int, int] = {}
    for index, placement in enumerate(layout):
        offset = len(placements)
        indices[index] = offset
        if placement.piece.id != _BRIDGE_ID:
            placements.append(placement)
            for port in range(len(placement.piece.ports)):
                ends[index, port] = (offset, port)
            continue
        for part in parts:
            local = part.frame
            frame = placement.frame.then(local.x, local.y, local.z, local.heading)
            placements.append(Placement(part.piece, frame))
        for (ai, ap), (bi, bp) in parts.links.items():
            links[offset + ai, ap] = (offset + bi, bp)
        ends[index, 0] = (offset, 0)
        ends[index, 1] = (offset + 3, 0)
    for a, b in layout.links.items():
        links[ends[a]] = ends[b]
    accessories = tuple((indices[entry[0]], *entry[1:]) for entry in layout.accessories)
    return Layout(tuple(placements), links, accessories)


def bridge_completion(
    base: Layout,
    catalog: Mapping[str, PieceType],
    remaining: Mapping[str, int],
    grow: End,
    close: End,
    *,
    max_pieces: int,
    max_results: int,
    max_nodes: int,
    progress: object = None,
) -> SolveResult | None:
    """Try one conventional bridge, counting all four components against the limits.

    Restricting this stage to ground-level ends avoids floating curves and inverted
    bridges. Other elevations and multiple bridges remain available to the fallback.
    A macro costs one search move but four real pieces, so reserve three slots. This
    deliberately under-searches bridge-free routes; the plain stage handles those.
    """
    if (max_pieces < 4 or remaining.get("ramp", 0) < 2 or remaining.get("span", 0) < 2
            or base.pose_of(grow).z != ZERO or base.pose_of(close).z != ZERO):
        return None
    bridge = _bridge(catalog)
    if bridge is None:
        return None
    macro, parts = bridge
    inventory = {pid: n for pid in ("curve", "straight")
                 if (n := remaining.get(pid, 0)) > 0}
    inventory[_BRIDGE_ID] = 1
    result = solve(
        inventory, {**catalog, _BRIDGE_ID: macro},
        SolverConfig(min_pieces=0, max_pieces=max_pieces - 3, max_results=max_results,
                     max_nodes=max_nodes, progress=progress),
        base=base, grow_from=grow, close_onto=close,
    )
    candidates: list[Solution] = []
    before = base.piece_counts
    for candidate in result.solutions:
        expanded = _expand(candidate.layout, parts)
        # Macro adjacency exemptions are broader than those of its components.
        # Only the expanded actual-link audit is authoritative for publication.
        if len(expanded) - len(base) > max_pieces or any(
            n - before.get(pid, 0) > remaining.get(pid, 0)
            for pid, n in expanded.piece_counts.items()
        ):
            continue
        if any(
            placement.frame.z != ZERO
            for placement in expanded.placements[len(base):]
            if placement.piece.id in ("curve", "straight", "ramp")
        ):
            continue
        if expanded.joint_issues() or _solution_overlaps(
            expanded, len(base), DEFAULT_CLEARANCE, 8.0
        ):
            continue
        candidates.append(replace(
            candidate, layout=expanded, steps=(),
            signature=("standard_bridge", candidate.signature),
        ))
    # Even an exhausted macro search proves nothing about the whole inventory.
    return SolveResult(candidates, replace(
        result.stats, complete=False, stop_reason="bridge_search",
        max_pieces_searched=result.stats.max_pieces_searched + 3,
    ))
