"""The complete standard bridge as one search move, for the editor's bridge stage.

The stage (see ``editor_search.PairSearch``) is a heuristic, not an exhaustive
search: it tries at most one complete ramp/span/span/ramp assembly plus ordinary
track, and the full-inventory stage remains the fallback. Every macro is expanded
and audited with the real pieces before publication.
"""

from __future__ import annotations

from collections.abc import Mapping

from .catalog import default_catalog
from .geometry import ORIGIN
from .layout import End, Layout, Placement, build_chain
from .pieces import Path, PieceType, Port, Ramp, Route

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

