"""Overlap detection between placed pieces.

Each placement contributes the sampled centrelines of its paths; two placements clash
when any two of their sample points come closer than the sum of their half-widths
(minus a small margin so that exactly-touching parallel tracks stay legal -- sidings
laid side by side are a feature, not a collision).

Height is respected two ways.  Points whose elevations differ by at least
``clearance`` pass over each other freely -- a blanket rule no current piece can
reach.  Separately, pieces flagged ``underpass`` (the bridge arch span: an open
arch, unlike the solid ramps) let track run beneath wherever their deck stands at
least ``UNDERPASS_MIN`` higher: with the current bridge profile that opens a window
around the mid-bridge crest only, matching the user's observation that a train
passes under the arch there but never under the ramps.

Directly-linked placements are exempt from mutual checking: neighbouring pieces meet at
their shared joint by construction, and that contact is not an overlap.  The one thing
that exemption cannot judge is bodies extending *past* the joint (the level crossing's
road plate overhangs its connectors by 16 mm) -- the disc model cannot tell a legal
plate-over-plain-track join from an illegal plate-over-plate one.  That constraint is
therefore enforced at link level instead: pieces declare an ``end_overhang`` and two
overhanging ends refuse to mate (see ``PieceType.end_overhang`` and ``Layout.join``).
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field

__all__ = ["CollisionField", "TOUCH_MARGIN", "DEFAULT_CLEARANCE", "UNDERPASS_MIN"]

#: Two tracks may come this close (mm) before it counts as an overlap.  Set just under
#: the 64 mm piece width so flush parallel tracks are allowed.
TOUCH_MARGIN = 2.0

#: Vertical separation (mm) at which one track clears another regardless of piece
#: type.  No in-system elevation reaches it; solid pieces (ramps) therefore never
#: admit track beneath them.
DEFAULT_CLEARANCE = 120.0

#: An ``underpass`` piece (the bridge arch, and the ramps near their high ends)
#: admits track beneath any deck point standing at least this much higher.  Set
#: from the user's observations on the real 10872 bridge: a train passes under
#: the mid-arch, and grazing the ramp's highest portion is fine too.  The value
#: allows for the pairwise disc model: a crossing interacts with deck points up
#: to ~60 mm to the side, which on the 18% ramp sit 10.8 mm lower than the point
#: directly overhead -- 42 here means "about 53 mm of deck straight above".
#: With the provisional profile (ramp 0->57.6, span 57.6->76.8 mm) crossings
#: clear the full spans plus roughly the last 30 mm of each ramp, and the lower
#: ramp stays solid.  Refine when the real bridge is measured.
UNDERPASS_MIN = 42.0


@dataclass(slots=True)
class _CellCloud:
    """One placement's sample points that fall in a single grid cell."""

    placement: int
    half_width: float
    points: list[tuple[float, float, float]]
    underpass: bool


@dataclass(slots=True)
class _Cloud:
    """Bookkeeping for one placement, including the cells it occupies."""

    placement: int
    half_width: float
    cells: tuple[tuple[int, int], ...]
    underpass: bool = False
    previous_max_half_width: float = 0.0


@dataclass
class CollisionField:
    """Incremental collision checker over a growing set of placements.

    Supports ``add`` / ``pop`` in LIFO order, matching depth-first search.  Points are
    binned into a coarse grid; each query scans a neighbourhood wide enough for the
    largest interaction radius actually stored, so wide pieces (the 160 mm level
    crossing) are detected just as reliably as plain 64 mm track.
    """

    clearance: float = DEFAULT_CLEARANCE
    cell: float = 96.0
    _clouds: list[_Cloud] = field(default_factory=list)
    _grid: dict[tuple[int, int], list[_CellCloud]] = field(default_factory=dict)
    _max_half_width: float = 0.0

    def clashes(
        self,
        points: list[tuple[float, float, float]],
        half_width: float,
        ignore: set[int],
        underpass: bool = False,
    ) -> bool:
        """Would a piece with these sample points overlap anything already placed?

        *ignore* lists placement indices exempt from the check (the piece's direct
        neighbours in the layout graph); *underpass* marks the querying piece as an
        open arch that admits track beneath its deck.  This is the solver's hottest
        non-arithmetic loop, hence the inlined cell scan.
        """
        if not self._grid:
            return False
        cell = self.cell
        clearance = self.clearance
        grid = self._grid
        reach = half_width + self._max_half_width - TOUCH_MARGIN
        r = max(1, math.ceil(reach / cell))
        neighbourhoods: dict[tuple[int, int], tuple[list[_CellCloud], ...]] = {}
        for x, y, z in points:
            cx = int(x // cell)
            cy = int(y // cell)
            key = (cx, cy)
            buckets = neighbourhoods.get(key)
            if buckets is None:
                buckets = tuple(
                    bucket
                    for gx in range(cx - r, cx + r + 1)
                    for gy in range(cy - r, cy + r + 1)
                    if (bucket := grid.get((gx, gy)))
                )
                neighbourhoods[key] = buckets
            for bucket in buckets:
                for cloud in bucket:
                    if cloud.placement in ignore:
                        continue
                    limit = half_width + cloud.half_width - TOUCH_MARGIN
                    limit2 = limit * limit
                    stored_underpass = cloud.underpass
                    for px, py, pz in cloud.points:
                        dz = z - pz
                        if dz >= clearance or dz <= -clearance:
                            continue
                        if stored_underpass and dz <= -UNDERPASS_MIN:
                            continue  # running under the stored piece's open arch
                        if underpass and dz >= UNDERPASS_MIN:
                            continue  # the stored track runs under this open arch
                        dx = x - px
                        dy = y - py
                        if dx * dx + dy * dy < limit2:
                            return True
        return False

    def add(
        self,
        placement: int,
        points: list[tuple[float, float, float]],
        half_width: float,
        underpass: bool = False,
    ) -> None:
        cell = self.cell
        grouped: dict[tuple[int, int], list[tuple[float, float, float]]] = {}
        for point in points:
            x, y, _z = point
            key = (int(x // cell), int(y // cell))
            grouped.setdefault(key, []).append(point)
        cloud = _Cloud(
            placement, half_width, tuple(grouped), underpass, self._max_half_width
        )
        self._clouds.append(cloud)
        self._max_half_width = max(self._max_half_width, half_width)
        grid = self._grid
        for key, cell_points in grouped.items():
            grid.setdefault(key, []).append(
                _CellCloud(placement, half_width, cell_points, underpass)
            )

    def pop(self) -> None:
        """Remove the most recently added placement (backtracking)."""
        cloud = self._clouds.pop()
        # Each placement contributes one grouped suffix per occupied cell. LIFO
        # backtracking therefore removes one cell-cloud at a time, independent of
        # how many centreline samples happened to land in that cell.
        self._max_half_width = cloud.previous_max_half_width
        grid = self._grid
        for key in cloud.cells:
            bucket = grid[key]
            if bucket[-1].placement != cloud.placement:
                raise RuntimeError("collision field must be popped in LIFO order")
            bucket.pop()
            if not bucket:
                del grid[key]

    def __len__(self) -> int:
        return len(self._clouds)
