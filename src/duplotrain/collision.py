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

_Point = tuple[float, float, float]
_Cell = tuple[int, int]
_GroupedPoints = tuple[tuple[_Cell, list[_Point]], ...]
#: (xmin, xmax, ymin, ymax, zmin, zmax) of one placement's samples.
_Bounds = tuple[float, float, float, float, float, float]


def bounds_of(points: list[_Point], offset: _Point | None = None) -> _Bounds:
    """Axis-aligned bounds of *points*, translated by *offset* if given."""
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    zs = [p[2] for p in points]
    ox, oy, oz = offset if offset is not None else (0.0, 0.0, 0.0)
    # Translating every point by the same offset translates the extremes exactly.
    return (ox + min(xs), ox + max(xs), oy + min(ys), oy + max(ys), oz + min(zs), oz + max(zs))


@dataclass(slots=True)
class _CellCloud:
    """One placement's sample points that fall in a single grid cell."""

    placement: int
    half_width: float
    points: list[_Point]
    underpass: bool


@dataclass(slots=True)
class _Cloud:
    """Bookkeeping for one placement, including the cells it occupies."""

    placement: int
    half_width: float
    cells: tuple[_Cell, ...]
    underpass: bool = False
    previous_max_half_width: float = 0.0
    bounds: _Bounds | None = None
    #: ``(local points, offset)`` of a placement not yet binned into the grid. A
    #: piece is only binned once a query's bounds come within reach of it.
    deferred: tuple[list[_Point], _Point] | None = None


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
    _grid: dict[_Cell, list[_CellCloud]] = field(default_factory=dict)
    _max_half_width: float = 0.0

    def _prepare(
        self,
        points: list[_Point],
        *,
        offset: _Point | None = None,
    ) -> _GroupedPoints:
        """Group candidate samples by grid cell, optionally translating them once."""
        cell = self.cell
        grouped: dict[_Cell, list[_Point]] = {}
        last_key: _Cell | None = None
        last_points: list[_Point] = []
        if offset is None:
            for point in points:
                x, y, _z = point
                key = (int(x // cell), int(y // cell))
                if key == last_key:
                    last_points.append(point)
                    continue
                cell_points = grouped.get(key)
                if cell_points is None:
                    cell_points = []
                    grouped[key] = cell_points
                cell_points.append(point)
                last_key = key
                last_points = cell_points
        else:
            ox, oy, oz = offset
            for x, y, z in points:
                point = (ox + x, oy + y, oz + z)
                key = (int(point[0] // cell), int(point[1] // cell))
                if key == last_key:
                    last_points.append(point)
                    continue
                cell_points = grouped.get(key)
                if cell_points is None:
                    cell_points = []
                    grouped[key] = cell_points
                cell_points.append(point)
                last_key = key
                last_points = cell_points
        return tuple(grouped.items())

    def _clashes_prepared(
        self,
        grouped: _GroupedPoints,
        half_width: float,
        ignore: set[int],
        underpass: bool = False,
    ) -> bool:
        """Check samples already grouped by query cell against stored placements."""
        if not self._grid:
            return False
        cell = self.cell
        clearance = self.clearance
        grid = self._grid
        reach = half_width + self._max_half_width - TOUCH_MARGIN
        r = max(1, math.ceil(reach / cell))
        for (cx, cy), cell_points in grouped:
            for gx in range(cx - r, cx + r + 1):
                for gy in range(cy - r, cy + r + 1):
                    bucket = grid.get((gx, gy))
                    if not bucket:
                        continue
                    for cloud in bucket:
                        if cloud.placement in ignore:
                            continue
                        limit = half_width + cloud.half_width - TOUCH_MARGIN
                        limit2 = limit * limit
                        stored_underpass = cloud.underpass
                        for x, y, z in cell_points:
                            for px, py, pz in cloud.points:
                                dz = z - pz
                                if dz >= clearance or dz <= -clearance:
                                    continue
                                if stored_underpass and dz <= -UNDERPASS_MIN:
                                    continue
                                if underpass and dz >= UNDERPASS_MIN:
                                    continue
                                dx = x - px
                                dy = y - py
                                if dx * dx + dy * dy < limit2:
                                    return True
        return False

    def clashes(
        self,
        points: list[_Point],
        half_width: float,
        ignore: set[int],
        underpass: bool = False,
    ) -> bool:
        """Would a piece with these sample points overlap anything already placed?"""
        return self._clashes_prepared(
            self._prepare(points), half_width, ignore, underpass=underpass
        )

    def _add_prepared(
        self,
        placement: int,
        grouped: _GroupedPoints,
        half_width: float,
        underpass: bool = False,
        bounds: _Bounds | None = None,
    ) -> None:
        """Insert samples already grouped by grid cell."""
        if bounds is None:
            bounds = bounds_of([p for _key, pts in grouped for p in pts])
        cloud = _Cloud(
            placement,
            half_width,
            tuple(key for key, _points in grouped),
            underpass,
            self._max_half_width,
            bounds,
        )
        self._clouds.append(cloud)
        self._max_half_width = max(self._max_half_width, half_width)
        grid = self._grid
        for key, cell_points in grouped:
            grid.setdefault(key, []).append(
                _CellCloud(placement, half_width, cell_points, underpass)
            )

    def add_deferred(
        self,
        placement: int,
        points: list[_Point],
        offset: _Point,
        half_width: float,
        bounds: _Bounds,
        underpass: bool = False,
    ) -> None:
        """Record a placement whose samples are binned only when a query needs them.

        *bounds* must enclose ``points`` translated by *offset*. Until some query's
        bounds come within reach, the placement costs no translation or binning.
        """
        self._clouds.append(_Cloud(
            placement, half_width, (), underpass, self._max_half_width, bounds,
            (points, offset),
        ))
        self._max_half_width = max(self._max_half_width, half_width)

    def _bin_deferred(self, cloud: _Cloud) -> None:
        points, offset = cloud.deferred  # type: ignore[misc]
        grouped = self._prepare(points, offset=offset)
        cloud.cells = tuple(key for key, _points in grouped)
        cloud.deferred = None
        grid = self._grid
        for key, cell_points in grouped:
            grid.setdefault(key, []).append(
                _CellCloud(cloud.placement, cloud.half_width, cell_points, cloud.underpass)
            )

    def near(self, bounds: _Bounds, half_width: float, ignore: set[int]) -> bool:
        """Could samples inside *bounds* overlap any placement not in *ignore*?

        False proves no sample pair can come within the interaction limit: the
        boxes are at least that far apart in x or in y, or their heights differ
        by the blanket clearance everywhere. True bins every deferred placement
        within reach, so a following point test sees all of them in the grid.
        """
        xmin, xmax, ymin, ymax, zmin, zmax = bounds
        clearance = self.clearance
        near = False
        for cloud in self._clouds:
            if cloud.placement in ignore:
                continue
            b = cloud.bounds
            limit = half_width + cloud.half_width - TOUCH_MARGIN
            if (
                xmin - b[1] >= limit
                or b[0] - xmax >= limit
                or ymin - b[3] >= limit
                or b[2] - ymax >= limit
                or zmin - b[5] >= clearance
                or b[4] - zmax >= clearance
            ):
                continue
            if cloud.deferred is not None:
                self._bin_deferred(cloud)
            near = True
        return near

    def add(
        self,
        placement: int,
        points: list[_Point],
        half_width: float,
        underpass: bool = False,
    ) -> None:
        self._add_prepared(
            placement, self._prepare(points), half_width, underpass=underpass
        )

    def pop(self) -> None:
        """Remove the most recently added placement (backtracking)."""
        cloud = self._clouds.pop()
        # Each placement contributes one cell-cloud per occupied cell. A deferred
        # placement binned late may sit below a newer one in a shared bucket, so
        # remove by placement rather than assuming it is last.
        self._max_half_width = cloud.previous_max_half_width
        if cloud.deferred is not None:
            return
        grid = self._grid
        placement = cloud.placement
        for key in cloud.cells:
            bucket = grid[key]
            if bucket[-1].placement == placement:
                bucket.pop()
            else:
                bucket[:] = [c for c in bucket if c.placement != placement]
            if not bucket:
                del grid[key]

    def __len__(self) -> int:
        return len(self._clouds)
