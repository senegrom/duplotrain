"""Overlap detection between placed pieces.

Each placement contributes the sampled centrelines of its paths; two placements clash
when any two of their sample points come closer than the sum of their half-widths
(minus a small margin so that exactly-touching parallel tracks stay legal -- sidings
laid side by side are a feature, not a collision).

Height is respected two ways.  Points whose elevations differ by at least
``clearance`` pass over each other freely -- a blanket rule no current piece can
reach. Separately, pieces flagged ``underpass`` let track run beneath wherever their
deck stands at least ``UNDERPASS_MIN`` higher. The current catalogue flags both spans and ramps:
the spans and the highest portions of the ramps can clear track, while the lower
ramp sections stay solid. These thresholds are provisional.

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
#: type. No in-system elevation reaches it; lower clearances require the
#: ``underpass`` flag and the height-specific rule below.
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
# This broad-phase index contains sample BOUNDS, not samples. Keep it independent
# of the narrow-phase cell size, and cap both insertion and query work for custom
# long/diagonal pieces. Small fields and oversized queries retain the linear path.
_BOUNDS_CELL = 256.0
_BOUNDS_MAX_CELLS = 64
_BOUNDS_INDEX_MIN = 128
# Above this radius, scan occupied cells rather than a quadratic empty square.
_NARROW_MAX_RADIUS = 16


def _bound_cells(bounds: tuple[float, ...], padding: float = 0.0) -> tuple[_Cell, ...] | None:
    """Cells touching a padded planar box, or None for the bounded linear fallback."""
    edges = (bounds[0] - padding, bounds[1] + padding,
             bounds[2] - padding, bounds[3] + padding)
    if not all(math.isfinite(edge) for edge in edges):
        return None
    if padding > 0:
        # Outward rounding must not lose a borderline cloud through subtraction
        # rounding at a cell boundary; near() still applies the original predicate.
        edges = tuple(math.nextafter(edge, -math.inf if i % 2 == 0 else math.inf)
                      for i, edge in enumerate(edges))
        if not all(math.isfinite(edge) for edge in edges):
            return None
    xmin, xmax, ymin, ymax = (int(edge // _BOUNDS_CELL) for edge in edges)
    if (xmax - xmin + 1) * (ymax - ymin + 1) > _BOUNDS_MAX_CELLS:
        return None
    return tuple((x, y) for x in range(xmin, xmax + 1) for y in range(ymin, ymax + 1))


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
    #: (xmin, xmax, ymin, ymax) of ``points``: a query cell whose own box lies
    #: at least the interaction limit away in x or in y holds no clashing pair.
    box: tuple[float, float, float, float] = (0.0, 0.0, 0.0, 0.0)


def _cell_cloud(placement: int, half_width: float, points: list, underpass: bool) -> _CellCloud:
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    return _CellCloud(placement, half_width, points, underpass,
                      (min(xs), max(xs), min(ys), max(ys)))


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
    #: None means either not yet indexed, or deliberately outside the bounded grid.
    bound_cells: tuple[_Cell, ...] | None = None


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
    _bounds_grid: dict[_Cell, list[_Cloud]] | None = None
    _wide_clouds: list[_Cloud] = field(default_factory=list)

    def _index_bounds(self, cloud: _Cloud) -> None:
        """Register a cloud when the optional broad-phase index is active."""
        if self._bounds_grid is None:
            return
        keys = _bound_cells(cloud.bounds)
        cloud.bound_cells = keys
        if keys is None:
            self._wide_clouds.append(cloud)
        else:
            for key in keys:
                self._bounds_grid.setdefault(key, []).append(cloud)

    def _near_clouds(self, bounds: _Bounds, half_width: float) -> list[_Cloud] | tuple[_Cloud, ...]:
        """Return a conservative local superset; exact bounds are still checked below.

        Stored boxes are unpadded. Expand the query by the largest possible pair
        radius, then check each surviving cloud with its OWN radius in ``near``.
        The index is lazy: final audits call ``clashes`` directly and never pay
        to build it. Deferred clouds participate before their samples are binned.
        """
        if len(self._clouds) < _BOUNDS_INDEX_MIN:
            return self._clouds
        reach = max(0.0, half_width + self._max_half_width - TOUCH_MARGIN)
        keys = _bound_cells(bounds, reach)
        if keys is None or len(keys) * 4 > len(self._clouds):
            return self._clouds
        if self._bounds_grid is None:
            self._bounds_grid = {}
            for cloud in self._clouds:
                self._index_bounds(cloud)
        # A box may occupy several cells. Deduplicate CLOUDS, not placement IDs:
        # callers are permitted to add multiple clouds for the same placement.
        found = {}
        for key in keys:
            for cloud in self._bounds_grid.get(key, ()):
                found[id(cloud)] = cloud
        return (*self._wide_clouds, *found.values())

    def nearby_placements(self, bounds: _Bounds, half_width: float) -> list[int]:
        """Sorted, distinct IDs conservatively shortlisted by the bounds index.

        This is not an overlap verdict: callers must still check each pair with
        ``near`` and ``clashes``, applying their own neighbour exemptions. Small
        fields and oversized queries return all IDs. Deferred samples stay deferred.
        """
        return sorted({cloud.placement for cloud in self._near_clouds(bounds, half_width)})

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
        radius = reach / cell
        r = max(1, math.ceil(radius)) if math.isfinite(radius) else None
        for (cx, cy), cell_points in grouped:
            # The box of this cell's samples: a stored cloud whose box lies at
            # least the pair's limit away in x or in y cannot come within it.
            qx0 = qx1 = cell_points[0][0]
            qy0 = qy1 = cell_points[0][1]
            for x, y, _z in cell_points:
                if x < qx0:
                    qx0 = x
                elif x > qx1:
                    qx1 = x
                if y < qy0:
                    qy0 = y
                elif y > qy1:
                    qy1 = y
            if r is None:
                buckets = grid.values()
            elif r > _NARROW_MAX_RADIUS:
                buckets = (bucket for (gx, gy), bucket in grid.items()
                           if abs(gx - cx) <= r and abs(gy - cy) <= r)
            else:
                buckets = (grid.get((gx, gy))
                           for gx in range(cx - r, cx + r + 1)
                           for gy in range(cy - r, cy + r + 1))
            for bucket in buckets:
                if not bucket:
                    continue
                for cloud in bucket:
                    if cloud.placement in ignore:
                        continue
                    limit = half_width + cloud.half_width - TOUCH_MARGIN
                    bx0, bx1, by0, by1 = cloud.box
                    if (bx0 - qx1 >= limit or qx0 - bx1 >= limit
                            or by0 - qy1 >= limit or qy0 - by1 >= limit):
                        continue
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
        self._index_bounds(cloud)
        self._max_half_width = max(self._max_half_width, half_width)
        grid = self._grid
        for key, cell_points in grouped:
            grid.setdefault(key, []).append(
                _cell_cloud(placement, half_width, cell_points, underpass)
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
        cloud = _Cloud(
            placement, half_width, (), underpass, self._max_half_width, bounds,
            (points, offset),
        )
        self._clouds.append(cloud)
        self._index_bounds(cloud)
        self._max_half_width = max(self._max_half_width, half_width)

    def _bin_deferred(self, cloud: _Cloud) -> None:
        points, offset = cloud.deferred  # type: ignore[misc]
        grouped = self._prepare(points, offset=offset)
        cloud.cells = tuple(key for key, _points in grouped)
        cloud.deferred = None
        grid = self._grid
        for key, cell_points in grouped:
            grid.setdefault(key, []).append(
                _cell_cloud(cloud.placement, cloud.half_width, cell_points, cloud.underpass)
            )

    def place(
        self,
        placement: int,
        points: list[_Point],
        offset: _Point,
        half_width: float,
        bounds: _Bounds,
        ignore: set[int],
        underpass: bool = False,
    ) -> bool:
        """Add a placement unless it clashes with one not in *ignore*.

        The samples are binned and tested only when some placement's bounds come
        within reach; a piece laid clear of everything is deferred as-is.
        """
        if not self.near(bounds, half_width, ignore):
            self.add_deferred(placement, points, offset, half_width, bounds, underpass=underpass)
            return True
        grouped = self._prepare(points, offset=offset)
        if self._clashes_prepared(grouped, half_width, ignore, underpass=underpass):
            return False
        self._add_prepared(placement, grouped, half_width, underpass=underpass, bounds=bounds)
        return True

    def near(self, bounds: _Bounds, half_width: float, ignore: set[int]) -> bool:
        """Could samples inside *bounds* overlap any placement not in *ignore*?

        Large fields query a bounded spatial index first; small fields scan directly.
        False proves no sample pair can come within the interaction limit: the
        boxes are at least that far apart in x or in y, or their heights differ
        by the blanket clearance everywhere. True bins every deferred placement
        within reach, so a following point test sees all of them in the grid.
        """
        xmin, xmax, ymin, ymax, zmin, zmax = bounds
        clearance = self.clearance
        near = False
        for cloud in self._near_clouds(bounds, half_width):
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
        # Unlike the sample grid, this index is always populated in push order.
        # Removing a deferred cloud must remove its bounds too, before returning.
        if self._bounds_grid is not None and cloud.bound_cells is None:
            self._wide_clouds.pop()
        elif self._bounds_grid is not None:
            for key in cloud.bound_cells:
                bucket = self._bounds_grid[key]
                bucket.pop()
                if not bucket:
                    del self._bounds_grid[key]
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
