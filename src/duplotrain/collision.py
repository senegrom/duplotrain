"""Overlap detection between placed pieces.

Each placement contributes the sampled centrelines of its paths; two placements clash
when any two of their sample points come closer than the sum of their half-widths
(minus a small margin so that exactly-touching parallel tracks stay legal -- sidings
laid side by side are a feature, not a collision).

Height is respected: points whose elevations differ by at least ``clearance`` pass over
each other freely.  The default clearance is deliberately larger than the 10872 bridge
deck height, because a DUPLO train genuinely does not fit under that bridge -- if a
future piece (or a user's brick-stacked bridge) rises high enough, crossing under it
becomes legal automatically.

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

__all__ = ["CollisionField", "TOUCH_MARGIN", "DEFAULT_CLEARANCE"]

#: Two tracks may come this close (mm) before it counts as an overlap.  Set just under
#: the 64 mm piece width so flush parallel tracks are allowed.
TOUCH_MARGIN = 2.0

#: Vertical separation (mm) at which one track clears another.  A DUPLO locomotive is
#: taller than the 10872 bridge deck (~77 mm), so by default nothing passes under it.
DEFAULT_CLEARANCE = 120.0


@dataclass
class _Cloud:
    """The sample points of one placement, flattened for fast scanning."""

    placement: int
    half_width: float
    points: list[tuple[float, float, float]]


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
    _grid: dict[tuple[int, int], list[tuple[float, float, float, float, int]]] = field(
        default_factory=dict
    )
    _max_half_width: float = 0.0

    def clashes(
        self,
        points: list[tuple[float, float, float]],
        half_width: float,
        ignore: set[int],
    ) -> bool:
        """Would a piece with these sample points overlap anything already placed?

        *ignore* lists placement indices exempt from the check (the piece's direct
        neighbours in the layout graph).  This is the solver's hottest non-arithmetic
        loop, hence the inlined cell scan.
        """
        if not self._grid:
            return False
        cell = self.cell
        clearance = self.clearance
        grid = self._grid
        reach = half_width + self._max_half_width - TOUCH_MARGIN
        r = max(1, math.ceil(reach / cell))
        for x, y, z in points:
            cx = int(x // cell)
            cy = int(y // cell)
            for gx in range(cx - r, cx + r + 1):
                for gy in range(cy - r, cy + r + 1):
                    bucket = grid.get((gx, gy))
                    if not bucket:
                        continue
                    for px, py, pz, phw, pidx in bucket:
                        if pidx in ignore:
                            continue
                        dz = z - pz
                        if dz >= clearance or dz <= -clearance:
                            continue
                        limit = half_width + phw - TOUCH_MARGIN
                        dx = x - px
                        dy = y - py
                        if dx * dx + dy * dy < limit * limit:
                            return True
        return False

    def add(
        self, placement: int, points: list[tuple[float, float, float]], half_width: float
    ) -> None:
        cloud = _Cloud(placement, half_width, points)
        self._clouds.append(cloud)
        self._max_half_width = max(self._max_half_width, half_width)
        cell = self.cell
        for x, y, z in points:
            key = (int(x // cell), int(y // cell))
            self._grid.setdefault(key, []).append((x, y, z, half_width, placement))

    def pop(self) -> None:
        """Remove the most recently added placement (backtracking)."""
        cloud = self._clouds.pop()
        if cloud.half_width >= self._max_half_width:
            self._max_half_width = max(
                (c.half_width for c in self._clouds), default=0.0
            )
        cell = self.cell
        for x, y, _z in cloud.points:
            key = (int(x // cell), int(y // cell))
            bucket = self._grid[key]
            for i in range(len(bucket) - 1, -1, -1):
                if bucket[i][4] == cloud.placement:
                    bucket.pop(i)
                    break
            if not bucket:
                del self._grid[key]

    def __len__(self) -> int:
        return len(self._clouds)
