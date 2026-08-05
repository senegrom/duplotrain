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

#: An ``underpass`` piece (the open bridge arch) admits track beneath any deck point
#: standing at least this much higher.  With the provisional bridge profile (span
#: deck 57.6->76.8 mm) this opens roughly +/-90 mm of run around the mid-bridge
#: crest for a crossing at 30 degrees or steeper -- and excludes the ramps (<=57.6)
#: and the spans' low halves.  Refine when the real bridge is measured.
UNDERPASS_MIN = 64.0


@dataclass
class _Cloud:
    """The sample points of one placement, flattened for fast scanning."""

    placement: int
    half_width: float
    points: list[tuple[float, float, float]]
    underpass: bool = False


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
        for x, y, z in points:
            cx = int(x // cell)
            cy = int(y // cell)
            for gx in range(cx - r, cx + r + 1):
                for gy in range(cy - r, cy + r + 1):
                    bucket = grid.get((gx, gy))
                    if not bucket:
                        continue
                    for px, py, pz, phw, pidx, pu in bucket:
                        if pidx in ignore:
                            continue
                        dz = z - pz
                        if dz >= clearance or dz <= -clearance:
                            continue
                        if pu and dz <= -UNDERPASS_MIN:
                            continue  # running under the stored piece's open arch
                        if underpass and dz >= UNDERPASS_MIN:
                            continue  # the stored track runs under this open arch
                        limit = half_width + phw - TOUCH_MARGIN
                        dx = x - px
                        dy = y - py
                        if dx * dx + dy * dy < limit * limit:
                            return True
        return False

    def add(
        self,
        placement: int,
        points: list[tuple[float, float, float]],
        half_width: float,
        underpass: bool = False,
    ) -> None:
        cloud = _Cloud(placement, half_width, points, underpass)
        self._clouds.append(cloud)
        self._max_half_width = max(self._max_half_width, half_width)
        cell = self.cell
        for x, y, z in points:
            key = (int(x // cell), int(y // cell))
            self._grid.setdefault(key, []).append(
                (x, y, z, half_width, placement, underpass)
            )

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
