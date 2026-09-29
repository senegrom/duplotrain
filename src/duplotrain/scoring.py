"""How "nice" is a loop?

Closure is a hard constraint decided by the solver; this module ranks the survivors.
Niceness is taste, so the score is a weighted sum of transparent components and every
weight can be overridden.  The components:

``exactness``
    Exact closures beat forced fits; a forced fit loses points per millimetre of gap
    it asks the joints to absorb.

``usage``
    Fraction of the owned pieces the layout uses.  A layout that leaves half the box in
    the box is less satisfying.

``compactness``
    Track length relative to the bounding-box perimeter.  Long snaking layouts that
    wander off through the kitchen score lower than dense ones.

``squareness``
    Bounding-box aspect ratio.  1.0 for a square footprint, falling toward 0 for a
    bowling-alley strip -- living-room floors are roughly square.

``variety``
    Distinct piece types used.  A loop that works the switch and the bridge in is more
    fun than the plain ring.

``stub_penalty``
    Open switch branches dangling off the loop.  Mild by default: a stub is untidy but
    also a place to park the second train.

Apart from the score, ``raised`` counts the pieces that stand on stacks of DUPLO
bricks: those a brick or more above the layout's lowest track, save an arch resting
on a ramp that stands on the floor -- a bridge carries itself.  Raised track is
allowed, but a loop needing fewer stacks ranks first, whatever its score
(:attr:`ScoreBreakdown.rank`).
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from fractions import Fraction

from .exact import Alg
from .layout import Layout, _lowest
from .solver import Solution

__all__ = ["ScoreWeights", "ScoreBreakdown", "score_solution"]


@dataclass(frozen=True, slots=True)
class ScoreWeights:
    exactness: float = 40.0
    gap_penalty_per_mm: float = 8.0  # subtracted from exactness for forced fits
    usage: float = 25.0
    compactness: float = 15.0
    squareness: float = 10.0
    variety: float = 10.0
    stub_penalty: float = 3.0  # per dangling branch


@dataclass(frozen=True, slots=True)
class ScoreBreakdown:
    exactness: float
    usage: float
    compactness: float
    squareness: float
    variety: float
    stub_penalty: float
    raised: int  # pieces standing on bricks; not part of the total

    @property
    def total(self) -> float:
        return (
            self.exactness
            + self.usage
            + self.compactness
            + self.squareness
            + self.variety
            - self.stub_penalty
        )

    @property
    def rank(self) -> tuple[int, float]:
        """Sort key, best first: fewer pieces on bricks, then the higher total."""
        return (self.raised, -self.total)


#: One DUPLO brick: track lower than this above the floor needs nothing under it.
_BRICK = Alg(Fraction(96, 5))


def _raised_pieces(layout: Layout) -> int:
    """How many of *layout*'s pieces stand on stacks of DUPLO bricks (see above)."""
    lows = [_lowest(placement.port_pose(port).z for port in range(len(placement.piece.ports)))
            for placement in layout]
    floor = layout.floor()

    def carried(index: int) -> bool:
        # An arch whose foot rests on the top of a ramp standing on the floor.
        for port, spec in enumerate(layout.placements[index].piece.ports):
            mate = layout.links.get((index, port)) if spec.kind == "arch_foot" else None
            if (mate is not None and lows[mate[0]] == floor
                    and layout.placements[mate[0]].piece.ports[mate[1]].kind == "ramp_top"):
                return True
        return False

    return sum((low - floor - _BRICK).sign() >= 0 and not carried(index)
               for index, low in enumerate(lows))


def score_solution(
    solution: Solution,
    inventory: Mapping[str, int],
    weights: ScoreWeights | None = None,
) -> ScoreBreakdown:
    """Score one solver solution against the inventory it was drawn from."""
    w = weights or ScoreWeights()
    layout = solution.layout

    if solution.exact:
        exactness = w.exactness
    else:
        exactness = max(0.0, w.exactness - w.gap_penalty_per_mm * solution.gap)

    total_owned = sum(inventory.values()) or 1
    usage = w.usage * (len(layout) / total_owned)

    width, height = layout.size()
    perimeter = 2.0 * (width + height)
    # Track length over footprint perimeter, normalised by a circle's centreline
    # figure (pi/4). The footprint includes the track width, so a 12-curve circle
    # measures about 0.70 and gets about 0.89 of the full compactness weight.
    density = min(1.0, (layout.track_length() / perimeter) / 0.785) if perimeter else 0.0
    compactness = w.compactness * density

    long_side = max(width, height)
    squareness = w.squareness * ((min(width, height) / long_side) if long_side else 0.0)

    types_owned = sum(1 for n in inventory.values() if n > 0) or 1
    variety = w.variety * (len(layout.piece_counts) / types_owned)

    stub_penalty = w.stub_penalty * solution.open_stubs

    return ScoreBreakdown(
        exactness=exactness,
        usage=usage,
        compactness=compactness,
        squareness=squareness,
        variety=variety,
        stub_penalty=stub_penalty,
        raised=_raised_pieces(layout),
    )
