"""How "nice" is a loop?

Closure is a hard constraint decided by the solver; this module ranks the survivors.
Niceness is taste, so the score is a weighted sum of transparent components and every
weight can be overridden.  The components:

``exactness``
    Exact closures beat forced fits; a forced fit loses points per millimetre of gap
    it asks the joints to absorb.

``usage``
    Fraction of the owned pieces actually on the floor.  A layout that leaves half the
    box in the box is less satisfying.

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
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Mapping

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
    # A 12-curve circle has track/perimeter ~0.79; treat that as full marks.
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
    )
