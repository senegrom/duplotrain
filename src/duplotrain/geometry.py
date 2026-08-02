"""Poses and rigid motions on the DUPLO track lattice.

A *pose* is where a piece end sits and which way it faces: ``(x, y, z, heading)``.
Positions are exact :class:`~duplotrain.exact.Alg` values; the heading is an integer
index into a 24-step lattice, so one step is 15 degrees and a DUPLO curve is exactly
two steps.

Keeping the heading as an integer -- rather than a float angle -- is what makes loop
closure decidable.  Two poses face the same way when their heading indices are equal
mod 24, with no "is 359.9999 close enough to 0" question to answer.

The z axis is carried through for ramp and bridge pieces.  It never rotates (track only
ever tilts about its own axis of travel, and the rise of a ramp is fixed), so elevation
is a plain additive term.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction

from .exact import Alg, AlgLike, alg

__all__ = [
    "HEADING_STEPS",
    "DEGREES_PER_STEP",
    "steps_to_degrees",
    "degrees_to_steps",
    "cos_sin",
    "Pose",
    "ORIGIN",
]

#: Number of distinct headings on the lattice.  24 steps of 15 degrees covers every
#: angle DUPLO track uses (30-degree curves, 90-degree crossings) with room for 45- and
#: 15-degree pieces, and all of them stay exact in ``Q(sqrt2, sqrt3)``.
HEADING_STEPS = 24

#: Degrees turned by one heading step.
DEGREES_PER_STEP = 360 // HEADING_STEPS  # 15

# cos/sin for 0, 15, 30, 45, 60, 75 degrees, exactly.
_QUARTER: tuple[tuple[Alg, Alg], ...] = (
    (Alg(1), Alg(0)),                                                    # 0
    (Alg(0, Fraction(1, 4), 0, Fraction(1, 4)),                          # 15  (sqrt6+sqrt2)/4
     Alg(0, Fraction(-1, 4), 0, Fraction(1, 4))),                        #     (sqrt6-sqrt2)/4
    (Alg(0, 0, Fraction(1, 2), 0), Alg(Fraction(1, 2))),                 # 30
    (Alg(0, Fraction(1, 2), 0, 0), Alg(0, Fraction(1, 2), 0, 0)),        # 45
    (Alg(Fraction(1, 2)), Alg(0, 0, Fraction(1, 2), 0)),                 # 60
    (Alg(0, Fraction(-1, 4), 0, Fraction(1, 4)),                         # 75
     Alg(0, Fraction(1, 4), 0, Fraction(1, 4))),
)


def _build_rotations() -> tuple[tuple[Alg, Alg], ...]:
    """Exact ``(cos, sin)`` for every heading on the lattice."""
    table: list[tuple[Alg, Alg]] = []
    for k in range(HEADING_STEPS):
        quadrant, rem = divmod(k, 6)
        c, s = _QUARTER[rem]
        for _ in range(quadrant):
            c, s = -s, c  # rotate the pair by a further 90 degrees
        table.append((c, s))
    return tuple(table)


_ROTATIONS = _build_rotations()


def steps_to_degrees(steps: int) -> int:
    """Convert a heading index to degrees."""
    return (steps % HEADING_STEPS) * DEGREES_PER_STEP


def degrees_to_steps(degrees: float) -> int:
    """Convert an angle in degrees to a heading index, rejecting off-lattice angles.

    Raises:
        ValueError: if *degrees* is not a whole multiple of :data:`DEGREES_PER_STEP`.
    """
    steps = degrees / DEGREES_PER_STEP
    nearest = round(steps)
    if abs(steps - nearest) > 1e-9:
        raise ValueError(
            f"{degrees} deg is not a multiple of {DEGREES_PER_STEP} deg, so it does not "
            f"lie on the {HEADING_STEPS}-step heading lattice"
        )
    return nearest % HEADING_STEPS


def cos_sin(steps: int) -> tuple[Alg, Alg]:
    """Exact cosine and sine of a lattice heading."""
    return _ROTATIONS[steps % HEADING_STEPS]


@dataclass(frozen=True, slots=True)
class Pose:
    """A position and facing on the track lattice.

    ``heading`` is the direction of travel *out of* this point, as a lattice index.
    """

    x: Alg
    y: Alg
    z: Alg
    heading: int

    def __post_init__(self) -> None:
        # Normalise so that equal poses compare equal and hash alike.
        object.__setattr__(self, "x", alg(self.x))
        object.__setattr__(self, "y", alg(self.y))
        object.__setattr__(self, "z", alg(self.z))
        object.__setattr__(self, "heading", self.heading % HEADING_STEPS)

    @staticmethod
    def make(
        x: AlgLike = 0, y: AlgLike = 0, z: AlgLike = 0, heading: int = 0
    ) -> Pose:
        """Build a pose from loose numeric types."""
        return Pose(alg(x), alg(y), alg(z), heading)

    def then(self, dx: AlgLike, dy: AlgLike, dz: AlgLike, dheading: int) -> Pose:
        """Apply a displacement expressed in this pose's own frame.

        This is SE(2) composition with an elevation term: the offset ``(dx, dy)`` is
        rotated into world space by the current heading, ``dz`` is added directly, and
        the headings compose additively on the lattice.
        """
        c, s = cos_sin(self.heading)
        dx_a, dy_a = alg(dx), alg(dy)
        return Pose(
            self.x + c * dx_a - s * dy_a,
            self.y + s * dx_a + c * dy_a,
            self.z + alg(dz),
            self.heading + dheading,
        )

    def reversed(self) -> Pose:
        """The same point, facing the opposite way."""
        return Pose(self.x, self.y, self.z, self.heading + HEADING_STEPS // 2)

    def translated(self, dx: AlgLike, dy: AlgLike, dz: AlgLike = 0) -> Pose:
        """Translate in *world* axes, leaving the heading alone."""
        return Pose(self.x + alg(dx), self.y + alg(dy), self.z + alg(dz), self.heading)

    def rotated_about_origin(self, steps: int) -> Pose:
        """Rotate the whole pose about the world origin."""
        c, s = cos_sin(steps)
        return Pose(
            c * self.x - s * self.y,
            s * self.x + c * self.y,
            self.z,
            self.heading + steps,
        )

    def mirrored(self) -> Pose:
        """Reflect across the world x axis (y -> -y), which flips handedness."""
        return Pose(self.x, -self.y, self.z, -self.heading)

    @property
    def degrees(self) -> int:
        """Heading in degrees."""
        return steps_to_degrees(self.heading)

    def xy(self) -> tuple[float, float]:
        """Floating-point position, for rendering and distance maths."""
        return (float(self.x), float(self.y))

    def xyz(self) -> tuple[float, float, float]:
        return (float(self.x), float(self.y), float(self.z))

    def distance_to(self, other: Pose) -> float:
        """Planar distance to another pose, in catalogue units (mm)."""
        return math.hypot(float(other.x - self.x), float(other.y - self.y))

    def same_point(self, other: Pose) -> bool:
        """Exact positional coincidence, ignoring heading and elevation."""
        return self.x == other.x and self.y == other.y

    def connects_to(self, other: Pose) -> bool:
        """True when a piece leaving *self* would butt exactly against *other*.

        Two track ends mate when they sit at the same point at the same height and face
        *opposite* ways -- one end's outward direction is the other's inward direction.
        """
        return (
            self.x == other.x
            and self.y == other.y
            and self.z == other.z
            and (self.heading - other.heading) % HEADING_STEPS == HEADING_STEPS // 2
        )

    def __repr__(self) -> str:
        z = f", z={float(self.z):.4g}" if self.z else ""
        return f"Pose({float(self.x):.4g}, {float(self.y):.4g}{z}, {self.degrees}deg)"


#: The canonical starting pose: origin, ground level, facing along +x.
ORIGIN = Pose.make(0, 0, 0, 0)
