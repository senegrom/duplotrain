"""Integer fast path for the 30-degree track lattice.

Profiling puts ~85% of solve time inside :class:`~fractions.Fraction` churn under the
general ``Q(sqrt2, sqrt3)`` field.  But every piece in the real catalogue turns in
multiples of 30 degrees and measures in exact twentieths of a millimetre, so all
reachable positions live in the scaled cyclotomic ring

    (1/SCALE) * Z[zeta],    zeta = e^{i*pi/6},   SCALE = 20

A position is four integers ``(a, b, c, d)`` meaning ``a + b*zeta + c*zeta^2 +
d*zeta^3`` (a complex number = the xy-plane), plus one integer for elevation.
Rotating by 30 degrees is multiplication by zeta, which -- thanks to the minimal
polynomial ``zeta^4 = zeta^2 - 1`` -- is an *integer* shuffle:

    zeta * (a, b, c, d)  =  (-d, a, b + d, c)

so composing poses costs a handful of integer adds; no divisions, no GCDs, no
allocation-heavy Fractions.  Equality and hashing are tuple-of-int operations, which
is what makes exact closure tests cheap.

:func:`from_alg_xy` converts exact field coordinates into the ring (or reports that
they don't fit -- a user piece on the 15/45-degree grid, say), letting the solver
auto-select this fast engine and fall back to the general field otherwise.
"""

from __future__ import annotations

import math
from fractions import Fraction

from .exact import Alg

__all__ = [
    "SCALE",
    "LatticePoint",
    "LatticePose",
    "from_alg_xy",
    "z_from_alg",
    "ROT_COS_SIN",
]

#: Twentieths of a millimetre: covers the catalogue's fifths (bridge rises) and the
#: halves that 30-degree trigonometry introduces.
SCALE = 20

#: (cos, sin) per 30-degree step, as floats, for distance maths and rendering.
ROT_COS_SIN = tuple(
    (math.cos(math.radians(30 * k)), math.sin(math.radians(30 * k))) for k in range(12)
)

# Basis reals: zeta^0..zeta^3 = 1, (sqrt3+i)/2, (1+i*sqrt3)/2, i
_SQRT3 = math.sqrt(3.0)


class LatticePoint:
    """A point of ``(1/SCALE) * Z[zeta12]`` -- the xy-plane with exact 30-degree turns."""

    __slots__ = ("a", "b", "c", "d")

    def __init__(self, a: int, b: int, c: int, d: int) -> None:
        self.a = a
        self.b = b
        self.c = c
        self.d = d

    def rotated(self, steps: int) -> "LatticePoint":
        """Rotate by ``steps`` * 30 degrees (integer arithmetic only)."""
        a, b, c, d = self.a, self.b, self.c, self.d
        for _ in range(steps % 12):
            a, b, c, d = -d, a, b + d, c
        return LatticePoint(a, b, c, d)

    def __add__(self, other: "LatticePoint") -> "LatticePoint":
        return LatticePoint(
            self.a + other.a, self.b + other.b, self.c + other.c, self.d + other.d
        )

    def __sub__(self, other: "LatticePoint") -> "LatticePoint":
        return LatticePoint(
            self.a - other.a, self.b - other.b, self.c - other.c, self.d - other.d
        )

    def key(self) -> tuple[int, int, int, int]:
        return (self.a, self.b, self.c, self.d)

    def xy(self) -> tuple[float, float]:
        """Floating-point millimetres."""
        x = self.a + (self.b * _SQRT3 + self.c) / 2.0
        y = self.d + (self.c * _SQRT3 + self.b) / 2.0
        return (x / SCALE, y / SCALE)

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        x, y = self.xy()
        return f"LatticePoint({x:.3f}, {y:.3f})"


class LatticePose:
    """Pose on the fast lattice: xy in ``Z[zeta]``, integer z, heading in 30-degree steps.

    ``heading`` uses 12 steps per revolution (unlike :class:`~duplotrain.geometry.Pose`
    which uses 24 steps of 15 degrees); the solver converts between the two at the
    boundary.  ``then(delta, dz, turn)`` mirrors ``Pose.then`` exactly.
    """

    __slots__ = ("p", "z", "heading")

    def __init__(self, p: LatticePoint, z: int, heading: int) -> None:
        self.p = p
        self.z = z
        self.heading = heading % 12

    def then(self, delta: LatticePoint, dz: int, turn: int) -> "LatticePose":
        return LatticePose(
            self.p + delta.rotated(self.heading), self.z + dz, self.heading + turn
        )

    def key(self) -> tuple:
        return (*self.p.key(), self.z, self.heading)

    def position_key(self) -> tuple:
        return (*self.p.key(), self.z)

    def distance_to(self, other: "LatticePose") -> float:
        ax, ay = self.p.xy()
        bx, by = other.p.xy()
        return math.hypot(ax - bx, ay - by)

    def connects_to(self, other: "LatticePose") -> bool:
        """Same point and height, opposite headings -- the exact mating test."""
        return (
            self.p.key() == other.p.key()
            and self.z == other.z
            and (self.heading - other.heading) % 12 == 6
        )

    def xyz(self) -> tuple[float, float, float]:
        x, y = self.p.xy()
        return (x, y, self.z / SCALE)

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        x, y = self.p.xy()
        return f"LatticePose({x:.3f}, {y:.3f}, z={self.z / SCALE:.3f}, {self.heading * 30}deg)"


ORIGIN_POSE = LatticePose(LatticePoint(0, 0, 0, 0), 0, 0)


def _scaled_int(value: Fraction) -> int | None:
    scaled = value * SCALE
    if scaled.denominator != 1:
        return None
    return int(scaled)


def from_alg_xy(x: Alg, y: Alg) -> LatticePoint | None:
    """Express exact field coordinates as a lattice point, or None if off-lattice.

    From ``Re = a + c/2 + (b/2)*sqrt3`` and ``Im = b/2 + d + (c/2)*sqrt3``, with
    ``x = xa + xc*sqrt3`` and ``y = ya + yc*sqrt3`` (all pre-scaled by SCALE):

        b = 2*xc,  c = 2*yc,  a = xa - yc,  d = ya - xc

    Any sqrt2/sqrt6 component, or a coefficient not landing on 1/SCALE, disqualifies.
    """
    if x.b or x.d or y.b or y.d:  # sqrt2 / sqrt6 terms: 45-degree territory
        return None
    xa = _scaled_int(x.a)
    xc = _scaled_int(x.c)
    ya = _scaled_int(y.a)
    yc = _scaled_int(y.c)
    if None in (xa, xc, ya, yc):
        return None
    return LatticePoint(xa - yc, 2 * xc, 2 * yc, ya - xc)


def z_from_alg(z: Alg) -> int | None:
    """Elevation as a scaled integer, or None if it doesn't fit."""
    if not z.is_rational():
        return None
    return _scaled_int(z.a)
