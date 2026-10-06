"""Integer fast path for the 30-degree track lattice.

Exact ``Q(sqrt2, sqrt3)`` arithmetic spends most of its time in
:class:`~fractions.Fraction` churn.  But every piece in the real catalogue turns in
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

from .exact import Alg

#: Twentieths of a millimetre: covers the catalogue's fifths (bridge rises) and the
#: halves that 30-degree trigonometry introduces.
SCALE = 20

#: (cos, sin) per 30-degree step, as floats, for distance maths and rendering.
ROT_COS_SIN = tuple(
    (math.cos(math.radians(30 * k)), math.sin(math.radians(30 * k))) for k in range(12)
)


class LatticePoint:
    """A point of ``(1/SCALE) * Z[zeta12]`` -- the xy-plane with exact 30-degree turns."""

    __slots__ = ("a", "b", "c", "d")

    def __init__(self, a: int, b: int, c: int, d: int) -> None:
        self.a = a
        self.b = b
        self.c = c
        self.d = d

    def rotated(self, steps: int) -> LatticePoint:
        """Rotate by ``steps`` * 30 degrees (integer arithmetic only)."""
        a, b, c, d = self.a, self.b, self.c, self.d
        for _ in range(steps % 12):
            a, b, c, d = -d, a, b + d, c
        return LatticePoint(a, b, c, d)

    def key(self) -> tuple[int, int, int, int]:
        return (self.a, self.b, self.c, self.d)


class LatticePose:
    """Pose on the fast lattice: xy in ``Z[zeta]``, integer z, heading in 30-degree steps.

    ``heading`` uses 12 steps per revolution (unlike :class:`~duplotrain.geometry.Pose`
    which uses 24 steps of 15 degrees); the solver converts between the two at the
    boundary and moves flat tuples of these values.
    """

    __slots__ = ("p", "z", "heading")

    def __init__(self, p: LatticePoint, z: int, heading: int) -> None:
        self.p = p
        self.z = z
        self.heading = heading % 12


def from_alg_xy(x: Alg, y: Alg) -> LatticePoint | None:
    """Express exact field coordinates as a lattice point, or None if off-lattice.

    From ``Re = a + c/2 + (b/2)*sqrt3`` and ``Im = b/2 + d + (c/2)*sqrt3``, with
    ``x = xa + xc*sqrt3`` and ``y = ya + yc*sqrt3`` (all pre-scaled by SCALE):

        b = 2*xc,  c = 2*yc,  a = xa - yc,  d = ya - xc

    The point is on the lattice exactly when all four are integers; the scaled
    coefficients themselves may be halves (``zeta/SCALE`` has ``xc = ya = 1/2``).
    Any sqrt2/sqrt6 component disqualifies.
    """
    if x.b or x.d or y.b or y.d:  # sqrt2 / sqrt6 terms: 45-degree territory
        return None
    xa, xc, ya, yc = (value * SCALE for value in (x.a, x.c, y.a, y.c))
    coords = (xa - yc, 2 * xc, 2 * yc, ya - xc)
    if any(value.denominator != 1 for value in coords):
        return None
    return LatticePoint(*map(int, coords))


def z_from_alg(z: Alg) -> int | None:
    """Elevation as a scaled integer, or None if it doesn't fit."""
    if not z.is_rational():
        return None
    scaled = z.a * SCALE
    return int(scaled) if scaled.denominator == 1 else None
