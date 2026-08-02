"""Exact arithmetic for track geometry.

Track layouts live or die on one question: *does the loop close?*  Answering it in
floating point means picking a tolerance, and any tolerance is wrong somewhere -- too
tight and real loops are rejected, too loose and a layout that is 3 mm out gets called
closed.  Both failures are silent.

So we do the arithmetic exactly.

DUPLO curves turn 30 degrees, so every heading in a layout is a multiple of 30 degrees
and every position is an integer combination of ``sin``/``cos`` of such angles.  Those
values are not rational, but they all live in the number field ``Q(sqrt2, sqrt3)``::

    a + b*sqrt2 + c*sqrt3 + d*sqrt6        with a, b, c, d rational

That field is closed under the arithmetic we need, and it is big enough for *any* angle
that is a multiple of 15 degrees -- so 15, 22.5-free but 30, 45, 60, 90 all work.  That
leaves room for crossings at 45 or 90 degrees and any future piece on a 15-degree grid
without giving up exactness.

:class:`Alg` is the field element.  Equality is exact, so ``pose == HOME`` is a real
answer rather than a judgement call.
"""

from __future__ import annotations

import math
from fractions import Fraction
from typing import Union

__all__ = ["Alg", "ZERO", "ONE", "SQRT2", "SQRT3", "SQRT6", "alg", "AlgLike"]

# What can be coerced into an Alg.
AlgLike = Union["Alg", int, Fraction]


class Alg:
    """An exact element ``a + b*sqrt2 + c*sqrt3 + d*sqrt6`` of ``Q(sqrt2, sqrt3)``.

    The four coefficients are :class:`~fractions.Fraction`, so the representation is
    exact and canonical: two ``Alg`` values are equal if and only if they denote the
    same real number.  (Canonical because ``1, sqrt2, sqrt3, sqrt6`` are linearly
    independent over the rationals, so each real number in the field has exactly one
    coefficient tuple.)

    Instances are immutable and hashable, which lets layouts be deduplicated by exact
    position with an ordinary ``set``.
    """

    __slots__ = ("a", "b", "c", "d")

    def __init__(
        self,
        a: AlgLike = 0,
        b: Fraction | int = 0,
        c: Fraction | int = 0,
        d: Fraction | int = 0,
    ) -> None:
        if isinstance(a, Alg):
            if b or c or d:
                raise TypeError("cannot combine an Alg with extra radical coefficients")
            self.a, self.b, self.c, self.d = a.a, a.b, a.c, a.d
            return
        self.a = Fraction(a)
        self.b = Fraction(b)
        self.c = Fraction(c)
        self.d = Fraction(d)

    # -- construction ----------------------------------------------------------

    @staticmethod
    def coerce(value: AlgLike) -> Alg:
        """Return *value* as an :class:`Alg`, accepting ints and Fractions."""
        return value if isinstance(value, Alg) else Alg(value)

    # -- arithmetic ------------------------------------------------------------

    def __add__(self, other: AlgLike) -> Alg:
        o = Alg.coerce(other)
        return Alg(self.a + o.a, self.b + o.b, self.c + o.c, self.d + o.d)

    __radd__ = __add__

    def __neg__(self) -> Alg:
        return Alg(-self.a, -self.b, -self.c, -self.d)

    def __sub__(self, other: AlgLike) -> Alg:
        return self + (-Alg.coerce(other))

    def __rsub__(self, other: AlgLike) -> Alg:
        return Alg.coerce(other) + (-self)

    def __mul__(self, other: AlgLike) -> Alg:
        o = Alg.coerce(other)
        a1, b1, c1, d1 = self.a, self.b, self.c, self.d
        a2, b2, c2, d2 = o.a, o.b, o.c, o.d
        # Using sqrt2*sqrt3 = sqrt6, sqrt2*sqrt6 = 2*sqrt3, sqrt3*sqrt6 = 3*sqrt2,
        # sqrt2^2 = 2, sqrt3^2 = 3, sqrt6^2 = 6.
        return Alg(
            a1 * a2 + 2 * b1 * b2 + 3 * c1 * c2 + 6 * d1 * d2,
            a1 * b2 + b1 * a2 + 3 * c1 * d2 + 3 * d1 * c2,
            a1 * c2 + c1 * a2 + 2 * b1 * d2 + 2 * d1 * b2,
            a1 * d2 + d1 * a2 + b1 * c2 + c1 * b2,
        )

    __rmul__ = __mul__

    def conjugates(self) -> tuple[Alg, Alg, Alg]:
        """The three non-trivial Galois conjugates (flipping the sign of each radical)."""
        return (
            Alg(self.a, -self.b, self.c, -self.d),
            Alg(self.a, self.b, -self.c, -self.d),
            Alg(self.a, -self.b, -self.c, self.d),
        )

    def inverse(self) -> Alg:
        """Multiplicative inverse.

        Computed as ``conj_product / norm`` where the norm is the rational product of
        all four conjugates.
        """
        if not self:
            raise ZeroDivisionError("Alg inverse of zero")
        k1, k2, k3 = self.conjugates()
        numerator = k1 * k2 * k3
        norm = self * numerator
        if norm.b or norm.c or norm.d:  # pragma: no cover - guards a maths error
            raise ArithmeticError(f"norm of {self!r} was not rational: {norm!r}")
        return numerator * Alg(1 / norm.a)

    def __truediv__(self, other: AlgLike) -> Alg:
        o = Alg.coerce(other)
        # Dividing by a plain rational is the common case; skip the conjugate dance.
        if not (o.b or o.c or o.d):
            if not o.a:
                raise ZeroDivisionError("Alg division by zero")
            inv = 1 / o.a
            return Alg(self.a * inv, self.b * inv, self.c * inv, self.d * inv)
        return self * o.inverse()

    def __rtruediv__(self, other: AlgLike) -> Alg:
        return Alg.coerce(other) * self.inverse()

    # -- comparison ------------------------------------------------------------

    def __eq__(self, other: object) -> bool:
        if isinstance(other, (int, Fraction)):
            other = Alg(other)
        if not isinstance(other, Alg):
            return NotImplemented
        return (self.a, self.b, self.c, self.d) == (other.a, other.b, other.c, other.d)

    def __hash__(self) -> int:
        return hash((self.a, self.b, self.c, self.d))

    def __bool__(self) -> bool:
        return bool(self.a or self.b or self.c or self.d)

    def __lt__(self, other: AlgLike) -> bool:
        # Exact sign comparison would need interval refinement; float is fine for
        # ordering (used only for sorting and bounding boxes, never for equality).
        return float(self) < float(Alg.coerce(other))

    def __le__(self, other: AlgLike) -> bool:
        return self == other or self < other

    def __gt__(self, other: AlgLike) -> bool:
        return not self <= other

    def __ge__(self, other: AlgLike) -> bool:
        return not self < other

    # -- conversion ------------------------------------------------------------

    def __float__(self) -> float:
        return (
            float(self.a)
            + float(self.b) * math.sqrt(2.0)
            + float(self.c) * math.sqrt(3.0)
            + float(self.d) * math.sqrt(6.0)
        )

    def is_rational(self) -> bool:
        return not (self.b or self.c or self.d)

    def as_fraction(self) -> Fraction:
        """Return the value as a :class:`Fraction`, if it is rational."""
        if not self.is_rational():
            raise ValueError(f"{self!r} is not rational")
        return self.a

    def coeffs(self) -> tuple[Fraction, Fraction, Fraction, Fraction]:
        return (self.a, self.b, self.c, self.d)

    # -- display ---------------------------------------------------------------

    def __repr__(self) -> str:
        parts = []
        for coeff, symbol in (
            (self.a, ""),
            (self.b, "*sqrt2"),
            (self.c, "*sqrt3"),
            (self.d, "*sqrt6"),
        ):
            if coeff:
                parts.append(f"{coeff}{symbol}")
        return f"Alg({' + '.join(parts) if parts else '0'})"

    def __str__(self) -> str:
        return f"{float(self):.6g}"


def alg(value: AlgLike) -> Alg:
    """Shorthand for :meth:`Alg.coerce`."""
    return Alg.coerce(value)


ZERO = Alg(0)
ONE = Alg(1)
SQRT2 = Alg(0, 1, 0, 0)
SQRT3 = Alg(0, 0, 1, 0)
SQRT6 = Alg(0, 0, 0, 1)
