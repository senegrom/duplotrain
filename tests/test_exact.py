"""The exact number field: arithmetic, equality, conversion."""

import copy
import math
import pickle
from dataclasses import replace
from fractions import Fraction

import pytest

from duplotrain.exact import ONE, SQRT2, SQRT3, SQRT6, ZERO, Alg, _exact_fraction


def test_float_values():
    assert float(SQRT2) == pytest.approx(math.sqrt(2))
    assert float(SQRT3) == pytest.approx(math.sqrt(3))
    assert float(SQRT6) == pytest.approx(math.sqrt(6))


def test_radical_products_stay_in_field():
    assert SQRT2 * SQRT2 == 2
    assert SQRT3 * SQRT3 == 3
    assert SQRT6 * SQRT6 == 6
    assert SQRT2 * SQRT3 == SQRT6
    assert SQRT2 * SQRT6 == 2 * SQRT3
    assert SQRT3 * SQRT6 == 3 * SQRT2


def test_mixed_arithmetic():
    x = Alg(1, 2, 3, 4)  # 1 + 2*sqrt2 + 3*sqrt3 + 4*sqrt6
    y = Alg(Fraction(1, 2), -1, 0, 2)
    assert float(x + y) == pytest.approx(float(x) + float(y))
    assert float(x - y) == pytest.approx(float(x) - float(y))
    assert float(x * y) == pytest.approx(float(x) * float(y))
    assert float(x / y) == pytest.approx(float(x) / float(y))


def test_equality_is_exact_not_floating():
    # 2 - sqrt3 differs from 0.26794919243... by less than any float epsilon test
    # would notice if we were sloppy; exact comparison must still distinguish.
    a = Alg(2, 0, -1, 0)
    b = Alg(Fraction(26794919243112270, 10**17))
    assert a != b
    assert a == Alg(2) - SQRT3


def test_inverse_round_trips():
    for value in (SQRT2, SQRT3 + 1, Alg(1, 1, 1, 1), Alg(0, 3, -2, 5)):
        assert value * value.inverse() == ONE
        assert (1 / value) * value == ONE


def test_zero_division():
    with pytest.raises(ZeroDivisionError):
        ONE / ZERO
    with pytest.raises(ZeroDivisionError):
        ZERO.inverse()


def test_hash_consistency():
    assert hash(Alg(3, 0, 2, 0)) == hash(3 + 2 * SQRT3)
    assert len({Alg(1), Alg(1, 0, 0, 0), ONE}) == 1


def test_ordering_matches_floats():
    values = [ZERO, ONE, SQRT2, SQRT3, SQRT6, Alg(-1), Alg(2, -1, 0, 0)]
    as_floats = sorted(float(v) for v in values)
    assert [float(v) for v in sorted(values)] == as_floats


def test_rationality():
    assert Alg(Fraction(7, 3)).is_rational()
    assert not SQRT3.is_rational()


@pytest.mark.parametrize("value, sign", [
    (Alg(0), 0), (Alg(-1), -1), (Alg(-2, 0, 1), -1), (Alg(0, -1, 1), 1), (Alg(0, 0, 1, -1), -1),
    # Negative, though their float images are positive.
    (Alg(271736178976085, 0, -156886956080403), -1),
    (Alg(2030458102, 0, 0, -828931049), -1),
    (Alg(4114, 11592, 10472, -15777), -1),
])
def test_sign_is_exact_on_every_radical(value, sign):
    assert value.sign() == sign
    assert (-value).sign() == -sign


def test_fraction_reuse_does_not_retain_subclass_behaviour():
    value = Fraction(7, 13)
    assert _exact_fraction(value) is value

    class CustomFraction(Fraction):
        pass

    assert type(_exact_fraction(CustomFraction(7, 13))) is Fraction
    assert Alg(152.4).a == Fraction(762, 5)


def test_alg_hash_memo_is_not_a_constructor_field():
    x = Alg(1, 2, 3, 4)
    assert hash(x) == hash(Alg(1, 2, 3, 4))  # memoises x's hash
    # A copy with other coefficients must not inherit that memo: equal values
    # hash equal, so the copy is found in sets and dicts of fresh values.
    y = replace(x, a=5)
    assert y == Alg(5, 2, 3, 4)
    assert hash(y) == hash(Alg(5, 2, 3, 4)) and hash(y) != hash(x)
    assert y in {Alg(5, 2, 3, 4)} and {y: 1}[Alg(5, 2, 3, 4)] == 1
    assert pickle.loads(pickle.dumps(x)) == x
    assert hash(pickle.loads(pickle.dumps(x))) == hash(x)
    assert hash(copy.deepcopy(x)) == hash(x)
    assert repr(x) == repr(Alg(1, 2, 3, 4))
