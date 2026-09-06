"""Bounded fraction parser regressions for CodeQL alert #52."""

from fractions import Fraction

import pytest

from duplotrain.validation import MAX_COEFFICIENT_LENGTH, rational_coefficient


@pytest.mark.parametrize(("value", "expected"), [
    (0, Fraction(0)), (-7, Fraction(-7)), ("+42", Fraction(42)),
    ("+0012/-0003", Fraction(-4)), ("-12/-3", Fraction(4)),
    ("1/+3", Fraction(1, 3)), ("-0", Fraction(0)),
    ("0" * MAX_COEFFICIENT_LENGTH, Fraction(0)),
    ("-1000000000", Fraction(-10**9)), ("1000000000", Fraction(10**9)),
])
def test_bounded_fraction_grammar_is_preserved(value, expected):
    assert rational_coefficient(value) == expected


@pytest.mark.parametrize("value", [
    "", "+", "-", "/", "1/", "/1", "1//2", "1/2/3", "1/-", "++1", "--1",
    "1 2", " 1", "1 ", "1\n", "\n1", "1_000", "1.0", "1e999999999",
    "\u0661", "1/\u0662", "\uff11", "\u22121", "1/0", "1/-0", "1000000001",
    True, False, 1.0, None, {}, [],
])
def test_invalid_fraction_grammar_is_rejected(value):
    with pytest.raises(ValueError):
        rational_coefficient(value)


def test_long_coefficients_never_reach_the_component_scanner(monkeypatch):
    import duplotrain.validation as validation

    def unexpected_scan(_text):
        pytest.fail("unbounded input reached the scanner")

    monkeypatch.setattr(validation, "_signed_decimal", unexpected_scan)
    for value in ("9" * 49, "9" * (2 * 1024 * 1024), "1/" + "9" * 100000, 1 << 100000):
        with pytest.raises(ValueError):
            rational_coefficient(value)
