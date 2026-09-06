"""Bounded parsing for untrusted layout JSON (shared by the CLI and editor)."""

from __future__ import annotations

from fractions import Fraction

MAX_JSON_BYTES = 2 * 1024 * 1024
MAX_PLACEMENTS = 1500
MAX_COEFFICIENT_LENGTH = 48


def _signed_decimal(text: str) -> bool:
    """An optional sign followed by ASCII digits, with no regex backtracking."""
    digits = text[1:] if text.startswith(("+", "-")) else text
    return bool(digits) and digits.isascii() and digits.isdigit()


def rational_coefficient(value: object) -> Fraction:
    """Accept bounded integers or n/d strings, never exponent notation.

    Bounding text length alone is insufficient: ``1e999999999`` is short but
    makes Fraction construct an enormous integer. Validate the grammar first.
    """
    if type(value) not in (int, str):
        raise ValueError("frame coefficients must be integers or rational strings")
    if isinstance(value, int) and value.bit_length() > 160:
        raise ValueError("frame coefficient too large")
    text = str(value)
    # Reject long input before scanning or converting either component.
    if len(text) > MAX_COEFFICIENT_LENGTH:
        raise ValueError("frame coefficients must be bounded integers or n/d strings")
    numerator, sep, denominator = text.partition("/")
    if not _signed_decimal(numerator) or (sep and not _signed_decimal(denominator)):
        raise ValueError("frame coefficients must be bounded integers or n/d strings")
    den = int(denominator) if sep else 1
    if den == 0:
        raise ValueError("frame coefficient denominator must not be zero")
    result = Fraction(int(numerator), den)
    # Also keep downstream float drawing/grid arithmetic in a useful range.
    if abs(result) > 10**9:
        raise ValueError("frame coefficient magnitude exceeds 1000000000")
    return result


def check_layout_json(data: object) -> None:
    """Validate structure and resource bounds before constructing any layout."""
    if not isinstance(data, dict):
        raise ValueError("layout must be a JSON object")
    if data.get("format") != "duplotrain-layout/1":
        raise ValueError("unrecognised layout format (expected duplotrain-layout/1)")
    placements = data.get("placements")
    if not isinstance(placements, list) or len(placements) > MAX_PLACEMENTS:
        raise ValueError(f"placements must be a list (limit {MAX_PLACEMENTS})")
    for entry in placements:
        if not isinstance(entry, dict):
            raise ValueError("placement entries must be objects")
        if not isinstance(entry.get("piece"), str) or len(entry["piece"]) > 40:
            raise ValueError("invalid piece id")
        frame = entry.get("frame")
        if not isinstance(frame, dict):
            raise ValueError("placement frame missing")
        for axis in ("x", "y", "z"):
            coeffs = frame.get(axis)
            if not isinstance(coeffs, list) or len(coeffs) != 4:
                raise ValueError(f"frame {axis} must contain exactly 4 coefficients")
            for coefficient in coeffs:
                rational_coefficient(coefficient)
        heading = frame.get("heading")
        if type(heading) is not int or abs(heading) > 10**6:
            raise ValueError("frame heading out of bounds")
    links = data.get("links", [])
    if not isinstance(links, list) or len(links) > 6000:
        raise ValueError("links must be a list (limit 6000)")
    for entry in links:
        if (not isinstance(entry, list) or len(entry) != 4
                or any(type(v) is not int or abs(v) > 10**6 for v in entry)):
            raise ValueError("links must be [i, port, j, port] integer rows")
    accessories = data.get("accessories", [])
    if not isinstance(accessories, list) or len(accessories) > 200:
        raise ValueError("accessories must be a list (limit 200)")
    for entry in accessories:
        if not isinstance(entry, list) or not 2 <= len(entry) <= 3:
            raise ValueError("accessory rows must be [index, stone] or [index, stone, port]")
        if (type(entry[0]) is not int or abs(entry[0]) > 10**6
                or not isinstance(entry[1], str) or len(entry[1]) > 40):
            raise ValueError("accessory row out of bounds")
        if len(entry) == 3 and (type(entry[2]) is not int or abs(entry[2]) > 64):
            raise ValueError("accessory port out of bounds")
