"""Piece-boundary-independent sampling of a centreline union.

Straight/Ramp segments are unioned on their exact supporting lines before
sampling. Circular arcs are unioned in fixed 15-degree sectors, independent of
how a catalogue splits an arc into pieces or segments. Geometry, not sample
multiplicity, determines the translation origin. Unknown Segment subclasses
retain their own sampling implementation rather than being treated as lines.
"""

from __future__ import annotations

import math
from collections import defaultdict
from fractions import Fraction
from functools import cmp_to_key, lru_cache

from .exact import Alg
from .geometry import DEGREES_PER_STEP, HEADING_STEPS, Pose, cos_sin
from .layout import Layout
from .pieces import Arc, Ramp, Straight

_Point = tuple[Alg, Alg, Alg]


@lru_cache(maxsize=32)
def _radical_bounds(bits: int) -> tuple[tuple[Fraction, Fraction], ...]:
    scale = 1 << bits
    return tuple(
        (Fraction(math.isqrt(n * scale * scale), scale),
         Fraction(math.isqrt(n * scale * scale) + 1, scale))
        for n in (2, 3, 6)
    )


def _compare(a: Alg, b: Alg) -> int:
    """Exact interval ordering; Alg.__lt__ deliberately uses floats elsewhere.

    Refining rational bounds on the three radicals eventually separates every
    nonzero field element from zero. A rounded comparison must not bridge gaps
    between collinear runs or erase an extremely short segment.
    """
    diff = a - b
    if not diff:
        return 0
    if diff.is_rational():
        return 1 if diff.a > 0 else -1
    bits = 16
    while True:
        low = high = diff.a
        for coefficient, (lo, hi) in zip(diff.coeffs()[1:], _radical_bounds(bits), strict=True):
            low += coefficient * (lo if coefficient >= 0 else hi)
            high += coefficient * (hi if coefficient >= 0 else lo)
        if low > 0:
            return 1
        if high < 0:
            return -1
        bits *= 2


def _xyz(pose: Pose) -> _Point:
    return pose.x, pose.y, pose.z


def _line_key(a: _Point, b: _Point) -> tuple[int, _Point, _Point]:
    delta = tuple(y - x for x, y in zip(a, b, strict=True))
    axis = next(i for i, value in enumerate(delta) if value)
    direction = tuple(value / delta[axis] for value in delta)
    origin = tuple(value - d * a[axis] for value, d in zip(a, direction, strict=True))
    return axis, direction, origin


def _on_line(direction: _Point, origin: _Point, t: Alg) -> _Point:
    return tuple(o + d * t for o, d in zip(origin, direction, strict=True))


def _on_circle(centre: _Point, radius: Alg, heading: int) -> _Point:
    c, s = cos_sin(heading)
    return centre[0] + radius * c, centre[1] + radius * s, centre[2]


def curve_points(layout: Layout, spacing: float) -> list[tuple[float, float, float]]:
    """Sample the normalized union about a rigid-motion-equivariant origin.

    Output still uses floating samples; the public congruence key applies its
    requested rounding tolerance. Primitive merging and the translation origin
    use exact geometry, never the varying number of per-piece sample points.
    """
    if not math.isfinite(spacing) or spacing <= 0:
        raise ValueError("spacing must be finite and positive")
    line_groups = defaultdict(list)
    circles = defaultdict(set)
    isolated: set[_Point] = set()
    opaque = []
    for placement in layout:
        for path in placement.piece.paths:
            cursor = placement.frame.then(*_xyz(path.start), path.start.heading)
            for segment in path.segments:
                end = cursor.then(*segment.delta(), segment.turn_steps)
                a, b = _xyz(cursor), _xyz(end)
                if type(segment) in (Straight, Ramp):
                    if a == b:
                        isolated.add(a)
                    else:
                        key = _line_key(a, b)
                        lo, hi = a[key[0]], b[key[0]]
                        if _compare(lo, hi) > 0:
                            lo, hi = hi, lo
                        line_groups[key].append((lo, hi))
                elif type(segment) is Arc:
                    if not segment.radius or not segment.degrees:
                        isolated.add(a)
                    else:
                        sign = 1 if segment.degrees > 0 else -1
                        c, s = cos_sin(cursor.heading)
                        centre = (cursor.x - sign * segment.radius * s,
                                  cursor.y + sign * segment.radius * c, cursor.z)
                        radius = segment.radius
                        start = cursor.heading - sign * (HEADING_STEPS // 4)
                        if _compare(radius, Alg(0)) < 0:
                            radius = -radius
                            start += HEADING_STEPS // 2
                        count = abs(segment.degrees) // DEGREES_PER_STEP
                        first = start if sign > 0 else start - count
                        circles[centre, radius].update(
                            (first + i) % HEADING_STEPS for i in range(min(count, HEADING_STEPS))
                        )
                else:
                    opaque.append((cursor, end, segment))
                cursor = end

    lines = []
    features: set[_Point] = set()
    for (_axis, direction, origin), intervals in line_groups.items():
        intervals.sort(key=cmp_to_key(lambda a, b: _compare(a[0], b[0])))
        merged = []
        for lo, hi in intervals:
            if merged and _compare(lo, merged[-1][1]) <= 0:
                if _compare(hi, merged[-1][1]) > 0:
                    merged[-1] = (merged[-1][0], hi)
            else:
                merged.append((lo, hi))
        for lo, hi in merged:
            a, b = _on_line(direction, origin, lo), _on_line(direction, origin, hi)
            lines.append((a, b))
            features.update((a, b))
        # Zero-length segments inside this union contribute no additional feature.
        isolated = {
            point for point in isolated
            if _on_line(direction, origin, point[_axis]) != point
            or not any(_compare(lo, point[_axis]) <= 0 and _compare(point[_axis], hi) <= 0
                       for lo, hi in merged)
        }
    for (centre, radius), sectors in circles.items():
        for sector in sectors:
            features.add(_on_circle(centre, radius, sector))
            features.add(_on_circle(centre, radius, sector + 1))
        for point in tuple(isolated):
            dx, dy = point[0] - centre[0], point[1] - centre[1]
            if point[2] != centre[2] or dx * dx + dy * dy != radius * radius:
                continue
            for sector in sectors:
                c, s = cos_sin(sector)
                ec, es = cos_sin(sector + 1)
                if _compare(c * dy - s * dx, Alg(0)) >= 0 and (
                    _compare(dx * es - dy * ec, Alg(0)) >= 0
                ):
                    isolated.remove(point)
                    break
    features.update(isolated)
    for start, end, _segment in opaque:
        features.update((_xyz(start), _xyz(end)))
    if not features:
        return []
    # Unique normalized endpoints/sector boundaries transform as a set. Averaging
    # them exactly makes translation independent of segmentation and duplication.
    origin = tuple(sum((p[i] for p in features), Alg(0)) / len(features) for i in range(3))

    def relative(point: _Point) -> tuple[float, float, float]:
        return tuple(float(p - o) for p, o in zip(point, origin, strict=True))

    points = [relative(point) for point in isolated]
    for a, b in lines:
        delta = tuple(y - x for x, y in zip(a, b, strict=True))
        # Compute length before float conversion: lattice rotations must not change
        # ceil(length / spacing) through roundoff at an integer sample count.
        length = math.sqrt(float(sum((d * d for d in delta), Alg(0))))
        count = max(1, math.ceil(length / spacing))
        af, bf = relative(a), relative(b)
        points.extend(
            tuple(x * (1 - i / count) + y * (i / count) for x, y in zip(af, bf, strict=True))
            for i in range(count + 1)
        )
    for (centre, radius), sectors in circles.items():
        cx, cy, cz = relative(centre)
        r = float(radius)
        count = max(1, math.ceil(r * math.radians(DEGREES_PER_STEP) / spacing))
        for sector in sectors:
            points.append(relative(_on_circle(centre, radius, sector)))
            points.append(relative(_on_circle(centre, radius, sector + 1)))
            for i in range(1, count):
                angle = math.radians(DEGREES_PER_STEP * (sector + i / count))
                points.append((cx + r * math.cos(angle), cy + r * math.sin(angle), cz))
    for start, _end, segment in opaque:
        ox, oy, oz = relative(_xyz(start))
        c, s = (float(v) for v in cos_sin(start.heading))
        points.append((ox, oy, oz))
        points.extend((ox + c * x - s * y, oy + s * x + c * y, oz + z)
                      for x, y, z, _heading in segment.sample(spacing))
    return points
