"""Exact centreline unions for congruence sampling and total running length.

Straight/Ramp segments are unioned on their exact supporting lines before
sampling. Circular arcs are unioned in fixed 15-degree sectors, independent of
how a catalogue splits an arc into pieces or segments. Geometry, not sample
multiplicity, determines the translation origin and canonical orientation.
Unknown Segment subclasses retain their own sampling and length implementations
rather than being treated as lines.
"""

from __future__ import annotations

import math
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import cmp_to_key, lru_cache
from math import gcd, lcm
from typing import TYPE_CHECKING

from .exact import Alg
from .geometry import DEGREES_PER_STEP, HEADING_STEPS, Pose, cos_sin
from .pieces import Arc, Ramp, Segment, Straight

if TYPE_CHECKING:
    from .layout import Layout

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


@dataclass(frozen=True, slots=True)
class _Curve:
    """Normalized exact primitives; no sample counts or piece boundaries."""

    lines: tuple[tuple[_Point, _Point], ...]
    circles: tuple[tuple[_Point, Alg, tuple[int, ...]], ...]
    isolated: frozenset[_Point]
    opaque: tuple[tuple[Pose, Pose, Segment], ...]
    origin: _Point


#: Exact primitives of a placed piece depend only on the piece and its frame,
#: and an enumeration replays the same placements in thousands of candidate
#: layouts. Bounded: cleared wholesale when full.
_PRIMITIVE_CACHE: dict[tuple, tuple] = {}
_PRIMITIVE_CACHE_LIMIT = 8192


def _placement_primitives(placement) -> tuple:
    """(line intervals, arc sectors, isolated points, opaque segments) of one placement."""
    key = (placement.piece, placement.frame)
    cached = _PRIMITIVE_CACHE.get(key)
    if cached is not None:
        return cached
    lines: list = []
    arcs: list = []
    isolated: list = []
    opaque: list = []
    for path in placement.piece.paths:
        cursor = placement.frame.then(*_xyz(path.start), path.start.heading)
        for segment in path.segments:
            end = cursor.then(*segment.delta(), segment.turn_steps)
            a, b = _xyz(cursor), _xyz(end)
            if type(segment) in (Straight, Ramp):
                if a == b:
                    isolated.append(a)
                else:
                    line = _line_key(a, b)
                    lo, hi = a[line[0]], b[line[0]]
                    low_point, high_point = a, b
                    if _compare(lo, hi) > 0:
                        lo, hi = hi, lo
                        low_point, high_point = b, a
                    # The endpoints are exactly what _on_line yields at lo and hi.
                    lines.append((line, lo, hi, low_point, high_point))
            elif type(segment) is Arc:
                if not segment.radius or not segment.degrees:
                    isolated.append(a)
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
                    sectors = frozenset(
                        (first + i) % HEADING_STEPS for i in range(min(count, HEADING_STEPS))
                    )
                    # Sector boundaries are the arc's feature points: computed
                    # once per placed arc, not once per candidate layout.
                    boundaries = {}
                    for sector in sectors:
                        for h in (sector, sector + 1):
                            if h not in boundaries:
                                boundaries[h] = _on_circle(centre, radius, h)
                    arcs.append(((centre, radius), sectors, boundaries))
            else:
                opaque.append((cursor, end, segment))
            cursor = end
    cached = (tuple(lines), tuple(arcs), tuple(isolated), tuple(opaque))
    if len(_PRIMITIVE_CACHE) >= _PRIMITIVE_CACHE_LIMIT:
        _PRIMITIVE_CACHE.clear()
    _PRIMITIVE_CACHE[key] = cached
    return cached


def _normalise(layout: Layout) -> _Curve:
    """Union exact primitives and choose an equivariant translation origin."""
    line_groups = defaultdict(list)
    circles = defaultdict(set)
    endpoints: dict[tuple, dict] = defaultdict(dict)  # line -> axis value -> point
    boundaries: dict[tuple, dict] = defaultdict(dict)  # circle -> heading -> point
    isolated: set[_Point] = set()
    opaque = []
    for placement in layout:
        lines, arcs, points, segments = _placement_primitives(placement)
        for line, lo, hi, low_point, high_point in lines:
            line_groups[line].append((lo, hi))
            points_on = endpoints[line]
            points_on[lo] = low_point
            points_on[hi] = high_point
        for circle, sectors, sector_points in arcs:
            circles[circle].update(sectors)
            boundaries[circle].update(sector_points)
        isolated.update(points)
        opaque.extend(segments)

    lines = []
    features: set[_Point] = set()
    for line_id, intervals in line_groups.items():
        _axis, direction, origin = line_id
        points_on = endpoints[line_id]
        intervals.sort(key=cmp_to_key(lambda a, b: _compare(a[0], b[0])))
        merged = []
        for lo, hi in intervals:
            if merged and _compare(lo, merged[-1][1]) <= 0:
                if _compare(hi, merged[-1][1]) > 0:
                    merged[-1] = (merged[-1][0], hi)
            else:
                merged.append((lo, hi))
        for lo, hi in merged:
            # Interval ends are segment ends whose exact points the placement
            # cache holds; on the same line an equal value is the same point.
            a, b = points_on[lo], points_on[hi]
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
        sector_points = boundaries[centre, radius]
        for sector in sectors:
            features.add(sector_points[sector])
            features.add(sector_points[sector + 1])
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
    # Unique normalized endpoints/sector boundaries transform as a set. Averaging
    # them exactly makes translation independent of segmentation and duplication.
    # The exact average is summed in integers over one common denominator, with
    # one Fraction per coefficient at the end.
    if features:
        rows = [tuple(value.coeffs() for value in point) for point in features]
        denominator = 1
        for point in rows:
            for row in point:
                for coefficient in row:
                    denominator = lcm(denominator, coefficient.denominator)
        count = len(rows) * denominator
        sums = [[0, 0, 0, 0] for _ in range(3)]
        for point in rows:
            for i, row in enumerate(point):
                total = sums[i]
                for j, coefficient in enumerate(row):
                    total[j] += coefficient.numerator * (denominator // coefficient.denominator)
        origin = tuple(Alg(*(Fraction(value, count) for value in total)) for total in sums)
    else:
        origin = (Alg(0), Alg(0), Alg(0))
    return _Curve(tuple(lines), tuple((c, r, tuple(sorted(sectors)))
                                     for (c, r), sectors in circles.items()),
                  frozenset(isolated), tuple(opaque), origin)


def _point_key(point: _Point) -> tuple:
    # Coefficient tuples give a total, exact, deterministic order. Their ordering
    # need not be physical coordinate order: it only chooses one orbit member.
    return tuple(value.coeffs() for value in point)


def _in_frame(curve: _Curve, heading: int, mirror: bool) -> _Curve:
    """Apply the entire rigid transform in the field, before any float conversion."""
    c, s = cos_sin(heading)
    cache: dict[_Point, _Point] = {}

    def transform(point: _Point) -> _Point:
        if point not in cache:
            x, y, z = (p - o for p, o in zip(point, curve.origin, strict=True))
            if mirror:
                y = -y
            cache[point] = (c * x - s * y, s * x + c * y, z)
        return cache[point]

    lines = tuple(tuple(sorted((transform(a), transform(b)), key=_point_key))
                  for a, b in curve.lines)
    circles = tuple((transform(centre), radius,
                     tuple(sorted((heading - h - 1 if mirror else heading + h) % HEADING_STEPS
                                  for h in sectors)))
                    for centre, radius, sectors in curve.circles)
    # Opaque samples remain local to their segment. Keep the local reflection for
    # _sample rather than pretending an unknown segment is a known primitive.
    opaque = tuple((Pose(*transform(_xyz(start)), heading + (-start.heading if mirror
                                                           else start.heading)),
                    Pose(*transform(_xyz(end)), heading + (-end.heading if mirror
                                                         else end.heading)), segment)
                   for start, end, segment in curve.opaque)
    return _Curve(lines, circles, frozenset(transform(p) for p in curve.isolated),
                  opaque, (Alg(0), Alg(0), Alg(0)))


def _identity(curve: _Curve) -> tuple:
    """Exact union identity in one frame, independent of traversal/collection order."""
    return (
        tuple(sorted((_point_key(a), _point_key(b)) for a, b in curve.lines)),
        tuple(sorted((_point_key(c), r.coeffs(), sectors) for c, r, sectors in curve.circles)),
        tuple(sorted(_point_key(p) for p in curve.isolated)),
    )


def _rotation_ints() -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    """Four times the exact cosine and sine of every heading, as integer vectors."""
    table = []
    for heading in range(HEADING_STEPS):
        pair = []
        for value in cos_sin(heading):
            scaled = [coefficient * 4 for coefficient in value.coeffs()]
            assert all(f.denominator == 1 for f in scaled)
            pair.append(tuple(int(f) for f in scaled))
        table.append(tuple(pair))
    return tuple(table)


_ROTATION_INTS = _rotation_ints()


def _mul4(u: tuple[int, ...], v: tuple[int, ...]) -> tuple[int, int, int, int]:
    """Product in Q(sqrt2, sqrt3) of two coefficient vectors over 1, sqrt2, sqrt3, sqrt6."""
    a, b, c, d = u
    p, q, r, s = v
    return (
        a * p + 2 * b * q + 3 * c * r + 6 * d * s,
        a * q + b * p + 3 * (c * s + d * r),
        a * r + c * p + 2 * (b * s + d * q),
        a * s + d * p + b * r + c * q,
    )


def _canonical_frame(curve: _Curve) -> tuple[tuple, _Curve]:
    """The exact identity of the smallest frame, and that frame materialised.

    Equivalent to comparing the exact identities of all 48 frames, but in integer
    arithmetic: every centred point becomes integer coefficient vectors over one
    common denominator, each rotation is an integer bilinear map, and a frame's
    identity is reduced by the gcd of its entries, so congruent curves that
    arrive with different denominators still compare equal and pick the same
    frame. The four products of a point with one cosine and sine serve all four
    quadrant rotations and both reflections, and a quarter turn only permutes
    and negates the reduced vectors. A frame whose reduced scale or smallest
    primitive already exceeds the best one's is discarded before its identity
    is built. The winning frame's exact points are rebuilt from its integer
    vectors, which is what rotating them in the field would have produced.
    """
    exact: set[_Point] = set(curve.isolated)
    for a, b in curve.lines:
        exact.update((a, b))
    for centre, _radius, _sectors in curve.circles:
        exact.add(centre)
    if not exact:
        return (0, (), (), ()), _Curve((), (), frozenset(), (), (Alg(0), Alg(0), Alg(0)))
    # Centre in integer arithmetic: every coefficient of every point and of the
    # origin over one common denominator. A common factor left in the vectors
    # cancels in the gcd reduction below, so the identity is the same as with
    # lowest-terms centred coordinates.
    rows = {point: tuple(value.coeffs() for value in point) for point in exact}
    origin_rows = tuple(value.coeffs() for value in curve.origin)
    denominator = 1
    for vectors in rows.values():
        for vector in vectors:
            for coefficient in vector:
                denominator = lcm(denominator, coefficient.denominator)
    for vector in origin_rows:
        for coefficient in vector:
            denominator = lcm(denominator, coefficient.denominator)
    origin_ints = tuple(
        tuple(coefficient.numerator * (denominator // coefficient.denominator)
              for coefficient in vector)
        for vector in origin_rows
    )
    ints = {
        point: tuple(
            tuple(coefficient.numerator * (denominator // coefficient.denominator) - offset
                  for coefficient, offset in zip(vector, origin_vector, strict=True))
            for vector, origin_vector in zip(vectors, origin_ints, strict=True)
        )
        for point, vectors in rows.items()
    }
    heights = {point: tuple(4 * value for value in z) for point, (_x, _y, z) in ints.items()}
    circles = [(centre, radius.coeffs(), sectors) for centre, radius, sectors in curve.circles]
    lines, isolated = curve.lines, curve.isolated
    scale = 4 * denominator
    best = None
    best_screen = None
    for base in range(6):
        cosine, sine = _ROTATION_INTS[base]
        products = {
            point: (_mul4(cosine, x), _mul4(sine, y), _mul4(sine, x), _mul4(cosine, y))
            for point, (x, y, _z) in ints.items()
        }
        for mirror in (False, True):
            # Reflect (y -> -y) first, then rotate by the base heading.
            planar = {}
            for point, (cx, sy, sx, cy) in products.items():
                if mirror:
                    planar[point] = (tuple(u + v for u, v in zip(cx, sy, strict=True)),
                                     tuple(u - v for u, v in zip(sx, cy, strict=True)))
                else:
                    planar[point] = (tuple(u - v for u, v in zip(cx, sy, strict=True)),
                                     tuple(u + v for u, v in zip(sx, cy, strict=True)))
            # Quarter turns permute and negate entries, so one gcd serves all four.
            common = scale
            for x, y in planar.values():
                for value in x:
                    common = gcd(common, value)
                for value in y:
                    common = gcd(common, value)
            for z in heights.values():
                for value in z:
                    common = gcd(common, value)
            reduced_scale = scale // common
            if best is not None and reduced_scale > best_screen[0]:
                continue
            # The gcd divides every entry exactly, so negation commutes with the
            # reduction: the four quadrants are (x, y), (-y, x), (-x, -y), (y, -x).
            rotated = {}
            for point, (x, y) in planar.items():
                rx = tuple(value // common for value in x)
                ry = tuple(value // common for value in y)
                nrx = tuple(-value for value in rx)
                nry = tuple(-value for value in ry)
                rz = tuple(value // common for value in heights[point])
                rotated[point] = ((rx, ry, rz), (nry, rx, rz), (nrx, nry, rz), (ry, nrx, rz))
            for quadrant in range(4):
                heading = base + 6 * quadrant
                reduced = {point: frames[quadrant] for point, frames in rotated.items()}

                def sectors_of(sectors, heading=heading, mirror=mirror):
                    return tuple(sorted((heading - h - 1 if mirror else heading + h)
                                        % HEADING_STEPS for h in sectors))

                # The identity orders lines, then circles, then isolated points,
                # so its first nonempty component decides against a larger one.
                if lines:
                    first = min(tuple(sorted((reduced[a], reduced[b]))) for a, b in lines)
                elif circles:
                    first = min((reduced[centre], radius, sectors_of(sectors))
                                for centre, radius, sectors in circles)
                else:
                    first = min((reduced[point] for point in isolated), default=())
                screen = (reduced_scale, first)
                if best is not None and screen > best_screen:
                    continue
                identity = (
                    reduced_scale,
                    tuple(sorted(tuple(sorted((reduced[a], reduced[b]))) for a, b in lines)),
                    tuple(sorted((reduced[centre], radius, sectors_of(sectors))
                                 for centre, radius, sectors in circles)),
                    tuple(sorted(reduced[point] for point in isolated)),
                )
                if best is None or identity < best[0]:
                    best = (identity, heading, mirror, reduced, reduced_scale)
                    best_screen = screen
    identity, heading, mirror, reduced, reduced_scale = best

    def exact_point(point: _Point) -> _Point:
        return tuple(
            Alg(*(Fraction(value, reduced_scale) for value in vector))
            for vector in reduced[point]
        )

    moved = {point: exact_point(point) for point in reduced}
    frame_lines = tuple(tuple(sorted((moved[a], moved[b]), key=_point_key)) for a, b in lines)
    frame_circles = tuple(
        (moved[centre], radius,
         tuple(sorted((heading - h - 1 if mirror else heading + h) % HEADING_STEPS
                      for h in sectors)))
        for centre, radius, sectors in curve.circles
    )
    return identity, _Curve(frame_lines, frame_circles, frozenset(moved[p] for p in isolated), (),
                            (Alg(0), Alg(0), Alg(0)))


def _spacing(spacing: float) -> None:
    if not math.isfinite(spacing) or spacing <= 0:
        raise ValueError("spacing must be finite and positive")


def _sample(
    curve: _Curve, spacing: float, *, mirror_opaque: bool = False
) -> list[tuple[float, float, float]]:
    """Sample only after a frame has been chosen with exact arithmetic."""
    def relative(point: _Point) -> tuple[float, float, float]:
        return tuple(float(p) for p in point)

    points = [relative(point) for point in curve.isolated]
    for a, b in curve.lines:
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
    for centre, radius, sectors in curve.circles:
        cx, cy, cz = relative(centre)
        r = float(radius)
        count = max(1, math.ceil(r * math.radians(DEGREES_PER_STEP) / spacing))
        for sector in sectors:
            points.append(relative(_on_circle(centre, radius, sector)))
            points.append(relative(_on_circle(centre, radius, sector + 1)))
            for i in range(1, count):
                angle = math.radians(DEGREES_PER_STEP * (sector + i / count))
                points.append((cx + r * math.cos(angle), cy + r * math.sin(angle), cz))
    for start, _end, segment in curve.opaque:
        ox, oy, oz = relative(_xyz(start))
        c, s = (float(v) for v in cos_sin(start.heading))
        points.append((ox, oy, oz))
        for x, y, z, _heading in segment.sample(spacing):
            if mirror_opaque:
                y = -y
            points.append((ox + c * x - s * y, oy + s * x + c * y, oz + z))
    return points


#: The sampled key is a function of the exact canonical identity alone, and an
#: enumeration keys every congruent duplicate it finds. Bounded: cleared when full.
_KEY_CACHE: dict[tuple, tuple] = {}
_KEY_CACHE_LIMIT = 4096


def curve_key(layout: Layout, spacing: float, decimals: int) -> tuple:
    """Choose an exact canonical frame, then sample and round just once.

    Rotating already-rounded or floating samples changes half-way rounding cases.
    Each exact orbit is identical under all 24 rotations and reflection, so its
    minimum exact primitive descriptor supplies bit-identical sampling inputs.
    The returned key is still approximate; it is not an exact congruence proof.
    """
    _spacing(spacing)
    curve = _normalise(layout)

    def rounded(frame: _Curve, mirror: bool = False) -> tuple:
        return tuple(sorted({tuple(round(v, decimals) for v in p)
                             for p in _sample(frame, spacing, mirror_opaque=mirror)}))

    if curve.opaque:
        # No exact primitive descriptor exists for arbitrary user Segment
        # implementations. Preserve their sampled shape across the orbit.
        best_sample: tuple | None = None
        for mirror in (False, True):
            for heading in range(HEADING_STEPS):
                candidate = rounded(_in_frame(curve, heading, mirror), mirror)
                if best_sample is None or candidate < best_sample:
                    best_sample = candidate
        assert best_sample is not None
        return best_sample
    identity, frame = _canonical_frame(curve)
    cache_key = (identity, spacing, decimals)
    key = _KEY_CACHE.get(cache_key)
    if key is None:
        key = rounded(frame)
        if len(_KEY_CACHE) >= _KEY_CACHE_LIMIT:
            _KEY_CACHE.clear()
        _KEY_CACHE[cache_key] = key
    return key


def curve_length(layout: Layout) -> float:
    """Length of the 3D centreline union, not just one route per placement.

    Known collinear intervals and circular sectors are counted once even when
    routes share them or duplicate them with different segment boundaries. For an
    unknown Segment, its declared length is used; arbitrary-shape intersections
    cannot be unioned without a primitive description.
    """
    curve = _normalise(layout)
    lengths = [math.sqrt(float(sum(((y - x) * (y - x) for x, y in zip(a, b, strict=True)),
                                  Alg(0)))) for a, b in curve.lines]
    lengths.extend(float(radius) * math.radians(DEGREES_PER_STEP * len(sectors))
                   for _centre, radius, sectors in curve.circles)
    lengths.extend(segment.length() for _start, _end, segment in curve.opaque)
    return math.fsum(lengths)
