"""Draw layouts, top-down, with matplotlib.

The drawing is deliberately toy-like: a grey ballast band per piece, two rails, sleeper
ticks, and dots at the joints.  Raised and climbing track is tinted by its height above
the layout's lowest track, and bridge pieces and track raised on bricks have their
elevation printed on them.  Where track passes over track, the track that is higher
there is drawn on top: climbing track is ordered one sleeper spacing at a time, not by
its piece's mean height.  Output format follows the
file extension (``.png``, ``.svg``, ``.pdf``); pass no path to get the figure back
for further fiddling.

matplotlib is imported lazily so the geometry and solver work in environments without
it (it is an optional dependency, installed via ``duplotrain[render]``).
"""

from __future__ import annotations

import math
from bisect import bisect_left
from collections.abc import Iterator, Sequence
from typing import TYPE_CHECKING

from .catalog import ACCESSORIES, BRICK
from .layout import Layout

if TYPE_CHECKING:  # pragma: no cover
    from matplotlib.axes import Axes
    from matplotlib.figure import Figure

__all__ = ["render_layout"]

BALLAST_EDGE = "#8d949c"
RAIL = "#6d7278"
SLEEPER = "#9aa0a7"
JOINT = "#4d5359"
OPEN_END = "#d0342c"

#: Estimated rail gauge (mm, centre to centre).  Cosmetic only.
GAUGE = 48.0

#: Elevation colour scale, one hue band per bridge-crest level (76.8 mm each):
#: ballast grey at ground, then amber, brick red, purple, indigo, glacier blue
#: and finally snow at level six -- a mountain's worth of climbing.  Pieces show
#: the gradient along their run, so up-ramps visibly change toward their high
#: end and every extra stacked climb shifts into the next band.
ELEVATION_STOPS = [
    (0.0, (185, 190, 196)),    # ballast grey
    (76.8, (214, 164, 76)),    # amber: one crest up
    (153.6, (196, 94, 69)),    # brick red: two crests
    (230.4, (142, 79, 150)),   # purple: three
    (307.2, (86, 96, 178)),    # indigo: four
    (384.0, (70, 150, 180)),   # glacier blue: five
    (460.8, (225, 230, 238)),  # snow: six crests up
]


def elevation_color(z: float) -> str:
    """Hex colour for elevation *z* (mm), interpolated over ELEVATION_STOPS."""
    stops = ELEVATION_STOPS
    if z <= stops[0][0]:
        r, g, b = stops[0][1]
    elif z >= stops[-1][0]:
        r, g, b = stops[-1][1]
    else:
        for (z0, c0), (z1, c1) in zip(stops, stops[1:], strict=False):
            if z <= z1:
                t = (z - z0) / (z1 - z0)
                r, g, b = (
                    c0[0] + t * (c1[0] - c0[0]),
                    c0[1] + t * (c1[1] - c0[1]),
                    c0[2] + t * (c1[2] - c0[2]),
                )
                break
    return f"#{int(r):02x}{int(g):02x}{int(b):02x}"


def _offset(
    line: Sequence[tuple[float, float]], distance: float
) -> list[tuple[float, float]]:
    """Offset a polyline sideways by *distance* (positive = left of travel)."""
    if len(line) < 2:
        return list(line)
    normals: list[tuple[float, float]] = []
    for i in range(len(line)):
        if i == 0:
            dx, dy = line[1][0] - line[0][0], line[1][1] - line[0][1]
        elif i == len(line) - 1:
            dx, dy = line[-1][0] - line[-2][0], line[-1][1] - line[-2][1]
        else:
            dx = line[i + 1][0] - line[i - 1][0]
            dy = line[i + 1][1] - line[i - 1][1]
        norm = math.hypot(dx, dy) or 1.0
        normals.append((-dy / norm, dx / norm))
    return [
        (x + nx * distance, y + ny * distance)
        for (x, y), (nx, ny) in zip(line, normals, strict=True)
    ]


_Point = tuple[float, float]
_Chunk = tuple[float, list[tuple[float, list[_Point]]], list[list[_Point]] | None,
               list[list[_Point]], list[list[_Point]]]


def _mean_height(line3d: Sequence[tuple[float, float, float]], start: int, end: int) -> float:
    """Mean height of the samples *start* to *end* (inclusive) of a path."""
    return sum(point[2] for point in line3d[start:end + 1]) / (end - start + 1)


def _track_chunks(
    lines3d: Sequence[Sequence[tuple[float, float, float]]], half_width: float
) -> Iterator[_Chunk]:
    """The drawing pieces of one placement's paths, each with the height that orders it.

    Yields ``(height, decks, edges, rails, sleepers)``, the decks as ``(tint height,
    polygon)`` pairs.  A flat path stays whole, its deck outlined as one polygon
    (``edges`` is None).  A climbing path is cut at the sample points nearest midway
    between its sleepers: each piece is ordered by its own mean height, so a crossing
    follows the height of the track where it crosses, and carries one sleeper, clear of
    the decks beside it.  Its deck is tinted three sample chords at a time.  Offsets and
    sleeper positions come from the whole path, so the cuts add neither end lines nor
    sleepers.
    """
    for line3d in lines3d:
        line = [(x, y) for x, y, _z in line3d]
        left, right = _offset(line, half_width), _offset(line, -half_width)
        rails = [_offset(line, side) for side in (GAUGE / 2.0, -GAUGE / 2.0)]
        distances = [0.0]
        for (x0, y0), (x1, y1) in zip(line, line[1:], strict=False):
            distances.append(distances[-1] + math.hypot(x1 - x0, y1 - y0))
        total = distances[-1]
        sleepers: dict[int, list[list[_Point]]] = {}
        count = max(2, int(total // 30))
        for i in range(count):
            target = (i + 0.5) / count * total
            segment = max(0, bisect_left(distances, target) - 1)
            if segment + 1 >= len(line):
                continue
            length = distances[segment + 1] - distances[segment]
            if not length:
                continue
            (x0, y0), (x1, y1) = line[segment], line[segment + 1]
            u = (target - distances[segment]) / length
            cx, cy = x0 + u * (x1 - x0), y0 + u * (y1 - y0)
            nx, ny = -(y1 - y0) / length, (x1 - x0) / length
            w = half_width * 0.82
            sleepers.setdefault(segment, []).append(
                [(cx - nx * w, cy - ny * w), (cx + nx * w, cy + ny * w)])
        last = len(line) - 1
        flat = all(point[2] == line3d[0][2] for point in line3d)
        cuts = [0]
        for k in range(1, 1 if flat else count):
            target = k / count * total
            j = bisect_left(distances, target)
            if j > 0 and target - distances[j - 1] < distances[j] - target:
                j -= 1
            if cuts[-1] < j < last:
                cuts.append(j)
        cuts.append(last)
        for start, end in zip(cuts, cuts[1:], strict=False):
            rail_parts = [rail[start:end + 1] for rail in rails]
            ties = [sleeper for i in range(start, end) for sleeper in sleepers.get(i, ())]
            if flat:
                yield line3d[0][2], [(line3d[0][2], left + right[::-1])], None, rail_parts, ties
                continue
            tints = [(s, min(s + 3, end)) for s in range(start, end, 3)]
            decks = [(_mean_height(line3d, s, e), left[s:e + 1] + right[s:e + 1][::-1])
                     for s, e in tints]
            edges = [left[start:end + 1], right[start:end + 1]]
            if start == 0:
                edges.append([left[0], right[0]])
            if end == last:
                edges.append([left[-1], right[-1]])
            yield _mean_height(line3d, start, end), decks, edges, rail_parts, ties


def render_layout(
    layout: Layout,
    path: str | None = None,
    title: str | None = None,
    ax: Axes | None = None,
    dpi: int = 150,
) -> Figure:
    """Draw *layout*; save to *path* if given, and return the figure.

    The *title*, by default the piece counts and size, is drawn as plain text.

    A figure made only to be saved is a standalone :class:`~matplotlib.figure.Figure`:
    pyplot's backend and open figures stay as they were. A caller's *ax* keeps its
    figure open.
    """
    if ax is None and path is not None:
        from matplotlib.figure import Figure

        fig = Figure(figsize=(9, 9))
        ax = fig.subplots()
    elif ax is None:
        import matplotlib.pyplot as plt

        fig, ax = plt.subplots(figsize=(9, 9))
    else:
        fig = ax.figure

    # Heights count from the layout's lowest track, which stands on the floor: a
    # fresh loop's coordinates start wherever its walk began, perhaps up a bridge.
    sampled = [(placement, placement.centrelines(spacing=6.0)) for placement in layout]
    ground = min((z for _placement, lines in sampled for line in lines for _x, _y, z in line),
                 default=0.0)
    sampled = [(placement, [[(x, y, z - ground) for x, y, z in line] for line in lines])
               for placement, lines in sampled]

    # Each height paints in its own band, decks first, then edges, sleepers and rails,
    # so a deck covers everything of the track below it and nothing of the track above
    # (a band per piece, at its mean height, would draw a ground rail over a ramp's high
    # end).  Each band is a few collections, not an artist per piece of track.
    from matplotlib.collections import LineCollection, PolyCollection

    bands: dict[float, tuple[list, list, list, list, list]] = {}
    for placement, lines3d in sampled:
        for height, decks, edges, rails, ties in _track_chunks(
            lines3d, placement.piece.width / 2.0
        ):
            outlined, bare, outlines, sleepers, tracks = bands.setdefault(
                height, ([], [], [], [], []))
            if edges is None:
                outlined.extend(polygon for _tint, polygon in decks)
            else:
                bare.extend(decks)
                outlines.extend(edges)
            sleepers.extend(ties)
            tracks.extend(rails)
    step = min(1.0, 4.0 / max(1, len(bands)))
    for index, height in enumerate(sorted(bands)):
        band = 1 + index * step
        outlined, bare, outlines, sleepers, tracks = bands[height]
        # A flat path's deck is one outlined, antialiased patch.  The pieces of a
        # climbing path are aliased, so no seam shows where they meet, and edged by
        # lines whose projecting caps carry them, like the rails, across the cuts.
        if outlined:
            ax.add_collection(PolyCollection(
                outlined, facecolors=elevation_color(height), edgecolors=BALLAST_EDGE,
                linewidths=0.8, joinstyle="miter", zorder=band))
        if bare:
            ax.add_collection(PolyCollection(
                [polygon for _tint, polygon in bare],
                facecolors=[elevation_color(tint) for tint, _polygon in bare],
                edgecolors="none", antialiaseds=False, zorder=band))
        for segments, colour, width, cap, offset in (
            (outlines, BALLAST_EDGE, 0.8, "projecting", 0.01),
            (sleepers, SLEEPER, 2.2, "butt", 0.5),
            (tracks, RAIL, 1.6, "projecting", 0.501),
        ):
            if segments:
                ax.add_collection(LineCollection(
                    segments, colors=colour, linewidths=width, capstyle=cap,
                    zorder=band + step * offset))
    ax.autoscale_view()

    # Action stones clipped onto pieces (mid-piece, or pulled toward a port face).
    for k, entry in enumerate(layout.accessories):
        index, stone_id = entry[0], entry[1]
        at_port = entry[2] if len(entry) > 2 else None
        info = ACCESSORIES.get(stone_id, {})
        line = layout.placements[index].centrelines()[0]
        mx, my, _ = line[len(line) // 2]
        if at_port is not None:
            px, py = layout.placements[index].port_pose(at_port).xy()
            mx, my = 0.82 * px + 0.18 * mx, 0.82 * py + 0.18 * my
        offset = 30.0 * sum(
            1 for j, other in enumerate(layout.accessories)
            if other[0] == index and j < k
        )
        ax.plot(
            mx,
            my + offset,
            "o",
            color=info.get("color", "#888888"),
            markersize=11,
            markeredgecolor="white",
            markeredgewidth=1.6,
            zorder=6.5,
        )

    # Joints and open ends.
    for index, placement in enumerate(layout):
        for port in range(len(placement.piece.ports)):
            pose = placement.port_pose(port)
            x, y = pose.xy()
            if port in placement.piece.sealed:
                # A buffer's dead face: draw the bumper bar, never an arrow.
                rad = math.radians(pose.degrees + 90)
                bx, by = math.cos(rad) * 26, math.sin(rad) * 26
                ax.plot(
                    [x - bx, x + bx], [y - by, y + by],
                    color="#8c1d18", linewidth=4, zorder=6, solid_capstyle="butt",
                )
            elif (index, port) in layout.links:
                ax.plot(x, y, "o", color=JOINT, markersize=3.5, zorder=6)
            else:
                ax.plot(x, y, "o", color=OPEN_END, markersize=6, zorder=6)
                dx = 18 * math.cos(math.radians(pose.degrees))
                dy = 18 * math.sin(math.radians(pose.degrees))
                ax.annotate(
                    "",
                    xy=(x + dx, y + dy),
                    xytext=(x, y),
                    arrowprops={"arrowstyle": "-|>", "color": OPEN_END, "lw": 1.2},
                    zorder=6,
                )

    # Elevation labels on raised bridge pieces and on track raised on bricks (a slight
    # slope's few millimetres rest on the joints), below any stone.
    stoned = {entry[0] for entry in layout.accessories}
    for index, (placement, lines3d) in enumerate(sampled):
        line = lines3d[0]
        mx, my, mz = line[len(line) // 2]
        raised = min(z for _x, _y, z in line) > float(BRICK) - 1e-6
        if mz > 1.0 and (placement.piece.category == "bridge" or raised):
            ax.annotate(
                f"+{mz:.0f}mm",
                (mx, my),
                xytext=(0, -12 if index in stoned else 0),
                textcoords="offset points",
                fontsize=7,
                ha="center",
                va="center",
                color="#5a4a33",
                zorder=7,
            )

    if title is None:
        width, height = layout.size()
        counts = ", ".join(f"{n} {pid}" for pid, n in sorted(layout.piece_counts.items()))
        title = f"{counts}  |  {width / 10:.0f} x {height / 10:.0f} cm"
    # Plain text: a "$" in a piece id is no mathematics.
    ax.set_title(title, fontsize=10, parse_math=False)
    ax.set_aspect("equal")
    ax.margins(0.08)
    ax.set_xticks([])
    ax.set_yticks([])
    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.set_facecolor("#f4f2ee")

    if path is not None:
        fig.savefig(path, dpi=dpi, bbox_inches="tight")
    return fig
