"""Draw layouts, top-down, with matplotlib.

The drawing is deliberately toy-like: a grey ballast band per piece, two rails, sleeper
ticks, and dots at the joints.  Bridge pieces get a warmer tint and their elevation
printed on them.  Output format follows the file extension (``.png``, ``.svg``,
``.pdf``); pass no path to get the figure back for further fiddling.

matplotlib is imported lazily so the geometry and solver work in environments without
it (it is an optional dependency, installed via ``duplotrain[render]``).
"""

from __future__ import annotations

import math
from typing import TYPE_CHECKING, Sequence

from .layout import Layout

if TYPE_CHECKING:  # pragma: no cover
    from matplotlib.axes import Axes
    from matplotlib.figure import Figure

__all__ = ["render_layout"]

BALLAST = "#b9bec4"
BALLAST_EDGE = "#8d949c"
BRIDGE = "#c9b79b"
RAIL = "#6d7278"
SLEEPER = "#9aa0a7"
JOINT = "#4d5359"
OPEN_END = "#d0342c"

#: Estimated rail gauge (mm, centre to centre).  Cosmetic only.
GAUGE = 48.0


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
        for (x, y), (nx, ny) in zip(line, normals)
    ]


def _band(line: Sequence[tuple[float, float]], half_width: float) -> list[tuple[float, float]]:
    """Closed polygon covering the line swept to +/- half_width."""
    left = _offset(line, half_width)
    right = _offset(line, -half_width)
    return left + right[::-1]


def render_layout(
    layout: Layout,
    path: str | None = None,
    title: str | None = None,
    ax: "Axes | None" = None,
    dpi: int = 150,
) -> "Figure":
    """Draw *layout*; save to *path* if given, and return the figure."""
    import matplotlib

    if path is not None and ax is None:
        matplotlib.use("Agg", force=False)
    import matplotlib.pyplot as plt

    if ax is None:
        fig, ax = plt.subplots(figsize=(9, 9))
    else:
        fig = ax.figure

    max_z = 1e-9
    for placement in layout:
        for line in placement.centrelines():
            for _x, _y, z in line:
                max_z = max(max_z, z)

    # Ballast bands first, then rails and sleepers on top, so overlaps look right.
    features: list[tuple[float, list[list[tuple[float, float]]], float, bool]] = []
    for placement in layout:
        elevated = placement.piece.category == "bridge"
        lines3d = placement.centrelines(spacing=6.0)
        lines = [[(x, y) for x, y, _ in line] for line in lines3d]
        mean_z = sum(z for line in lines3d for _x, _y, z in line) / max(
            1, sum(len(line) for line in lines3d)
        )
        features.append((mean_z, lines, placement.piece.width / 2.0, elevated))

    for mean_z, lines, half_width, elevated in sorted(features, key=lambda f: f[0]):
        shade = 1.0 - 0.25 * (mean_z / max_z if max_z > 0 else 0.0)
        # One zorder band per piece: an elevated deck (ballast ~1.8) must paint over a
        # ground piece's rails (~1.5), not thread between another piece's layers.
        band = 1 + mean_z / 100.0
        for line in lines:
            face = BRIDGE if elevated else BALLAST
            poly = _band(line, half_width)
            ax.fill(
                [p[0] for p in poly],
                [p[1] for p in poly],
                facecolor=face,
                edgecolor=BALLAST_EDGE,
                linewidth=0.8,
                alpha=min(1.0, 0.75 + 0.25 * shade),
                zorder=band,
            )
        for line in lines:
            z = band + 0.5
            # Sleepers.
            total = sum(
                math.hypot(bx - ax_, by - ay) for (ax_, ay), (bx, by) in zip(line, line[1:])
            )
            n_sleepers = max(2, int(total // 30))
            for i in range(n_sleepers):
                t = (i + 0.5) / n_sleepers
                target = t * total
                run = 0.0
                for (x0, y0), (x1, y1) in zip(line, line[1:]):
                    seg = math.hypot(x1 - x0, y1 - y0)
                    if run + seg >= target and seg > 0:
                        u = (target - run) / seg
                        cx, cy = x0 + u * (x1 - x0), y0 + u * (y1 - y0)
                        nx, ny = -(y1 - y0) / seg, (x1 - x0) / seg
                        w = half_width * 0.82
                        ax.plot(
                            [cx - nx * w, cx + nx * w],
                            [cy - ny * w, cy + ny * w],
                            color=SLEEPER,
                            linewidth=2.2,
                            solid_capstyle="butt",
                            zorder=z,
                        )
                        break
                    run += seg
            # Rails.
            for side in (GAUGE / 2.0, -GAUGE / 2.0):
                rail = _offset(line, side)
                ax.plot(
                    [p[0] for p in rail],
                    [p[1] for p in rail],
                    color=RAIL,
                    linewidth=1.6,
                    zorder=z + 0.001,
                )

    # Action stones clipped onto pieces (mid-piece, or pulled toward a port face).
    if layout.accessories:
        from .catalog import ACCESSORIES

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

    # Elevation labels on bridge pieces.
    if max_z > 1e-6:
        for placement in layout:
            if placement.piece.category != "bridge":
                continue
            line = placement.centrelines()[0]
            mx, my, mz = line[len(line) // 2]
            if mz > 1.0:
                ax.text(
                    mx,
                    my,
                    f"+{mz:.0f}mm",
                    fontsize=7,
                    ha="center",
                    va="center",
                    color="#5a4a33",
                    zorder=7,
                )

    width, height = layout.size()
    if title is None:
        counts = ", ".join(f"{n} {pid}" for pid, n in sorted(layout.piece_counts.items()))
        title = f"{counts}  |  {width / 10:.0f} x {height / 10:.0f} cm"
    ax.set_title(title, fontsize=10)
    ax.set_aspect("equal")
    ax.margins(0.08)
    ax.set_xticks([])
    ax.set_yticks([])
    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.set_facecolor("#f4f2ee")

    if path is not None:
        fig.savefig(path, dpi=dpi, bbox_inches="tight")
        plt.close(fig)
    return fig
