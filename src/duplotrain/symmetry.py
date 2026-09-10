"""Exact, route-aware placement identities for search-move deduplication.

Matching connector poses alone does not prove that two placements occupy the
same space. Keep each primitive path (up to reversal) as well as its ports and
routes. Unknown segment implementations conservatively keep distinct frames.
"""

from __future__ import annotations

from .geometry import HEADING_STEPS, Pose, cos_sin
from .pieces import Arc, PieceType, Ramp, Straight


def pose_key(pose: Pose, mirror: bool = False) -> tuple:
    """An exactly ordered pose key; never compare field elements as floats."""
    return (
        pose.x.coeffs(), (-pose.y if mirror else pose.y).coeffs(),
        pose.z.coeffs(), (-pose.heading if mirror else pose.heading) % HEADING_STEPS,
    )


def placement_key(piece: PieceType, frame: Pose, mirror: bool = False) -> tuple:
    """Identify full geometry and route incidence, not just endpoint positions.

    Primitive sequences are intentionally not simplified across segment splits:
    failing to merge a redundant move is safe; merging distinct shapes is not.
    """
    ports = tuple(
        pose_key(frame.then(p.pose.x, p.pose.y, p.pose.z, p.pose.heading), mirror)
        for p in piece.ports
    )
    if any(type(seg) not in (Straight, Ramp, Arc)
           for path in piece.paths for seg in path.segments):
        return ("opaque", pose_key(frame), mirror)

    paths = []
    for path in piece.paths:
        cursor = frame.then(path.start.x, path.start.y, path.start.z, path.start.heading)
        forward, backward = [], []
        for seg in path.segments:
            end = cursor.then(*seg.delta(), seg.turn_steps)
            a, b = pose_key(cursor, mirror)[:3], pose_key(end, mirror)[:3]
            if type(seg) is Arc:
                c, s = cos_sin(cursor.heading)
                sign = 1 if seg.degrees >= 0 else -1
                centre = Pose(cursor.x - sign * seg.radius * s,
                              cursor.y + sign * seg.radius * c, cursor.z, 0)
                centre_key = pose_key(centre, mirror)[:3]
                turn = -seg.degrees if mirror else seg.degrees
                forward.append((1, a, b, centre_key, seg.radius.coeffs(), turn))
                backward.append((1, b, a, centre_key, seg.radius.coeffs(), -turn))
            else:
                forward.append((0, a, b))
                backward.append((0, b, a))
            cursor = end
        paths.append(min(tuple(forward), tuple(reversed(backward))))

    routes = tuple(sorted(
        (min(ports[r.port_a], ports[r.port_b]), max(ports[r.port_a], ports[r.port_b]),
         paths[r.path_index])
        for r in piece.routes
    ))
    return (
        "paths",
        tuple(sorted((port, i in piece.sealed) for i, port in enumerate(ports))),
        tuple(sorted(paths)), routes,
    )
