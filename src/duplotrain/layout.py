"""Placed pieces, and the layouts they form.

A :class:`Placement` is one piece pinned down in world space.  A :class:`Layout` is a
set of placements plus the record of which port is plugged into which -- a graph, not
just a list, so that switches and crossings work as naturally as a plain oval.

Layouts are immutable.  :meth:`Layout.attach` returns a new layout, which keeps the
solver's backtracking trivially correct and lets finished layouts be cached and hashed.
The solver itself does not use this class in its inner loop -- it runs on flat tuples
for speed and only builds a ``Layout`` once a candidate is worth keeping.
"""

from __future__ import annotations

import math
from collections.abc import Iterable, Iterator, Mapping
from dataclasses import dataclass
from typing import Any

from .exact import Alg
from .geometry import Pose
from .pieces import PieceType
from .validation import check_layout_json, rational_coefficient

__all__ = ["Placement", "End", "Layout", "layout_to_dict", "layout_from_dict"]

#: A specific connector on a specific placed piece.
End = tuple[int, int]


def _alg_to_json(value: Alg) -> list[str]:
    return [str(c) for c in value.coeffs()]


def _alg_from_json(data: list[str]) -> Alg:
    a, b, c, d = (rational_coefficient(s) for s in data)
    return Alg(a, b, c, d)


@dataclass(frozen=True, slots=True)
class Placement:
    """One piece, positioned in world space.

    ``frame`` is the world pose of the piece's local origin; every port and centreline
    point is derived from it, so a placement is fully determined by the piece and the
    frame.
    """

    piece: PieceType
    frame: Pose

    def port_pose(self, port: int) -> Pose:
        """World pose of one of this piece's connectors (heading points outward)."""
        local = self.piece.ports[port].pose
        return self.frame.then(local.x, local.y, local.z, local.heading)

    def centrelines(self, spacing: float = 8.0) -> list[list[tuple[float, float, float]]]:
        """Every route through the piece, sampled in world coordinates."""
        theta = math.radians(self.frame.degrees)
        cos_t, sin_t = math.cos(theta), math.sin(theta)
        ox, oy, oz = self.frame.xyz()
        out = []
        for path_pts in self.piece.all_centrelines(spacing):
            out.append(
                [
                    (ox + cos_t * x - sin_t * y, oy + sin_t * x + cos_t * y, oz + z)
                    for x, y, z in path_pts
                ]
            )
        return out

    def __repr__(self) -> str:
        return f"Placement({self.piece.id}, {self.frame!r})"


@dataclass(frozen=True, slots=True, eq=False)
class Layout:
    """A set of connected placements.

    ``links`` maps each occupied end to the end it is plugged into.  It is symmetric:
    if ``links[a] == b`` then ``links[b] == a``.  ``accessories`` records action
    stones clipped onto placements as ``(placement index, accessory id)`` pairs --
    they carry no geometry, but they are part of the build.
    """

    placements: tuple[Placement, ...] = ()
    links: Mapping[End, End] = None  # type: ignore[assignment]
    #: (placement, stone id) for a mid-piece stone, (placement, stone id, port) for
    #: one positioned at that connector's face.
    accessories: tuple[tuple, ...] = ()

    def __post_init__(self) -> None:
        if self.links is None:
            object.__setattr__(self, "links", {})

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Layout):
            return NotImplemented
        return (
            self.placements == other.placements
            and dict(self.links) == dict(other.links)
            and sorted(self.accessories) == sorted(other.accessories)
        )

    # -- inspection ------------------------------------------------------------

    def __len__(self) -> int:
        return len(self.placements)

    def __iter__(self) -> Iterator[Placement]:
        return iter(self.placements)

    def ends(self) -> list[End]:
        """Every connector on every piece."""
        return [
            (i, p)
            for i, placement in enumerate(self.placements)
            for p in range(len(placement.piece.ports))
        ]

    def open_ends(self) -> list[End]:
        """Connectors that nothing is plugged into (including sealed dead faces)."""
        return [end for end in self.ends() if end not in self.links]

    def is_sealed(self, end: End) -> bool:
        """True when *end* is a dead face (a buffer's bumper) that can never mate."""
        return end[1] in self.placements[end[0]].piece.sealed

    def connectable_ends(self) -> list[End]:
        """Open ends something could actually plug into."""
        return [end for end in self.open_ends() if not self.is_sealed(end)]

    def pose_of(self, end: End) -> Pose:
        i, p = end
        return self.placements[i].port_pose(p)

    @property
    def is_closed(self) -> bool:
        """True when every real connector is mated -- no loose ends anywhere.

        Sealed faces (buffer bumpers) are not connectors, so a siding properly
        terminated by a buffer stop does not count as loose.
        """
        return bool(self.placements) and not self.connectable_ends()

    @property
    def piece_counts(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for placement in self.placements:
            counts[placement.piece.id] = counts.get(placement.piece.id, 0) + 1
        return counts

    def bounds(self) -> tuple[float, float, float, float]:
        """Outer envelope ``(min_x, min_y, max_x, max_y)`` in mm.

        Centreline samples are grown by each piece's half-width *perpendicular to the
        direction of travel* (plus any declared end overhang along it at the line
        ends), so a straight run reports its true footprint rather than being inflated
        lengthwise by its width.
        """
        min_x = min_y = float("inf")
        max_x = max_y = float("-inf")

        def grow(x: float, y: float) -> None:
            nonlocal min_x, min_y, max_x, max_y
            min_x, max_x = min(min_x, x), max(max_x, x)
            min_y, max_y = min(min_y, y), max(max_y, y)

        for placement in self.placements:
            hw = placement.piece.width / 2.0
            overhang = placement.piece.end_overhang
            for line in placement.centrelines():
                if len(line) < 2:
                    for x, y, _ in line:
                        grow(x - hw, y - hw)
                        grow(x + hw, y + hw)
                    continue
                n = len(line)
                for i, (x, y, _z) in enumerate(line):
                    ax, ay, _ = line[max(0, i - 1)]
                    bx, by, _ = line[min(n - 1, i + 1)]
                    dx, dy = bx - ax, by - ay
                    norm = math.hypot(dx, dy) or 1.0
                    nx, ny = -dy / norm, dx / norm
                    grow(x + nx * hw, y + ny * hw)
                    grow(x - nx * hw, y - ny * hw)
                    if overhang and i in (0, n - 1):
                        direction = -1.0 if i == 0 else 1.0
                        ox = x + direction * dx / norm * overhang
                        oy = y + direction * dy / norm * overhang
                        grow(ox + nx * hw, oy + ny * hw)
                        grow(ox - nx * hw, oy - ny * hw)
        if min_x > max_x:
            return (0.0, 0.0, 0.0, 0.0)
        return (min_x, min_y, max_x, max_y)

    def size(self) -> tuple[float, float]:
        """Footprint ``(width, height)`` in mm."""
        min_x, min_y, max_x, max_y = self.bounds()
        return (max_x - min_x, max_y - min_y)

    def track_length(self) -> float:
        """Total running length of track, in mm."""
        return sum(p.piece.paths[0].length() for p in self.placements)

    # -- construction ----------------------------------------------------------

    def with_piece(self, piece: PieceType, frame: Pose) -> tuple[Layout, int]:
        """Add a free-standing piece; returns the new layout and its placement index."""
        placements = self.placements + (Placement(piece, frame),)
        return Layout(placements, dict(self.links), self.accessories), len(placements) - 1

    def attach(self, piece: PieceType, entry_port: int, at: End) -> tuple[Layout, int]:
        """Plug *piece* into the open end *at*, entering through *entry_port*.

        Raises:
            ValueError: if *at* is already occupied, or both mating ends carry a body
                overhang (two level-crossing plates cannot share a joint).
        """
        if at in self.links:
            raise ValueError(f"end {at} is already connected to {self.links[at]}")
        if self.is_sealed(at):
            raise ValueError(f"end {at} is a sealed buffer face; nothing can mate there")
        if entry_port in piece.sealed:
            raise ValueError(f"port {entry_port} of {piece.id} is sealed and cannot mate")
        host = self.placements[at[0]].piece
        if host.end_overhang > 0 and piece.end_overhang > 0:
            raise ValueError(
                f"{host.id} and {piece.id} both overhang their connectors; their "
                "plates would overlap, so they cannot join directly"
            )
        # pose_of() already points outward from the existing piece, which is exactly the
        # direction the layout continues in -- what frame_for() wants.
        frame = piece.frame_for(entry_port, self.pose_of(at))
        placements = self.placements + (Placement(piece, frame),)
        new_index = len(placements) - 1
        links = dict(self.links)
        links[at] = (new_index, entry_port)
        links[(new_index, entry_port)] = at
        return Layout(placements, links, self.accessories), new_index

    def remove(self, index: int) -> Layout:
        """Take one placed piece off the floor.

        Its joints open up, its stones come off with it, and later placements shift
        down one index (links and accessories are remapped accordingly).
        """
        if not 0 <= index < len(self.placements):
            raise ValueError(f"no placement {index}")
        placements = self.placements[:index] + self.placements[index + 1 :]

        def remap(i: int) -> int:
            return i - 1 if i > index else i

        links: dict[End, End] = {}
        for (ai, ap), (bi, bp) in self.links.items():
            if ai == index or bi == index:
                continue
            links[(remap(ai), ap)] = (remap(bi), bp)
        accessories = tuple(
            (remap(entry[0]), *entry[1:])
            for entry in self.accessories
            if entry[0] != index
        )
        return Layout(placements, links, accessories)

    def join(self, a: End, b: End, force: bool = False) -> Layout:
        """Record that two existing open ends mate -- the move that closes a loop.

        With ``force`` the geometric check is skipped, recording a *forced* fit: a join
        the designed-in play of real DUPLO connectors can absorb even though the maths
        says the ends do not exactly coincide.

        Raises:
            ValueError: if either end is occupied, or (unless forced) the two do not
                physically meet.
        """
        for end in (a, b):
            if end in self.links:
                raise ValueError(f"end {end} is already connected")
            if self.is_sealed(end):
                raise ValueError(f"end {end} is a sealed buffer face; it cannot mate")
        piece_a = self.placements[a[0]].piece
        piece_b = self.placements[b[0]].piece
        if piece_a.end_overhang > 0 and piece_b.end_overhang > 0:
            raise ValueError(
                f"{piece_a.id} and {piece_b.id} both overhang their connectors; "
                "their plates would overlap, so they cannot join directly"
            )
        pose_a, pose_b = self.pose_of(a), self.pose_of(b)
        if not force and not pose_a.connects_to(pose_b):
            raise ValueError(
                f"ends do not meet: {pose_a!r} vs {pose_b!r} "
                f"(gap {pose_a.distance_to(pose_b):.3f} mm)"
            )
        links = dict(self.links)
        links[a] = b
        links[b] = a
        return Layout(self.placements, links, self.accessories)

    # -- accessories -------------------------------------------------------------

    def with_accessory(
        self, placement: int, accessory_id: str, at_port: int | None = None
    ) -> Layout:
        """Clip an action stone onto a placement.

        ``at_port`` positions the stone at that connector's face instead of
        mid-piece.  A face stone only acts on trains RUNNING INTO that face (a train
        setting off away from it sits past the trigger already) -- which is exactly
        what makes a direction stone at a buffer face a safe reversing terminator.
        """
        if not 0 <= placement < len(self.placements):
            raise ValueError(f"no placement {placement}")
        if at_port is not None and not (
            0 <= at_port < len(self.placements[placement].piece.ports)
        ):
            raise ValueError(f"placement {placement} has no port {at_port}")
        entry = (placement, accessory_id) if at_port is None else (
            placement,
            accessory_id,
            at_port,
        )
        return Layout(
            self.placements,
            dict(self.links),
            self.accessories + (entry,),
        )

    def without_accessory(self, placement: int, accessory_id: str) -> Layout:
        """Remove one matching stone (the last one clipped on), wherever it sits."""
        accessories = list(self.accessories)
        for i in range(len(accessories) - 1, -1, -1):
            if accessories[i][0] == placement and accessories[i][1] == accessory_id:
                accessories.pop(i)
                break
        else:
            raise ValueError(f"no {accessory_id!r} on placement {placement}")
        return Layout(self.placements, dict(self.links), tuple(accessories))

    def stones_on(self, placement: int) -> list[str]:
        return [entry[1] for entry in self.accessories if entry[0] == placement]

    def stone_entries_on(self, placement: int) -> list[tuple[str, int | None]]:
        """``(stone id, port position or None for mid-piece)`` for one placement."""
        return [
            (entry[1], entry[2] if len(entry) > 2 else None)
            for entry in self.accessories
            if entry[0] == placement
        ]

    # -- traversal -------------------------------------------------------------

    def walk(self, start: End | None = None) -> Iterator[tuple[int, int, int]]:
        """Follow the track from *start*, yielding ``(placement, entry, exit)`` triples.

        At a junction the main route is taken.  Stops on reaching an open end or
        returning to where it began.
        """
        if not self.placements:
            return
        if start is None:
            open_ends = self.open_ends()
            start = open_ends[0] if open_ends else (0, 0)
        seen: set[End] = set()
        cursor = start
        while cursor is not None and cursor not in seen:
            seen.add(cursor)
            index, port = cursor
            options = self.placements[index].piece.transit(port)
            if not options:
                return
            exit_port, _route = options[0]
            yield (index, port, exit_port)
            nxt = self.links.get((index, exit_port))
            if nxt is None:
                return
            cursor = nxt

    def gaps(self) -> list[tuple[End, End, float]]:
        """Pairs of open ends that nearly meet, with the gap in mm.

        Useful for reporting near-misses: a layout that is 4 mm from closing is a
        different kind of answer from one that is 400 mm away.
        """
        open_ends = self.open_ends()
        out = []
        for i, a in enumerate(open_ends):
            for b in open_ends[i + 1 :]:
                out.append((a, b, self.pose_of(a).distance_to(self.pose_of(b))))
        out.sort(key=lambda t: t[2])
        return out


# --------------------------------------------------------------------------------------
# Serialisation
# --------------------------------------------------------------------------------------


def layout_to_dict(layout: Layout) -> dict[str, Any]:
    """Serialise a layout, preserving exact geometry.

    Frames are written as their four exact rational coefficients rather than decimals,
    so a saved layout reloads bit-identical and still passes the closure test.
    """
    return {
        "format": "duplotrain-layout/1",
        "placements": [
            {
                "piece": p.piece.id,
                "frame": {
                    "x": _alg_to_json(p.frame.x),
                    "y": _alg_to_json(p.frame.y),
                    "z": _alg_to_json(p.frame.z),
                    "heading": p.frame.heading,
                },
            }
            for p in layout.placements
        ],
        "links": sorted(
            [list(a) + list(b) for a, b in layout.links.items() if a < b]
        ),
        "accessories": [list(entry) for entry in layout.accessories],
    }


def layout_from_dict(data: Mapping[str, Any], pieces: Mapping[str, PieceType]) -> Layout:
    """Rebuild a layout from :func:`layout_to_dict` output."""
    check_layout_json(data)

    placements = []
    for entry in data["placements"]:
        piece_id = entry["piece"]
        if piece_id not in pieces:
            raise ValueError(f"layout uses unknown piece {piece_id!r}")
        frame_spec = entry["frame"]
        frame = Pose(
            _alg_from_json(frame_spec["x"]),
            _alg_from_json(frame_spec["y"]),
            _alg_from_json(frame_spec["z"]),
            int(frame_spec["heading"]),
        )
        placements.append(Placement(pieces[piece_id], frame))

    def check_end(index: int, port: int) -> None:
        if not 0 <= index < len(placements):
            raise ValueError(f"layout refers to placement {index}, which does not exist")
        if not 0 <= port < len(placements[index].piece.ports):
            raise ValueError(f"placement {index} has no port {port}")

    links: dict[End, End] = {}
    for ai, ap, bi, bp in data.get("links", []):
        check_end(ai, ap)
        check_end(bi, bp)
        if ap in placements[ai].piece.sealed or bp in placements[bi].piece.sealed:
            raise ValueError("sealed faces cannot be linked")
        if (ai, ap) in links or (bi, bp) in links or (ai, ap) == (bi, bp):
            raise ValueError(f"end ({ai}, {ap}) or ({bi}, {bp}) is linked twice")
        links[(ai, ap)] = (bi, bp)
        links[(bi, bp)] = (ai, ap)
    accessories = tuple(
        (int(entry[0]), str(entry[1]))
        if len(entry) < 3
        else (int(entry[0]), str(entry[1]), int(entry[2]))
        for entry in data.get("accessories", [])
    )
    for entry in accessories:
        check_end(entry[0], entry[2] if len(entry) > 2 else 0)
    return Layout(tuple(placements), links, accessories)




def build_chain(
    pieces: Iterable[tuple[PieceType, int, int]], start: Pose | None = None
) -> Layout:
    """Build a simple chain from ``(piece, entry_port, exit_port)`` triples.

    Handy in tests and at the REPL: ``build_chain([(curve, 0, 1)] * 12)`` lays twelve
    curves nose to tail.
    """
    from .geometry import ORIGIN

    layout = Layout()
    cursor: End | None = None
    for piece, entry, exit_port in pieces:
        if cursor is None:
            frame = piece.frame_for(entry, start or ORIGIN)
            layout, index = layout.with_piece(piece, frame)
        else:
            layout, index = layout.attach(piece, entry, cursor)
        cursor = (index, exit_port)
    return layout
