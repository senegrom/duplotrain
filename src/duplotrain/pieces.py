"""Track piece definitions.

A piece is described by the *paths a train can take through it*, not by its outline.
Each path is a chain of primitive segments -- a straight run, a circular arc, or a
ramp -- laid out in the piece's own local frame.  Everything else is derived:

* **Ports** are the endpoints of those paths.  Endpoints that land on the same point
  facing the same way are merged, which is what turns two paths sharing a stem into a
  three-port switch.
* **Routes** are the port pairs a train can actually run between.
* **Centrelines** are sampled from the segments for collision checking and drawing.

The payoff is that a new piece is a few lines of JSON.  Describe where its paths go and
the rest of the program -- solver, collision, renderer -- picks it up with no changes.

Lengths and radii are exact :class:`~duplotrain.exact.Alg` values rather than plain
decimals.  That matters more than it looks: if a straight piece happens to be exactly as
long as the chord of a curve (a natural way to design a toy track system), that length is
irrational, and rounding it to a decimal would make genuinely closed loops fail the
closure test.  Writing it as an exact field element keeps the test honest.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Iterable, Literal, Sequence

from .exact import Alg, alg
from .geometry import HEADING_STEPS, Pose, cos_sin, degrees_to_steps

__all__ = [
    "Segment",
    "Straight",
    "Arc",
    "Ramp",
    "Path",
    "Port",
    "Route",
    "PieceType",
    "parse_length",
    "parse_piece",
    "parse_pieces",
]


def parse_length(value: Any) -> Alg:
    """Parse a catalogue length into an exact field element.

    Accepts:

    * a plain number -- ``152.5`` becomes ``305/2`` exactly (parsed via ``str``, so no
      binary-float noise creeps in);
    * ``{"alg": [a, b, c, d]}`` -- the value ``a + b*sqrt2 + c*sqrt3 + d*sqrt6``;
    * ``{"chord": {"radius": R, "degrees": D}}`` -- the straight-line distance between
      the ends of that arc, i.e. ``2 R sin(D/2)``.  Use this when a straight piece is
      built to match a curve's end-to-end span.
    """
    if isinstance(value, Alg):
        return value
    if isinstance(value, (int, Fraction)):
        return alg(Fraction(value))
    if isinstance(value, float):
        return alg(Fraction(str(value)))
    if isinstance(value, str):
        return alg(Fraction(value))
    if isinstance(value, dict):
        if "alg" in value:
            a, b, c, d = (Fraction(str(x)) for x in value["alg"])
            return Alg(a, b, c, d)
        if "chord" in value:
            spec = value["chord"]
            radius = parse_length(spec["radius"])
            half = degrees_to_steps(Fraction(str(spec["degrees"])) / 2)
            _, sin_half = cos_sin(half)
            return radius * sin_half * 2
        raise ValueError(f"unrecognised length expression {value!r}")
    raise TypeError(f"cannot read a length from {value!r}")


# --------------------------------------------------------------------------------------
# Primitive segments
# --------------------------------------------------------------------------------------


class Segment:
    """One primitive stretch of track, expressed in the frame where it starts."""

    #: Change in heading across the segment, in lattice steps.
    turn_steps: int = 0

    def delta(self) -> tuple[Alg, Alg, Alg]:
        """Displacement ``(dx, dy, dz)`` from segment start to segment end."""
        raise NotImplementedError

    def length(self) -> float:
        """Arc length along the centreline, in millimetres."""
        raise NotImplementedError

    def sample(self, spacing: float) -> list[tuple[float, float, float, float]]:
        """Points along the centreline as ``(x, y, z, heading_rad)``, in the segment's
        own start frame, at roughly *spacing* mm apart.

        The start point is excluded -- callers chain segments and already hold it.
        """
        raise NotImplementedError


@dataclass(frozen=True, slots=True)
class Straight(Segment):
    """A straight run of the given length."""

    run: Alg

    turn_steps = 0

    def delta(self) -> tuple[Alg, Alg, Alg]:
        return (self.run, alg(0), alg(0))

    def length(self) -> float:
        return abs(float(self.run))

    def sample(self, spacing: float) -> list[tuple[float, float, float, float]]:
        run = float(self.run)
        n = max(1, math.ceil(abs(run) / spacing))
        return [(run * i / n, 0.0, 0.0, 0.0) for i in range(1, n + 1)]


@dataclass(frozen=True, slots=True)
class Arc(Segment):
    """A circular arc of the given centreline radius.

    ``degrees`` is positive for a left turn and negative for a right turn.  Because a
    DUPLO connector is genderless, one physical curve serves as both -- the solver just
    enters it from the other end -- so a catalogue entry only needs one handedness.
    """

    radius: Alg
    degrees: int

    turn_steps: int = field(default=0, init=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "turn_steps", degrees_to_steps(self.degrees))

    def delta(self) -> tuple[Alg, Alg, Alg]:
        # Entering at the origin heading +x, an arc turning left by theta ends at
        # (R sin theta, R (1 - cos theta)); a right turn mirrors the lateral term.
        # Note x uses |theta| -- an arc always advances forward, whichever way it bends.
        c, s = cos_sin(degrees_to_steps(abs(self.degrees)))
        forward = self.radius * s
        lateral = self.radius * (alg(1) - c)
        if self.degrees < 0:
            lateral = -lateral
        return (forward, lateral, alg(0))

    def length(self) -> float:
        return abs(float(self.radius) * math.radians(self.degrees))

    def sample(self, spacing: float) -> list[tuple[float, float, float, float]]:
        n = max(2, math.ceil(self.length() / spacing))
        r = float(self.radius)
        theta = math.radians(self.degrees)
        sign = 1.0 if theta >= 0 else -1.0
        out = []
        for i in range(1, n + 1):
            t = abs(theta) * i / n
            out.append((r * math.sin(t), sign * r * (1.0 - math.cos(t)), 0.0, sign * t))
        return out


@dataclass(frozen=True, slots=True)
class Ramp(Segment):
    """A straight run that also changes height.

    The plan-view footprint is the horizontal *run*; ``rise`` is the height gained.  Loop
    closure cares about the run, and about the rises summing to zero around the loop --
    which is exactly how this is modelled.
    """

    run: Alg
    rise: Alg

    turn_steps = 0

    def delta(self) -> tuple[Alg, Alg, Alg]:
        return (self.run, alg(0), self.rise)

    def length(self) -> float:
        return math.hypot(float(self.run), float(self.rise))

    def sample(self, spacing: float) -> list[tuple[float, float, float, float]]:
        run, rise = float(self.run), float(self.rise)
        n = max(1, math.ceil(max(abs(run), 1e-9) / spacing))
        return [(run * i / n, 0.0, rise * i / n, 0.0) for i in range(1, n + 1)]


# --------------------------------------------------------------------------------------
# Paths, ports and routes
# --------------------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Path:
    """A route through a piece: a starting pose plus a chain of segments."""

    start: Pose
    segments: tuple[Segment, ...]

    def end(self) -> Pose:
        """Pose at the far end of the path, in the piece's local frame."""
        pose = self.start
        for seg in self.segments:
            dx, dy, dz = seg.delta()
            pose = pose.then(dx, dy, dz, seg.turn_steps)
        return pose

    def length(self) -> float:
        return sum(seg.length() for seg in self.segments)

    def sample(self, spacing: float = 8.0) -> list[tuple[float, float, float]]:
        """Centreline points ``(x, y, z)`` in the piece's local frame, both ends included.

        Runs in floating point: these points feed collision checks and drawing, where
        sub-micron exactness buys nothing and speed matters.
        """
        x, y, z = self.start.xyz()
        theta = math.radians(self.start.degrees)
        pts: list[tuple[float, float, float]] = [(x, y, z)]
        for seg in self.segments:
            cos_t, sin_t = math.cos(theta), math.sin(theta)
            for lx, ly, lz, _ in seg.sample(spacing):
                pts.append((x + cos_t * lx - sin_t * ly, y + sin_t * lx + cos_t * ly, z + lz))
            dx, dy, dz = seg.delta()
            fdx, fdy, fdz = float(dx), float(dy), float(dz)
            x, y = x + cos_t * fdx - sin_t * fdy, y + sin_t * fdx + cos_t * fdy
            z += fdz
            theta += math.radians(seg.turn_steps * (360 / HEADING_STEPS))
        return pts


@dataclass(frozen=True, slots=True)
class Port:
    """A connector on the edge of a piece.

    ``pose`` sits at the connector face and its heading points *outward*, away from the
    piece.  Two pieces mate when one port's pose faces exactly opposite the other's.
    """

    name: str
    pose: Pose


@dataclass(frozen=True, slots=True)
class Route:
    """A pair of ports a train can travel between, and the path that joins them."""

    port_a: int
    port_b: int
    path_index: int
    kind: Literal["main", "branch"] = "main"


@dataclass(frozen=True, slots=True)
class PieceType:
    """A kind of track piece: its paths, derived ports and routes, and metadata."""

    id: str
    name: str
    category: str
    paths: tuple[Path, ...]
    ports: tuple[Port, ...]
    routes: tuple[Route, ...]
    width: float = 40.0
    #: Solid body extending past each connector plane, mm -- beyond the standard
    #: interlock tab.  Two overhanging ends cannot legally mate (their bodies would
    #: claim the same strip of floor), which is how the level crossing's road plate
    #: forbids a second level crossing directly in series.
    end_overhang: float = 0.0
    part_numbers: tuple[str, ...] = ()
    notes: str = ""
    provisional: bool = False

    @property
    def is_junction(self) -> bool:
        """True when the piece offers a choice of route (a switch or a crossing)."""
        return len(self.ports) > 2

    def transit(self, entry_port: int) -> list[tuple[int, Route]]:
        """Ports reachable by entering at *entry_port*, with the route taken."""
        out = []
        for route in self.routes:
            if route.port_a == entry_port:
                out.append((route.port_b, route))
            elif route.port_b == entry_port:
                out.append((route.port_a, route))
        return out

    def frame_for(self, entry_port: int, at_end: Pose) -> Pose:
        """World pose of the piece's local origin when *entry_port* mates with *at_end*.

        *at_end* is an open track end whose heading is the direction the layout wants to
        continue in.  The entry port must land on that point facing back the other way,
        since a connector's heading points outward.
        """
        port = self.ports[entry_port].pose
        rotation = (at_end.heading + HEADING_STEPS // 2 - port.heading) % HEADING_STEPS
        c, s = cos_sin(rotation)
        return Pose(
            at_end.x - (c * port.x - s * port.y),
            at_end.y - (s * port.x + c * port.y),
            at_end.z - port.z,
            rotation,
        )

    def exit_delta(self, entry_port: int, exit_port: int) -> tuple[Alg, Alg, Alg, int]:
        """Displacement from the entry connection to the exit connection.

        Expressed in the frame of the open end being built onto, so the solver advances
        with a single :meth:`~duplotrain.geometry.Pose.then` call and never builds a
        transform.  The heading returned is the direction the layout carries on in.
        """
        entry = self.ports[entry_port].pose
        exit_ = self.ports[exit_port].pose
        # Rotate the piece so the entry port faces along -x, then read off the exit.
        rotation = (HEADING_STEPS // 2 - entry.heading) % HEADING_STEPS
        c, s = cos_sin(rotation)
        dx, dy = exit_.x - entry.x, exit_.y - entry.y
        return (
            c * dx - s * dy,
            s * dx + c * dy,
            exit_.z - entry.z,
            (exit_.heading + rotation) % HEADING_STEPS,
        )

    def centreline(self, route: Route, spacing: float = 8.0) -> list[tuple[float, float, float]]:
        """Sampled centreline of one route, in the piece's local frame."""
        return self.paths[route.path_index].sample(spacing)

    def all_centrelines(self, spacing: float = 8.0) -> list[list[tuple[float, float, float]]]:
        return [p.sample(spacing) for p in self.paths]

    def span(self) -> float:
        """Longest path length through the piece, in mm."""
        return max((p.length() for p in self.paths), default=0.0)


# --------------------------------------------------------------------------------------
# Parsing
# --------------------------------------------------------------------------------------


def _parse_segment(spec: dict[str, Any]) -> Segment:
    kind = spec.get("type")
    if kind == "straight":
        return Straight(run=parse_length(spec["run"]))
    if kind == "arc":
        return Arc(radius=parse_length(spec["radius"]), degrees=int(spec["degrees"]))
    if kind == "ramp":
        return Ramp(run=parse_length(spec["run"]), rise=parse_length(spec["rise"]))
    raise ValueError(f"unknown segment type {kind!r}")


def _parse_path(spec: dict[str, Any]) -> Path:
    start_spec = spec.get("start", {})
    start = Pose(
        parse_length(start_spec.get("x", 0)),
        parse_length(start_spec.get("y", 0)),
        parse_length(start_spec.get("z", 0)),
        degrees_to_steps(start_spec.get("heading_deg", 0)),
    )
    segments = tuple(_parse_segment(s) for s in spec["segments"])
    if not segments:
        raise ValueError("a path needs at least one segment")
    return Path(start=start, segments=segments)


def _derive_ports_and_routes(
    paths: Sequence[Path], names: Sequence[str] | None
) -> tuple[tuple[Port, ...], tuple[Route, ...]]:
    """Collect path endpoints into a deduplicated port list plus the routes joining them.

    A path's *start* faces backwards out of the piece (a train arrives against it) while
    its *end* faces forwards, so the two are recorded with opposite headings.  Merging
    coincident endpoints is what makes two paths sharing a stem come out as a three-port
    switch rather than four separate connectors.
    """
    ports: list[Port] = []
    index: dict[tuple[Alg, Alg, Alg, int], int] = {}

    def port_for(pose: Pose) -> int:
        key = (pose.x, pose.y, pose.z, pose.heading)
        if key not in index:
            index[key] = len(ports)
            ports.append(Port(name=f"p{len(ports)}", pose=pose))
        return index[key]

    routes: list[Route] = []
    for i, path in enumerate(paths):
        a = port_for(path.start.reversed())
        b = port_for(path.end())
        if a == b:
            raise ValueError("a path must start and end at different ports")
        routes.append(
            Route(port_a=a, port_b=b, path_index=i, kind="main" if i == 0 else "branch")
        )

    if names:
        if len(names) != len(ports):
            raise ValueError(
                f"piece declares {len(names)} port names but has {len(ports)} ports"
            )
        ports = [Port(name=n, pose=p.pose) for n, p in zip(names, ports)]
    return tuple(ports), tuple(routes)


def parse_piece(spec: dict[str, Any]) -> PieceType:
    """Build a :class:`PieceType` from its JSON/dict description."""
    piece_id = spec.get("id", "?")
    try:
        paths = tuple(_parse_path(p) for p in spec["paths"])
    except KeyError as exc:
        raise ValueError(f"piece {piece_id!r} is missing {exc}") from exc
    if not paths:
        raise ValueError(f"piece {piece_id!r} has no paths")

    ports, routes = _derive_ports_and_routes(paths, spec.get("port_names"))
    if len(ports) < 2:
        raise ValueError(
            f"piece {piece_id!r} collapsed to {len(ports)} port(s); its paths must have "
            "distinct endpoints"
        )

    return PieceType(
        id=spec["id"],
        name=spec.get("name", spec["id"]),
        category=spec.get("category", "track"),
        paths=paths,
        ports=ports,
        routes=routes,
        width=float(spec.get("width", 40.0)),
        end_overhang=float(spec.get("end_overhang", 0.0)),
        part_numbers=tuple(spec.get("part_numbers", ())),
        notes=spec.get("notes", ""),
        provisional=bool(spec.get("provisional", False)),
    )


def parse_pieces(specs: Iterable[dict[str, Any]]) -> dict[str, PieceType]:
    """Parse many piece specs into an id-keyed mapping."""
    pieces: dict[str, PieceType] = {}
    for spec in specs:
        piece = parse_piece(spec)
        if piece.id in pieces:
            raise ValueError(f"duplicate piece id {piece.id!r}")
        pieces[piece.id] = piece
    return pieces
