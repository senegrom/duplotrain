"""A local track-designer GUI.

``duplotrain gui`` serves a one-page editor on localhost.  Because DUPLO track only
ever attaches on the exact lattice, the editor needs no freeform dragging: every open
end is a clickable arrow, the palette arms a piece variant (curve left, curve right,
switch via its stem, ...), and clicking an arrow snaps the piece on.  The *Close the
loop* button hands the layout to the completion solver, which searches for ways to
join two chosen open ends with the pieces still in the box -- candidates preview as
ghosts and apply with a click.

Implementation notes: standard-library HTTP server, one JSON API, all state
server-side in a single :class:`Session` guarded by a lock (the editor is a local,
single-user tool).  No dependencies beyond the package itself; the front end is one
static HTML file shipped as package data.
"""

from __future__ import annotations

import itertools
import json
import threading
import webbrowser
from dataclasses import dataclass, field
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from importlib import resources
from typing import Any, Mapping

from .catalog import ACCESSORIES, STONE_MOUNTS, default_catalog
from .geometry import steps_to_degrees
from .layout import End, Layout, layout_from_dict, layout_to_dict
from .pieces import PieceType
from .sets import SETS, inventory_for_sets
from .solver import Solution, SolverConfig, _moves_for, solve

__all__ = ["Session", "make_server", "run"]

#: A friendly default box so the editor is playable before anyone edits counts.
DEFAULT_INVENTORY = {
    "straight": 8,
    "curve": 24,
    "switch": 2,
    "crossing": 1,
    "level_crossing": 2,
    "buffer": 2,
    "slope": 2,
    "ramp": 2,
    "span": 2,
}

DEFAULT_STONES = {sid: 1 for sid in ACCESSORIES}

#: Per-piece count reported while the sandbox "infinite pieces" mode is on: big
#: enough to never run out in practice, small enough to keep every sum finite.
UNLIMITED_COUNT = 999


def _signed_degrees(dheading: int) -> int:
    degrees = steps_to_degrees(dheading)
    return degrees - 360 if degrees >= 180 else degrees


@dataclass
class Session:
    """The editor's server-side state: the layout being built, and how it got there."""

    catalog: dict[str, PieceType] = field(default_factory=default_catalog)
    inventory: dict[str, int] = field(default_factory=lambda: dict(DEFAULT_INVENTORY))
    stones: dict[str, int] = field(default_factory=lambda: dict(DEFAULT_STONES))
    #: Sandbox mode: ignore inventory limits entirely -- place anything, and let
    #: the completion solver draw from a bottomless box.  The owned counts are
    #: kept untouched underneath so switching back restores them.
    unlimited: bool = False
    history: list[Layout] = field(default_factory=lambda: [Layout()])
    candidates: list[Solution] = field(default_factory=list)
    lock: threading.Lock = field(default_factory=threading.Lock)

    # -- state ------------------------------------------------------------------

    @property
    def layout(self) -> Layout:
        return self.history[-1]

    def remaining(self) -> dict[str, int]:
        if self.unlimited:
            return {pid: UNLIMITED_COUNT for pid in self.catalog}
        used = self.layout.piece_counts
        return {
            pid: max(0, self.inventory.get(pid, 0) - used.get(pid, 0))
            for pid in self.catalog
        }

    def stones_remaining(self) -> dict[str, int]:
        if self.unlimited:
            return {sid: UNLIMITED_COUNT for sid in ACCESSORIES}
        placed: dict[str, int] = {}
        for _idx, sid in self.layout.accessories:
            placed[sid] = placed.get(sid, 0) + 1
        return {
            sid: max(0, self.stones.get(sid, 0) - placed.get(sid, 0))
            for sid in ACCESSORIES
        }

    def set_unlimited(self, on: bool) -> None:
        self.unlimited = bool(on)

    def _push(self, layout: Layout) -> None:
        self.history.append(layout)
        if len(self.history) > 200:
            del self.history[1:2]
        self.candidates = []

    # -- serialisation for the front end ----------------------------------------

    def _layout_json(self, layout: Layout) -> dict[str, Any]:
        placements = []
        for index, placement in enumerate(layout):
            lines = [
                [[round(x, 2), round(y, 2), round(z, 2)] for x, y, z in line]
                for line in placement.centrelines(spacing=10.0)
            ]
            ports = []
            for port in range(len(placement.piece.ports)):
                pose = placement.port_pose(port)
                x, y = pose.xy()
                ports.append(
                    {
                        "x": round(x, 2),
                        "y": round(y, 2),
                        "deg": pose.degrees,
                        "open": (index, port) not in layout.links,
                        "sealed": port in placement.piece.sealed,
                        "port": port,
                        "name": placement.piece.ports[port].name,
                    }
                )
            main_line = lines[0]
            mid = main_line[len(main_line) // 2]
            placements.append(
                {
                    "piece": placement.piece.id,
                    "name": placement.piece.name,
                    "category": placement.piece.category,
                    "width": placement.piece.width,
                    "lines": lines,
                    "ports": ports,
                    "mid": [mid[0], mid[1]],
                    "stone_ok": placement.piece.id in STONE_MOUNTS,
                    "stones": layout.stones_on(index),
                    "stone_marks": [
                        {"id": sid, "at": pos}
                        for sid, pos in layout.stone_entries_on(index)
                    ],
                }
            )
        width, height = layout.size()
        return {
            "placements": placements,
            "closed": layout.is_closed,
            "size_cm": [round(width / 10, 1), round(height / 10, 1)],
            "piece_counts": layout.piece_counts,
        }

    def state(self) -> dict[str, Any]:
        palette = []
        for pid, piece in self.catalog.items():
            variants = []
            for move in _moves_for(piece):
                entry_name = piece.ports[move.entry].name
                exit_name = piece.ports[move.exit].name
                turn = _signed_degrees(move.dheading)
                if len(piece.ports) == 2 and turn == 0:
                    label = "ahead"
                elif len(piece.ports) == 2:
                    label = "turn left" if turn > 0 else "turn right"
                else:
                    label = f"{entry_name}→{exit_name}"
                variants.append(
                    {"entry": move.entry, "exit": move.exit, "label": label, "turn": turn}
                )
            if not variants:
                # No drivable route (a buffer stop): still placeable by hand through
                # each real connector -- attaching only needs an entry port.
                unsealed = [
                    p for p in range(len(piece.ports)) if p not in piece.sealed
                ]
                for p in unsealed:
                    label = "cap the end" if len(unsealed) == 1 else f"via {piece.ports[p].name}"
                    variants.append({"entry": p, "exit": p, "label": label, "turn": 0})
            palette.append(
                {
                    "id": pid,
                    "name": piece.name,
                    "category": piece.category,
                    "provisional": piece.provisional,
                    "variants": variants,
                }
            )
        mates = []
        opens = self.layout.connectable_ends()
        for i, a in enumerate(opens):
            for b in opens[i + 1 :]:
                if self.layout.pose_of(a).connects_to(self.layout.pose_of(b)):
                    mates.append([list(a), list(b)])
        return {
            "layout": self._layout_json(self.layout),
            "open_ends": [list(end) for end in self.layout.connectable_ends()],
            "matable": mates,
            "inventory": {
                "owned": {pid: self.inventory.get(pid, 0) for pid in self.catalog},
                "remaining": self.remaining(),
                "unlimited": self.unlimited,
            },
            "stones": {
                "catalog": ACCESSORIES,
                "owned": {sid: self.stones.get(sid, 0) for sid in ACCESSORIES},
                "remaining": self.stones_remaining(),
            },
            "sets": [
                {
                    "code": s.code,
                    "name": s.name,
                    "year": s.year,
                    "pieces": dict(s.pieces),
                    "stones": dict(s.stones),
                }
                for s in SETS.values()
            ],
            "palette": palette,
            "can_undo": len(self.history) > 1,
            "candidates": [self._candidate_json(i, s) for i, s in enumerate(self.candidates)],
        }

    def _candidate_json(self, index: int, sol: Solution) -> dict[str, Any]:
        width, height = sol.layout.size()
        added: dict[str, int] = dict(sol.layout.piece_counts)
        for pid, n in self.layout.piece_counts.items():
            added[pid] = added.get(pid, 0) - n
            if added[pid] <= 0:
                del added[pid]
        return {
            "index": index,
            "exact": sol.exact,
            "gap": round(sol.gap, 2),
            "kind": sol.kind,
            "added": added,
            "open_stubs": sol.open_stubs,
            "size_cm": [round(width / 10, 1), round(height / 10, 1)],
            "preview": self._layout_json(sol.layout),
        }

    # -- mutations ---------------------------------------------------------------

    def attach(self, piece_id: str, entry: int, at: End | None) -> None:
        """Attach a new piece at open end *at* (or place the first piece at the origin)."""
        if piece_id not in self.catalog:
            raise ValueError(f"unknown piece {piece_id!r}")
        if self.remaining().get(piece_id, 0) <= 0:
            raise ValueError(f"no {piece_id!r} left in the box (edit the inventory)")
        piece = self.catalog[piece_id]
        if self.layout.placements:
            if at is None:
                raise ValueError("pick an open end to attach to")
            layout, _ = self.layout.attach(piece, entry, at)
        else:
            from .geometry import ORIGIN

            layout, _ = self.layout.with_piece(piece, piece.frame_for(entry, ORIGIN))
        self._push(layout)

    def join(self, a: End, b: End) -> None:
        self._push(self.layout.join(a, b))

    def remove_piece(self, placement: int) -> None:
        self._push(self.layout.remove(placement))

    def undo(self) -> None:
        if len(self.history) > 1:
            self.history.pop()
            self.candidates = []

    def clear(self) -> None:
        self._push(Layout())
        self.history = self.history[-1:]

    def set_inventory(self, counts: Mapping[str, Any]) -> None:
        for pid, n in counts.items():
            if pid in self.catalog:
                self.inventory[pid] = max(0, int(n))
            elif pid in ACCESSORIES:
                self.stones[pid] = max(0, int(n))
            else:
                raise ValueError(f"unknown piece {pid!r}")

    def add_set(self, code: str) -> None:
        """Add one boxed set's pieces and stones to the owned inventory."""
        pieces, stones = inventory_for_sets([code])
        for pid, n in pieces.items():
            self.inventory[pid] = self.inventory.get(pid, 0) + n
        for sid, n in stones.items():
            self.stones[sid] = self.stones.get(sid, 0) + n

    def toggle_stone(
        self, placement: int, stone_id: str, at_port: int | None = None
    ) -> None:
        """Clip a stone onto a placement (mid-piece or at a connector face), or
        unclip it if one of that kind is already there."""
        if stone_id not in ACCESSORIES:
            raise ValueError(f"unknown action stone {stone_id!r}")
        if not 0 <= placement < len(self.layout.placements):
            raise ValueError(f"no placement {placement}")
        if stone_id in self.layout.stones_on(placement):
            self._push(self.layout.without_accessory(placement, stone_id))
            return
        piece = self.layout.placements[placement].piece
        if piece.id not in STONE_MOUNTS:
            raise ValueError(f"action stones clip onto straights, not {piece.id!r}")
        if self.stones_remaining().get(stone_id, 0) <= 0:
            raise ValueError(f"no {stone_id!r} left (edit the inventory)")
        self._push(self.layout.with_accessory(placement, stone_id, at_port=at_port))

    def _arc_closures(self, grow: End, close: End, max_results: int) -> list[Solution]:
        """Instant oracle for ring-shaped closures the DFS chronically misses.

        Tries every ``leveler + j straights + k same-sign curves + m straights +
        leveler`` chain (j, m <= 8, k <= 13), where a leveler is a short run of
        climbing pieces: any one-directional ramp/span sequence of up to four
        pieces, or the full up-and-over bridge.  This closes winding rings the
        search's toward-target ordering starves on -- ten curves looping to a
        neighbouring fork tip -- and their versions through bridges: finish the
        descent from a half-built climb, or a ring that carries a whole bridge.
        Heading and height prefilters keep it to a few thousand exact pose
        checks.
        """
        from .solver import _solution_overlaps

        remaining = self.remaining()
        base = self.layout
        n_base = len(base)
        curve, straight = self.catalog["curve"], self.catalog["straight"]
        ramp, span = self.catalog["ramp"], self.catalog["span"]
        target = base.pose_of(close)
        s_delta = straight.exit_delta(0, 1)
        c_delta = {entry: curve.exit_delta(entry, 1 - entry) for entry in (0, 1)}

        # Leveling units: (sequence of (piece, entry), float dz).  Monotone
        # ramp/span runs of length <= 4 both ways, the empty unit, and the full
        # bridge (which levels out at zero but spans 1024 mm of run).
        units: list[tuple[tuple, float]] = [((), 0.0)]
        for length in (1, 2, 3, 4):
            for combo in itertools.product(("ramp", "span"), repeat=length):
                for entry_side, sign in ((0, 1.0), (1, -1.0)):
                    seq = tuple((pid, entry_side) for pid in combo)
                    dz = sign * sum(57.6 if pid == "ramp" else 19.2 for pid in combo)
                    units.append((seq, dz))
        units.append(
            ((("ramp", 0), ("span", 0), ("span", 1), ("ramp", 1)), 0.0)
        )

        def unit_cost(seq):
            need: dict[str, int] = {}
            for pid, _e in seq:
                need[pid] = need.get(pid, 0) + 1
            return need

        def unit_ok(*seqs):
            need: dict[str, int] = {}
            for seq in seqs:
                for pid, _e in seq:
                    need[pid] = need.get(pid, 0) + 1
            return all(remaining.get(pid, 0) >= n for pid, n in need.items())

        target_dz = float(target.z) - float(base.pose_of(grow).z)
        pairs = [
            (pre, post)
            for pre, dz_pre in units
            for post, dz_post in units
            if abs(dz_pre + dz_post - target_dz) < 1e-6 and unit_ok(pre, post)
        ]
        pairs.sort(key=lambda pp: len(pp[0]) + len(pp[1]))
        pairs = pairs[:60]

        piece_of = {"ramp": ramp, "span": span}

        def apply_unit(pose, seq):
            for pid, entry_side in seq:
                d = piece_of[pid].exit_delta(entry_side, 1 - entry_side)
                pose = pose.then(*d)
            return pose

        def build(pre, j, k, entry, m, post):
            work, cursor = base, grow
            for pid, entry_side in pre:
                work, idx = work.attach(piece_of[pid], entry_side, cursor)
                cursor = (idx, 1 - entry_side)
            for _ in range(j):
                work, idx = work.attach(straight, 0, cursor)
                cursor = (idx, 1)
            for _ in range(k):
                work, idx = work.attach(curve, entry, cursor)
                cursor = (idx, 1 - entry)
            for _ in range(m):
                work, idx = work.attach(straight, 0, cursor)
                cursor = (idx, 1)
            for pid, entry_side in post:
                work, idx = work.attach(piece_of[pid], entry_side, cursor)
                cursor = (idx, 1 - entry_side)
            return work.join(cursor, close)

        start = base.pose_of(grow)
        want_heading = (target.heading + 12) % 24
        found: list[Solution] = []
        seen_pre = {}
        for pre, post in pairs:
            if pre not in seen_pre:
                seen_pre[pre] = apply_unit(start, pre)
            start_pre = seen_pre[pre]
            for entry, turn in ((0, 2), (1, -2)):
                for k in range(0 if (pre or post) else 1, 14):
                    if (start_pre.heading + turn * k) % 24 != want_heading:
                        continue
                    if k > remaining.get("curve", 0):
                        break
                    for j in range(0, 9):
                        pose = start_pre
                        for _ in range(j):
                            pose = pose.then(*s_delta)
                        for _ in range(k):
                            pose = pose.then(*c_delta[entry])
                        for m in range(0, 9):
                            if m:
                                pose = pose.then(*s_delta)
                            if j + m > remaining.get("straight", 0):
                                continue
                            if not pre and not post and not k:
                                continue
                            end_pose = apply_unit(pose, post) if post else pose
                            if not end_pose.connects_to(target):
                                continue
                            try:
                                closed = build(pre, j, k, entry, m, post)
                            except ValueError:
                                continue
                            if _solution_overlaps(closed, n_base, 120.0, 8.0):
                                continue
                            found.append(
                                Solution(
                                    layout=closed,
                                    steps=(),
                                    gap=0.0,
                                    exact=True,
                                    open_stubs=len(closed.connectable_ends()),
                                    signature=("arc", pre, j, k, entry, m, post),
                                )
                            )
                            if len(found) >= max_results:
                                return found
        return found

    def solve_gap(
        self,
        grow: End | None,
        close: End | None,
        slop: float,
        max_results: int,
        reversing: bool = False,
        progress: object = None,
    ) -> dict:
        """Search for completions; returns {found, aborted, searched[, reason]}.

        An instant arc oracle runs first (ring closures the DFS misses), then
        the staged search: plain running track (curves + straights) first --
        that closes almost every real gap within a few thousand nodes -- then
        the whole box only if needed.  A depth-first search over a BROAD
        inventory otherwise drowns exploring exotic-piece subtrees before
        finding the obvious answer.
        """
        opens = self.layout.connectable_ends()
        if grow is None or close is None:
            if len(opens) != 2:
                raise ValueError(
                    "pick the two ends to close (the layout has "
                    f"{len(opens)} open ends)"
                )
            grow, close = opens[1], opens[0]

        remaining = self.remaining()

        # Height sanity: if the two ends differ in elevation by more than every
        # climbing piece left in the box can supply, no search can help.
        dz = abs(float(self.layout.pose_of(grow).z) - float(self.layout.pose_of(close).z))
        if dz > 1e-9:
            lift = (
                57.6 * remaining.get("ramp", 0)
                + 19.2 * remaining.get("span", 0)
                + 5.6 * remaining.get("slope", 0)
            )
            if dz > lift + 1e-6:
                self.candidates = []
                return {
                    "found": 0,
                    "aborted": False,
                    "searched": 0,
                    "reason": (
                        f"impossible: those ends differ by {dz:.0f} mm in height "
                        f"and the remaining pieces can climb at most {lift:.0f} mm "
                        "— the track up there can never come back down"
                    ),
                }

        if not reversing:
            arcs = self._arc_closures(grow, close, max_results)
            if arcs:
                self.candidates = arcs
                return {"found": len(arcs), "aborted": False, "searched": 0}
        plain = {
            pid: n
            for pid, n in remaining.items()
            if pid in ("curve", "straight") and n > 0
        }
        full = {pid: n for pid, n in remaining.items() if n > 0}
        stages = [plain, full] if plain and plain != full else [full]

        searched = 0
        aborted = False
        self.candidates = []
        for stage_index, inventory in enumerate(stages):
            budget = 25_000 if stage_index == 0 and len(stages) > 1 else 60_000
            result = solve(
                inventory,
                self.catalog,
                SolverConfig(
                    slop=slop,
                    min_pieces=1,
                    max_pieces=26,
                    max_results=max_results,
                    max_nodes=budget,
                    reversing_loops=reversing,
                    progress=progress,
                ),
                base=self.layout,
                grow_from=grow,
                close_onto=close,
            )
            searched += result.stats.nodes
            aborted = result.stats.aborted
            if result.solutions:
                self.candidates = result.solutions[:max_results]
                break
        return {
            "found": len(self.candidates),
            "aborted": aborted and not self.candidates,
            "searched": searched,
        }

    def apply_candidate(self, index: int) -> None:
        if not 0 <= index < len(self.candidates):
            raise ValueError("no such candidate (solve again)")
        chosen = self.candidates[index].layout
        self._push(chosen)


# --------------------------------------------------------------------------------------
# HTTP plumbing
# --------------------------------------------------------------------------------------


def _handler_for(session: Session) -> type[BaseHTTPRequestHandler]:
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, fmt: str, *args: Any) -> None:  # quiet
            pass

        def _send(self, status: int, payload: bytes, content_type: str) -> None:
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(payload)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(payload)

        def _json(self, status: int, data: Any) -> None:
            self._send(status, json.dumps(data).encode("utf-8"), "application/json")

        def _body(self) -> dict[str, Any]:
            length = int(self.headers.get("Content-Length") or 0)
            if not length:
                return {}
            return json.loads(self.rfile.read(length).decode("utf-8"))

        def do_GET(self) -> None:  # noqa: N802 (http.server API)
            if self.path in ("/", "/index.html"):
                html = resources.files("duplotrain").joinpath("static/editor.html")
                self._send(200, html.read_bytes(), "text/html; charset=utf-8")
            elif self.path == "/api/state":
                with session.lock:
                    self._json(200, session.state())
            elif self.path == "/api/export":
                with session.lock:
                    self._json(200, layout_to_dict(session.layout))
            else:
                self._json(404, {"error": f"no route {self.path}"})

        def do_POST(self) -> None:  # noqa: N802
            try:
                body = self._body()
                with session.lock:
                    self._dispatch(body)
            except (ValueError, KeyError, TypeError) as exc:
                self._json(409, {"error": str(exc)})

        def _dispatch(self, body: dict[str, Any]) -> None:
            path = self.path
            if path == "/api/attach":
                at = tuple(body["at"]) if body.get("at") is not None else None
                session.attach(body["piece"], int(body["entry"]), at)
            elif path == "/api/join":
                session.join(tuple(body["a"]), tuple(body["b"]))
            elif path == "/api/undo":
                session.undo()
            elif path == "/api/remove":
                session.remove_piece(int(body["placement"]))
            elif path == "/api/clear":
                session.clear()
            elif path == "/api/inventory":
                session.set_inventory(body.get("counts", {}))
            elif path == "/api/unlimited":
                session.set_unlimited(bool(body.get("on")))
            elif path == "/api/add_set":
                session.add_set(str(body["code"]))
            elif path == "/api/stone":
                session.toggle_stone(
                    int(body["placement"]),
                    str(body["id"]),
                    int(body["at_port"]) if body.get("at_port") is not None else None,
                )
            elif path == "/api/solve":
                outcome = session.solve_gap(
                    tuple(body["grow"]) if body.get("grow") else None,
                    tuple(body["close"]) if body.get("close") else None,
                    float(body.get("slop", 0.0)),
                    int(body.get("max_results", 10)),
                    reversing=bool(body.get("reversing", False)),
                )
                self._json(200, {**outcome, **session.state()})
                return
            elif path == "/api/apply":
                session.apply_candidate(int(body["index"]))
            elif path == "/api/import":
                layout = layout_from_dict(body["data"], session.catalog)
                session._push(layout)
            else:
                self._json(404, {"error": f"no route {path}"})
                return
            self._json(200, session.state())

    return Handler


def make_server(session: Session, port: int = 8137) -> ThreadingHTTPServer:
    """Build (but do not start) the editor server; port 0 picks a free port."""
    return ThreadingHTTPServer(("127.0.0.1", port), _handler_for(session))


def run(port: int = 8137, open_browser: bool = True) -> None:
    """Serve the editor until interrupted."""
    session = Session()
    server = make_server(session, port)
    url = f"http://127.0.0.1:{server.server_port}/"
    print(f"duplotrain editor at {url}  (Ctrl+C to stop)")
    if open_browser:
        webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
