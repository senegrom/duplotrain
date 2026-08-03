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


def _signed_degrees(dheading: int) -> int:
    degrees = steps_to_degrees(dheading)
    return degrees - 360 if degrees >= 180 else degrees


@dataclass
class Session:
    """The editor's server-side state: the layout being built, and how it got there."""

    catalog: dict[str, PieceType] = field(default_factory=default_catalog)
    inventory: dict[str, int] = field(default_factory=lambda: dict(DEFAULT_INVENTORY))
    stones: dict[str, int] = field(default_factory=lambda: dict(DEFAULT_STONES))
    history: list[Layout] = field(default_factory=lambda: [Layout()])
    candidates: list[Solution] = field(default_factory=list)
    lock: threading.Lock = field(default_factory=threading.Lock)

    # -- state ------------------------------------------------------------------

    @property
    def layout(self) -> Layout:
        return self.history[-1]

    def remaining(self) -> dict[str, int]:
        used = self.layout.piece_counts
        return {
            pid: max(0, self.inventory.get(pid, 0) - used.get(pid, 0))
            for pid in self.catalog
        }

    def stones_remaining(self) -> dict[str, int]:
        placed: dict[str, int] = {}
        for _idx, sid in self.layout.accessories:
            placed[sid] = placed.get(sid, 0) + 1
        return {
            sid: max(0, self.stones.get(sid, 0) - placed.get(sid, 0))
            for sid in ACCESSORIES
        }

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

    def solve_gap(
        self,
        grow: End | None,
        close: End | None,
        slop: float,
        max_results: int,
        reversing: bool = False,
    ) -> int:
        opens = self.layout.connectable_ends()
        if grow is None or close is None:
            if len(opens) != 2:
                raise ValueError(
                    "pick the two ends to close (the layout has "
                    f"{len(opens)} open ends)"
                )
            grow, close = opens[1], opens[0]
        result = solve(
            self.remaining(),
            self.catalog,
            SolverConfig(
                slop=slop,
                min_pieces=1,
                max_results=max_results,
                # Modest budget: the editor must feel interactive, and under the web
                # build this runs in WebAssembly at a fraction of native speed.
                max_nodes=150_000,
                reversing_loops=reversing,
            ),
            base=self.layout,
            grow_from=grow,
            close_onto=close,
        )
        self.candidates = result.solutions[:max_results]
        return len(self.candidates)

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
            elif path == "/api/add_set":
                session.add_set(str(body["code"]))
            elif path == "/api/stone":
                session.toggle_stone(
                    int(body["placement"]),
                    str(body["id"]),
                    int(body["at_port"]) if body.get("at_port") is not None else None,
                )
            elif path == "/api/solve":
                found = session.solve_gap(
                    tuple(body["grow"]) if body.get("grow") else None,
                    tuple(body["close"]) if body.get("close") else None,
                    float(body.get("slop", 0.0)),
                    int(body.get("max_results", 10)),
                    reversing=bool(body.get("reversing", False)),
                )
                self._json(200, {"found": found, **session.state()})
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
