from pathlib import Path
R = Path('.')
def edit(path, old, new):
    p = R / path
    s = p.read_text()
    assert old in s, (path, old[:60])
    p.write_text(s.replace(old, new, 1))
edit('src/duplotrain/layout.py', 'from fractions import Fraction\n', '')
edit('src/duplotrain/layout.py', 'from .pieces import PieceType\n', 'from .pieces import PieceType\nfrom .validation import check_layout_json, rational_coefficient\n')
edit('src/duplotrain/layout.py', 'a, b, c, d = (Fraction(s) for s in data)', 'a, b, c, d = (rational_coefficient(s) for s in data)')
edit('src/duplotrain/layout.py', '    fmt = data.get("format", "")\n    if not str(fmt).startswith("duplotrain-layout/"):\n        raise ValueError(f"unrecognised layout format {fmt!r}")\n', '    check_layout_json(data)\n')
edit('src/duplotrain/layout.py', '        check_end(bi, bp)\n        if (ai, ap)', '        check_end(bi, bp)\n        if ap in placements[ai].piece.sealed or bp in placements[bi].piece.sealed:\n            raise ValueError("sealed faces cannot be linked")\n        if (ai, ap)')
edit('src/duplotrain/solver.py', '    engine: str = "auto"\n', '''    engine: str = "auto"

    def __post_init__(self) -> None:
        for name in ("slop", "clearance", "collision_spacing"):
            value = getattr(self, name)
            if not math.isfinite(value) or value < 0:
                raise ValueError(f"{name} must be finite and non-negative")
        if self.collision_spacing == 0:
            raise ValueError("collision_spacing must be positive")
        for name, minimum in (("min_pieces", 0), ("max_results", 1), ("max_nodes", 1)):
            value = getattr(self, name)
            if type(value) is not int or value < minimum:
                raise ValueError(f"{name} must be an integer >= {minimum}")
        if self.max_pieces is not None and (
            type(self.max_pieces) is not int or self.max_pieces < 1
        ):
            raise ValueError("max_pieces must be a positive integer or None")
''')
edit('src/duplotrain/solver.py', '    dropped_overlap: int = 0\n', '''    dropped_overlap: int = 0
    #: True only after exhausting the entire inventory, not a capped search.
    complete: bool = False
    stop_reason: str = "not_started"
    max_pieces_searched: int = 0
''')
edit('src/duplotrain/solver.py', '    for piece_id in inventory:\n        if piece_id not in pieces:\n            raise ValueError(f"inventory names unknown piece {piece_id!r}")\n', '''    for piece_id, count in inventory.items():
        if piece_id not in pieces:
            raise ValueError(f"inventory names unknown piece {piece_id!r}")
        if type(count) is not int or count < 0:
            raise ValueError(f"inventory count for {piece_id!r} must be a non-negative integer")
''')
edit('src/duplotrain/solver.py', '        opens = base.open_ends()', '        opens = base.connectable_ends()')
edit('src/duplotrain/solver.py', '        f_limit = depth_limit\n        dfs(', '        f_limit = depth_limit\n        stats.max_pieces_searched = f_limit\n        dfs(')
edit('src/duplotrain/solver.py', '        for f_limit in range(1, depth_limit + 1):  # noqa: B007 (read inside dfs)\n            if not dfs(', '        for f_limit in range(1, depth_limit + 1):\n            stats.max_pieces_searched = f_limit\n            if not dfs(')
edit('src/duplotrain/solver.py', '    stats.duration_s = time.perf_counter() - started\n', '''    if stats.aborted:
        stats.stop_reason = "node_limit"
    elif len(solutions) >= cfg.max_results:
        stats.stop_reason = "result_limit"
    elif depth_limit < total_pieces:
        stats.stop_reason = "piece_limit"
    else:
        stats.complete = True
        stats.stop_reason = "exhausted"
    stats.duration_s = time.perf_counter() - started
''')
p = R / 'src/duplotrain/gui.py'
s = p.read_text()
s = s.replace('import json\n', 'import json\nimport math\n', 1)
s = s.replace('from .solver import Solution, SolverConfig, _moves_for, solve\n', 'from .solver import Solution, SolverConfig, _moves_for, solve\nfrom .validation import MAX_JSON_BYTES, check_layout_json as check_layout_json\n')
a = s.index('def check_layout_json(')
b = s.index('def _signed_degrees', a)
s = s[:a] + '''MAX_INVENTORY_COUNT = 10_000


def _count(value: object) -> int:
    """Parse an inventory count without silently truncating fractional values."""
    if isinstance(value, str) and value.isascii() and value.isdigit() and len(value) <= 5:
        value = int(value)
    if type(value) is not int or not 0 <= value <= MAX_INVENTORY_COUNT:
        raise ValueError(f"counts must be whole numbers from 0 to {MAX_INVENTORY_COUNT}")
    return value


''' + s[b:]
s = s.replace('    lock: threading.Lock = field(default_factory=threading.Lock)\n', '''    lock: threading.Lock = field(default_factory=threading.Lock)
    revision: int = 0
    _candidate_revision: int | None = None
''')
s = s.replace('    def set_unlimited(self, on: bool) -> None:\n        self.unlimited = bool(on)\n', '''    def _invalidate(self) -> None:
        self.revision += 1
        self.candidates = []
        self._candidate_revision = None

    def set_unlimited(self, on: bool) -> None:
        if type(on) is not bool:
            raise ValueError("unlimited must be a boolean")
        if self.unlimited != on:
            self.unlimited = on
            self._invalidate()
''')
s = s.replace('        self.candidates = []\n\n    # -- serialisation', '        self._invalidate()\n\n    # -- serialisation', 1)
s = s.replace('    def state(self) -> dict[str, Any]:\n', '''    def snapshot(self) -> dict[str, Any]:
        """Exact geometry and owned counts; suitable for browser-local recovery."""
        return {
            "format": "duplotrain-session/1",
            "layout": layout_to_dict(self.layout),
            "inventory": dict(self.inventory),
            "stones": dict(self.stones),
            "unlimited": self.unlimited,
        }

    def restore(self, data: object) -> None:
        """Restore a validated checkpoint atomically. Never partially mutate on error."""
        if not isinstance(data, dict) or data.get("format") != "duplotrain-session/1":
            raise ValueError("unrecognised session format")
        inventory = self._validated_counts(data.get("inventory"), self.catalog)
        stones = self._validated_counts(data.get("stones"), ACCESSORIES)
        unlimited = data.get("unlimited")
        if type(unlimited) is not bool:
            raise ValueError("unlimited must be a boolean")
        layout = layout_from_dict(data.get("layout"), self.catalog)
        self.inventory, self.stones, self.unlimited = inventory, stones, unlimited
        self._push(layout)

    @staticmethod
    def _validated_counts(counts: object, known: Mapping) -> dict[str, int]:
        if not isinstance(counts, dict):
            raise ValueError("counts must be a JSON object")
        out = {}
        for pid, count in counts.items():
            if pid not in known:
                raise ValueError(f"unknown piece {pid!r}")
            out[pid] = _count(count)
        return out

    def state(self) -> dict[str, Any]:
''', 1)
s = s.replace('            "can_undo": len(self.history) > 1,', '''            "can_undo": len(self.history) > 1,
            "revision": self.revision,
            "snapshot": self.snapshot(),''', 1)
s = s.replace('            "index": index,\n            "exact": sol.exact,', '            "index": index,\n            "revision": self._candidate_revision,\n            "exact": sol.exact,', 1)
s = s.replace('        piece = self.catalog[piece_id]\n        if self.layout.placements:', '''        piece = self.catalog[piece_id]
        if type(entry) is not int or not 0 <= entry < len(piece.ports) or entry in piece.sealed:
            raise ValueError("pick a valid, unsealed entry port")
        if at is not None and at not in self.layout.connectable_ends():
            raise ValueError("pick an open, unsealed end to attach to")
        if self.layout.placements:''', 1)
s = s.replace('    def join(self, a: End, b: End) -> None:\n        self._push', '    def join(self, a: End, b: End) -> None:\n        opens = self.layout.connectable_ends()\n        if a == b or a not in opens or b not in opens:\n            raise ValueError("pick two distinct open ends to join")\n        self._push', 1)
s = s.replace('            self.candidates = []\n\n    def clear', '            self._invalidate()\n\n    def clear', 1)
s = s.replace('        self.history = self.history[-1:]\n', '', 1)
a = s.index('    def set_inventory(')
b = s.index('    def toggle_stone(', a)
s = s[:a] + '''    def set_inventory(self, counts: Mapping[str, Any]) -> None:
        validated = self._validated_counts(counts, {**self.catalog, **ACCESSORIES})
        inventory, stones = dict(self.inventory), dict(self.stones)
        for pid, n in validated.items():
            (inventory if pid in self.catalog else stones)[pid] = n
        if inventory != self.inventory or stones != self.stones:
            self.inventory, self.stones = inventory, stones
            self._invalidate()

    def add_set(self, code: str) -> None:
        """Add one boxed set, applying the same atomic count checks as manual edits."""
        pieces, stones = inventory_for_sets([code])
        self.set_inventory({
            **{pid: self.inventory.get(pid, 0) + n for pid, n in pieces.items()},
            **{sid: self.stones.get(sid, 0) + n for sid, n in stones.items()},
        })

''' + s[b:]
s = s.replace('def _arc_closures(self, grow: End, close: End, max_results: int) -> list[Solution]:', '''def _arc_closures(
        self, grow: End, close: End, max_results: int, max_pieces: int = 26
    ) -> list[Solution]:''')
s = s.replace('        remaining = self.remaining()\n        base = self.layout', '''        if not all(pid in self.catalog for pid in ("curve", "straight", "ramp", "span")):
            return []
        remaining = self.remaining()
        base = self.layout''', 1)
s = s.replace('                    dz = sign * sum(57.6 if pid == "ramp" else 19.2 for pid in combo)', '''                    dz = sum(float(self.catalog[pid].exit_delta(entry_side, 1 - entry_side)[2])
                             for pid in combo)''', 1)
s = s.replace('for entry_side, sign in ((0, 1.0), (1, -1.0)):', 'for entry_side in (0, 1):', 1)
s = s.replace('                            if j + m > remaining.get("straight", 0):', '''                            if len(pre) + len(post) + j + k + m > max_pieces:
                                continue
                            if j + m > remaining.get("straight", 0):''', 1)
s = s.replace('        progress: object = None,\n    ) -> dict:', '        progress: object = None,\n        max_pieces: int = 26,\n    ) -> dict:', 1)
s = s.replace('        opens = self.layout.connectable_ends()\n        if grow is None or close is None:', '''        if type(max_pieces) is not int or not 1 <= max_pieces <= 128:
            raise ValueError("search depth must be a whole number from 1 to 128")
        if type(max_results) is not int or not 1 <= max_results <= 50:
            raise ValueError("max_results must be a whole number from 1 to 50")
        if not math.isfinite(slop) or slop < 0:
            raise ValueError("slop must be finite and non-negative")
        opens = self.layout.connectable_ends()
        if grow is None or close is None:''', 1)
s = s.replace('        remaining = self.remaining()\n\n        # Height sanity', '''        if grow == close or grow not in opens or close not in opens:
            raise ValueError("pick two distinct open ends")
        self.candidates = []
        self._candidate_revision = self.revision
        remaining = self.remaining()

        # Height sanity''', 1)
a = s.index('            lift = (', s.index('    def solve_gap'))
b = s.index('            if dz > lift', a)
s = s[:a] + '''            lift = sum(
                max((abs(float(m.dz)) for m in _moves_for(self.catalog[pid])), default=0.0) * n
                for pid, n in remaining.items()
            )
''' + s[b:]
s = s.replace('        if dz > 1e-9:\n', '        if dz > 1e-9 and not reversing:\n', 1)
s = s.replace('                    "searched": 0,\n                    "reason":', '''                    "searched": 0,
                    "complete": True,
                    "stop_reason": "height_impossible",
                    "max_pieces_searched": 0,
                    "reason":''', 1)
s = s.replace('arcs = self._arc_closures(grow, close, max_results)', 'arcs = self._arc_closures(grow, close, max_results, max_pieces)', 1)
s = s.replace('                return {"found": len(arcs), "aborted": False, "searched": 0}', '''                return {
                    "found": len(arcs), "aborted": False, "searched": 0,
                    "complete": False, "stop_reason": "heuristic",
                    "max_pieces_searched": max_pieces,
                }''', 1)
s = s.replace('                    max_pieces=26,', '                    max_pieces=max_pieces,', 1)
s = s.replace('            "aborted": aborted and not self.candidates,\n            "searched": searched,', '''            "aborted": aborted,
            "searched": searched,
            "complete": result.stats.complete and inventory == full,
            "stop_reason": (result.stats.stop_reason if inventory == full else "staged_search"),
            "max_pieces_searched": result.stats.max_pieces_searched,''', 1)
s = s.replace('    def apply_candidate(self, index: int) -> None:\n', '''    def apply_candidate(self, index: int, revision: int | None = None) -> None:
        if self._candidate_revision != self.revision or (
            revision is not None and revision != self.revision
        ):
            raise ValueError("candidate is stale (solve again)")
''', 1)
s = s.replace('        chosen = self.candidates[index].layout\n        self._push(chosen)', '''        chosen = self.candidates[index].layout
        used, remaining = self.layout.piece_counts, self.remaining()
        if any(n - used.get(pid, 0) > remaining.get(pid, 0)
               for pid, n in chosen.piece_counts.items()):
            raise ValueError("candidate exceeds the current inventory (solve again)")
        self._push(chosen)''', 1)
a = s.index('def _handler_for(')
s = s[:a] + '''class UnknownRouteError(ValueError):
    """The editor API does not expose this route."""


def dispatch_session(
    session: Session, path: str, body: object, progress: object = None
) -> dict[str, Any]:
    """Shared HTTP/Pyodide API. Call with the session lock on threaded hosts."""
    if not isinstance(body, dict):
        raise ValueError("request body must be a JSON object")
    if path == "/api/state":
        return session.state()
    if path == "/api/export":
        return layout_to_dict(session.layout)
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
        session.set_unlimited(body.get("on"))
    elif path == "/api/add_set":
        session.add_set(str(body["code"]))
    elif path == "/api/stone":
        session.toggle_stone(
            int(body["placement"]), str(body["id"]),
            int(body["at_port"]) if body.get("at_port") is not None else None,
        )
    elif path == "/api/solve":
        outcome = session.solve_gap(
            tuple(body["grow"]) if body.get("grow") else None,
            tuple(body["close"]) if body.get("close") else None,
            float(body.get("slop", 0.0)), int(body.get("max_results", 10)),
            reversing=bool(body.get("reversing", False)), progress=progress,
            max_pieces=int(body.get("max_pieces", 26)),
        )
        return {**outcome, **session.state()}
    elif path == "/api/apply":
        session.apply_candidate(int(body["index"]), body.get("revision"))
    elif path == "/api/import":
        session._push(layout_from_dict(body.get("data"), session.catalog))
    elif path == "/api/restore":
        session.restore(body.get("data"))
    else:
        raise UnknownRouteError(f"no route {path}")
    return session.state()


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
            if not 0 <= length <= MAX_JSON_BYTES:
                raise ValueError("request body larger than 2 MB or invalid length")
            if not length:
                return {}
            return json.loads(self.rfile.read(length).decode("utf-8"))

        def do_GET(self) -> None:  # noqa: N802 (http.server API)
            if self.path in ("/", "/index.html"):
                html = resources.files("duplotrain").joinpath("static/editor.html")
                self._send(200, html.read_bytes(), "text/html; charset=utf-8")
            elif self.path in ("/api/state", "/api/export"):
                with session.lock:
                    self._json(200, dispatch_session(session, self.path, {}))
            else:
                self._json(404, {"error": f"no route {self.path}"})

        def do_POST(self) -> None:  # noqa: N802
            try:
                body = self._body()
                with session.lock:
                    result = dispatch_session(session, self.path, body)
                self._json(200, result)
            except UnknownRouteError as exc:
                self._json(404, {"error": str(exc)})
            except (ValueError, KeyError, TypeError, IndexError, OverflowError) as exc:
                self._json(409, {"error": str(exc)})

    return Handler


''' + s[s.index('def make_server(', a):]
p.write_text(s)
(R / 'webapp/adapter.py').write_text('''"""Expose the same editor API in Pyodide as the local HTTP server."""

import json

from duplotrain.gui import Session, dispatch_session
from duplotrain.validation import MAX_JSON_BYTES

session = Session()

try:
    from js import postMessage as _post

    def _progress(nodes: int) -> None:
        _post(nodes)

except ImportError:  # CPython tests/local host
    _progress = None


def dispatch(path: str, body_json: str | None) -> str:
    """Validate a request, then run the shared dispatcher without partial updates."""
    try:
        if body_json and len(body_json.encode("utf-8")) > MAX_JSON_BYTES:
            raise ValueError("request body larger than 2 MB")
        body = json.loads(body_json) if body_json else {}
        return json.dumps(dispatch_session(session, path, body, progress=_progress))
    except (ValueError, KeyError, TypeError, IndexError, OverflowError) as exc:
        return json.dumps({"__error": str(exc)})
''')
p = R / 'src/duplotrain/cli.py'
s = p.read_text()
s = s.replace('import json\n', 'import importlib\nimport json\n', 1)
s = s.replace('from .solver import SolverConfig, solve\n', 'from .solver import SolverConfig, solve\nfrom .validation import MAX_JSON_BYTES\n', 1)
a = s.index('        try:\n            from .render import render_layout', s.index('    if out:'))
b = s.index('        for rank, (score, sol)', a)
s = s[:a] + '        render_layout = _get_renderer(required=False)\n' + s[b:]
a = s.index('def _load_layout(')
s = s[:a] + '''def _get_renderer(required: bool = True):
    try:
        importlib.import_module("matplotlib")
    except ModuleNotFoundError as exc:
        if exc.name != "matplotlib":
            raise
        message = "matplotlib not installed; install duplotrain[render] to render images"
        if required:
            raise click.ClickException(message) from exc
        console.print(f"{message}; writing layout JSON only", style="yellow", markup=False)
        return None
    from .render import render_layout

    return render_layout


''' + s[a:]
s = s.replace('''        with open(layout_file, encoding="utf-8") as fh:
            return layout_from_dict(json.load(fh), catalog)
    except (ValueError, KeyError) as exc:''', '''        with open(layout_file, "rb") as fh:
            raw = fh.read(MAX_JSON_BYTES + 1)
        if len(raw) > MAX_JSON_BYTES:
            raise ValueError("layout file larger than 2 MB")
        return layout_from_dict(json.loads(raw.decode("utf-8")), catalog)
    except (ValueError, KeyError, TypeError, OSError) as exc:''', 1)
s = s.replace('    from .render import render_layout\n\n    catalog = _catalog', '    render_layout = _get_renderer()\n\n    catalog = _catalog', 1)
s = s.replace('    from .render import render_layout\n\n    catalog = default_catalog()', '    render_layout = _get_renderer()\n\n    catalog = default_catalog()', 1)
s = s.replace('        + (", [red]stopped at node limit[/red]" if stats.aborted else "")', '        + (f", [yellow]stopped: {stats.stop_reason}[/yellow]" if not stats.complete else "")', 1)
s = s.replace('''        console.print(
            "No closed loop fits. Try adding curves''', '''        if not stats.complete:
            console.print("No loop found within the search limits; a closure may still exist.")
            return
        console.print(
            "No closed loop fits. Try adding curves''', 1)
p.write_text(s)
edit('pyproject.toml', 'license = { text = "MIT" }', 'license = { file = "LICENSE" }')
