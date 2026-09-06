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
import math
import threading
import webbrowser
from collections.abc import Mapping
from dataclasses import dataclass, field
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from importlib import resources
from time import monotonic
from typing import Any

from .catalog import ACCESSORIES, STONE_MOUNTS, default_catalog
from .geometry import ORIGIN, steps_to_degrees
from .layout import End, Layout, layout_from_dict, layout_to_dict
from .pieces import PieceType
from .sets import SETS, inventory_for_sets
from .solver import Solution, SolverConfig, _moves_for, solve
from .validation import MAX_JSON_BYTES, MAX_SNAPSHOT_BYTES
from .validation import check_layout_json as check_layout_json

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


MAX_INVENTORY_COUNT = 10_000


def _count(value: object) -> int:
    """Parse an inventory count without silently truncating fractional values."""
    if isinstance(value, str) and value.isascii() and value.isdigit() and len(value) <= 5:
        value = int(value)
    if type(value) is not int or not 0 <= value <= MAX_INVENTORY_COUNT:
        raise ValueError(f"counts must be whole numbers from 0 to {MAX_INVENTORY_COUNT}")
    return value


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
    revision: int = 0
    _candidate_revision: int | None = None

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
        for entry in self.layout.accessories:
            sid = entry[1]
            placed[sid] = placed.get(sid, 0) + 1
        return {
            sid: max(0, self.stones.get(sid, 0) - placed.get(sid, 0))
            for sid in ACCESSORIES
        }

    def _invalidate(self) -> None:
        self.revision += 1
        self.candidates = []
        self._candidate_revision = None

    def set_unlimited(self, on: bool) -> None:
        if type(on) is not bool:
            raise ValueError("unlimited must be a boolean")
        if self.unlimited != on:
            self._check_snapshot({**self.snapshot(), "unlimited": on})
            self.unlimited = on
            self._invalidate()

    @staticmethod
    def _check_snapshot(snapshot: dict[str, Any]) -> None:
        """An accepted edit must be readable by our own import/recovery parser."""
        check_layout_json(snapshot["layout"])
        # ASCII escaping and default whitespace bound the smaller browser JSON
        # representation too; reserve space for its versioned save envelope.
        if len(json.dumps(snapshot, ensure_ascii=True).encode("utf-8")) > MAX_SNAPSHOT_BYTES:
            raise ValueError("session is too large to save; remove pieces before adding more")

    def _push(self, layout: Layout) -> None:
        self._check_snapshot(self.snapshot(layout=layout))
        self.history.append(layout)
        if len(self.history) > 200:
            del self.history[1:2]
        self._invalidate()

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
        joint_issues = layout.joint_issues()
        return {
            "placements": placements,
            "closed": layout.is_closed,  # topological, retained for API compatibility
            "exactly_closed": layout.is_closed and not joint_issues,
            "joint_issues": joint_issues,
            "size_cm": [round(width / 10, 1), round(height / 10, 1)],
            "piece_counts": layout.piece_counts,
        }

    def snapshot(self, *, layout: Layout | None = None) -> dict[str, Any]:
        """Exact geometry and owned counts; suitable for browser-local recovery."""
        return {
            "format": "duplotrain-session/1",
            "layout": layout_to_dict(self.layout if layout is None else layout),
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
        self._check_snapshot({
            **self.snapshot(layout=layout),
            "inventory": inventory, "stones": stones, "unlimited": unlimited,
        })
        # _push may reject geometry/size; do not change owned counts beforehand.
        self._push(layout)
        self.inventory, self.stones, self.unlimited = inventory, stones, unlimited

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
        palette = []
        for pid, piece in self.catalog.items():
            variants = []
            for move in _moves_for(piece):
                entry_name = piece.ports[move.entry].name
                exit_name = piece.ports[move.exit].name
                turn = _signed_degrees(move.dheading)
                rise = float(move.dz)
                if len(piece.ports) == 2 and turn == 0 and abs(rise) > 0.5:
                    # Climbing pieces MUST distinguish direction: two identical
                    # "ahead" buttons once left a user's bridge hanging mid-air.
                    label = (
                        f"↑ climb {rise:.0f}mm"
                        if rise > 0
                        else f"↓ descend {-rise:.0f}mm"
                    )
                elif len(piece.ports) == 2 and turn == 0:
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
        mates = [[list(a), list(b)] for a, b in self.layout.matable_pairs()]
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
            "revision": self.revision,
            "snapshot": self.snapshot(),
            "candidates": [self._candidate_json(i, s) for i, s in enumerate(self.candidates)],
        }

    def _candidate_json(self, index: int, sol: Solution) -> dict[str, Any]:
        preview = self._layout_json(sol.layout)
        added: dict[str, int] = dict(sol.layout.piece_counts)
        for pid, n in self.layout.piece_counts.items():
            added[pid] = added.get(pid, 0) - n
            if added[pid] <= 0:
                del added[pid]
        return {
            "index": index,
            "revision": self._candidate_revision,
            "exact": sol.exact,
            "gap": round(sol.gap, 2),
            "kind": sol.kind,
            "added": added,
            "open_stubs": sol.open_stubs,
            "size_cm": list(preview["size_cm"]),
            "preview": preview,
        }

    # -- mutations ---------------------------------------------------------------

    def attach(self, piece_id: str, entry: int, at: End | None) -> None:
        """Attach a new piece at open end *at* (or place the first piece at the origin)."""
        if piece_id not in self.catalog:
            raise ValueError(f"unknown piece {piece_id!r}")
        if self.remaining().get(piece_id, 0) <= 0:
            raise ValueError(f"no {piece_id!r} left in the box (edit the inventory)")
        piece = self.catalog[piece_id]
        if type(entry) is not int or not 0 <= entry < len(piece.ports) or entry in piece.sealed:
            raise ValueError("pick a valid, unsealed entry port")
        if at is not None and at not in self.layout.connectable_ends():
            raise ValueError("pick an open, unsealed end to attach to")
        if self.layout.placements:
            if at is None:
                raise ValueError("pick an open end to attach to")
            layout, _ = self.layout.attach(piece, entry, at)
        else:
            from .geometry import ORIGIN

            layout, _ = self.layout.with_piece(piece, piece.frame_for(entry, ORIGIN))
        self._push(layout)

    def join(self, a: End, b: End) -> None:
        opens = self.layout.connectable_ends()
        if a == b or a not in opens or b not in opens:
            raise ValueError("pick two distinct open ends to join")
        self._push(self.layout.join(a, b))

    def remove_piece(self, placement: int) -> None:
        self._push(self.layout.remove(placement))

    def undo(self) -> None:
        if len(self.history) > 1:
            self.history.pop()
            self._invalidate()

    def clear(self) -> None:
        self._push(Layout())

    def set_inventory(self, counts: Mapping[str, Any]) -> None:
        validated = self._validated_counts(counts, {**self.catalog, **ACCESSORIES})
        inventory, stones = dict(self.inventory), dict(self.stones)
        for pid, n in validated.items():
            (inventory if pid in self.catalog else stones)[pid] = n
        if inventory != self.inventory or stones != self.stones:
            self._check_snapshot({**self.snapshot(), "inventory": inventory, "stones": stones})
            self.inventory, self.stones = inventory, stones
            self._invalidate()

    def add_set(self, code: str) -> None:
        """Add one boxed set, applying the same atomic count checks as manual edits."""
        pieces, stones = inventory_for_sets([code])
        self.set_inventory({
            **{pid: self.inventory.get(pid, 0) + n for pid, n in pieces.items()},
            **{sid: self.stones.get(sid, 0) + n for sid, n in stones.items()},
        })

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

    def _arc_closures(
        self, grow: End, close: End, max_results: int, max_pieces: int = 26
    ) -> list[Solution]:
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

        if not all(pid in self.catalog for pid in ("curve", "straight", "ramp", "span")):
            return []
        remaining = self.remaining()
        base = self.layout
        n_base = len(base)
        curve, straight = self.catalog["curve"], self.catalog["straight"]
        ramp, span = self.catalog["ramp"], self.catalog["span"]
        deltas = {
            (pid, side): self.catalog[pid].exit_delta(side, 1 - side)
            for pid in ("ramp", "span") for side in (0, 1)
        }
        target = base.pose_of(close)
        s_delta = straight.exit_delta(0, 1)
        c_delta = {entry: curve.exit_delta(entry, 1 - entry) for entry in (0, 1)}

        # Leveling units: (sequence of (piece, entry), float dz).  Monotone
        # ramp/span runs of length <= 4 both ways, the empty unit, and the full
        # bridge (which levels out at zero but spans 1024 mm of run).
        units: list[tuple[tuple, float]] = [((), 0.0)]
        for length in (1, 2, 3, 4):
            for combo in itertools.product(("ramp", "span"), repeat=length):
                for entry_side in (0, 1):
                    seq = tuple((pid, entry_side) for pid in combo)
                    dz = sum(float(deltas[pid, entry_side][2])
                             for pid in combo)
                    units.append((seq, dz))
        units.append(
            ((("ramp", 0), ("span", 0), ("span", 1), ("ramp", 1)), 0.0)
        )

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

        # One exact rigid transform per demanded unit, local to this search.
        unit_deltas = {}

        def apply_unit(pose, seq):
            if not seq:
                return pose
            if seq not in unit_deltas:
                unit = ORIGIN
                for pid, side in seq:
                    unit = unit.then(*deltas[pid, side])
                unit_deltas[seq] = (unit.x, unit.y, unit.z, unit.heading)
            return pose.then(*unit_deltas[seq])

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
        prefixes = {}
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
                        # Different post-units reuse the same exact prefix.
                        prefix = (pre, j, k, entry)
                        if prefix not in prefixes:
                            pose = start_pre
                            for _ in range(j):
                                pose = pose.then(*s_delta)
                            for _ in range(k):
                                pose = pose.then(*c_delta[entry])
                            prefixes[prefix] = pose
                        pose = prefixes[prefix]
                        for m in range(0, 9):
                            if m:
                                pose = pose.then(*s_delta)
                            if len(pre) + len(post) + j + k + m > max_pieces:
                                continue
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
        max_pieces: int = 26,
    ) -> dict:
        """Search for completions; returns {found, aborted, searched[, reason]}.

        An instant arc oracle runs first (ring closures the DFS misses), then
        the staged search: plain running track (curves + straights) first --
        that closes almost every real gap within a few thousand nodes -- then
        the whole box only if needed.  A depth-first search over a BROAD
        inventory otherwise drowns exploring exotic-piece subtrees before
        finding the obvious answer.
        """
        if type(max_pieces) is not int or not 1 <= max_pieces <= 128:
            raise ValueError("search depth must be a whole number from 1 to 128")
        if type(max_results) is not int or not 1 <= max_results <= 50:
            raise ValueError("max_results must be a whole number from 1 to 50")
        if not math.isfinite(slop) or slop < 0:
            raise ValueError("slop must be finite and non-negative")
        opens = self.layout.connectable_ends()
        if grow is None or close is None:
            if len(opens) != 2:
                raise ValueError(
                    "pick the two ends to close (the layout has "
                    f"{len(opens)} open ends)"
                )
            grow, close = opens[1], opens[0]

        if grow == close or grow not in opens or close not in opens:
            raise ValueError("pick two distinct open ends")
        # Candidate indices change on every search, even on unchanged geometry.
        # Give the result list its own revision so another tab cannot apply an
        # index from the previous search to this one.
        self._invalidate()
        self._candidate_revision = self.revision
        remaining = self.remaining()

        # Height sanity: if the two ends differ in elevation by more than every
        # climbing piece left in the box can supply, no search can help.
        dz = abs(float(self.layout.pose_of(grow).z) - float(self.layout.pose_of(close).z))
        if dz > 1e-9 and not reversing:
            lift = sum(
                max((abs(float(m.dz)) for m in _moves_for(self.catalog[pid])), default=0.0) * n
                for pid, n in remaining.items()
            )
            if dz > lift + 1e-6:
                self.candidates = []
                return {
                    "found": 0,
                    "aborted": False,
                    "searched": 0,
                    "complete": True,
                    "stop_reason": "height_impossible",
                    "max_pieces_searched": 0,
                    "reason": (
                        f"impossible: those ends differ by {dz:.0f} mm in height "
                        f"and the remaining pieces can climb at most {lift:.0f} mm "
                        "— the track up there can never come back down"
                    ),
                }

        if not reversing:
            arcs = self._arc_closures(grow, close, max_results, max_pieces)
            if arcs:
                self.candidates = arcs
                return {
                    "found": len(arcs), "aborted": False, "searched": 0,
                    "complete": False, "stop_reason": "heuristic",
                    "max_pieces_searched": max_pieces,
                }
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
                    max_pieces=max_pieces,
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
            "aborted": aborted,
            "searched": searched,
            "complete": result.stats.complete and inventory == full,
            "stop_reason": (result.stats.stop_reason if inventory == full else "staged_search"),
            "max_pieces_searched": result.stats.max_pieces_searched,
        }

    def apply_candidate(self, index: int, revision: int | None = None) -> None:
        if self._candidate_revision != self.revision or (
            revision is not None and revision != self.revision
        ):
            raise ValueError("candidate is stale (solve again)")
        if not 0 <= index < len(self.candidates):
            raise ValueError("no such candidate (solve again)")
        chosen = self.candidates[index].layout
        used, remaining = self.layout.piece_counts, self.remaining()
        if any(n - used.get(pid, 0) > remaining.get(pid, 0)
               for pid, n in chosen.piece_counts.items()):
            raise ValueError("candidate exceeds the current inventory (solve again)")
        self._push(chosen)


# --------------------------------------------------------------------------------------
# HTTP plumbing
# --------------------------------------------------------------------------------------


class UnknownRouteError(ValueError):
    """The editor API does not expose this route."""


class RevisionConflictError(ValueError):
    """The client is attempting to edit a state it has not seen."""


MUTATING_ROUTES = frozenset({
    "/api/attach", "/api/join", "/api/undo", "/api/remove", "/api/clear",
    "/api/inventory", "/api/unlimited", "/api/add_set", "/api/stone",
    "/api/solve", "/api/apply", "/api/import", "/api/restore",
})


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
    if path not in MUTATING_ROUTES:
        raise UnknownRouteError(f"no route {path}")
    revision = body.get("revision")
    if type(revision) is not int or revision != session.revision:
        raise RevisionConflictError(
            "The session changed in another tab, or this page is out of date. "
            "Your action was not applied. Review the refreshed layout and try again."
        )
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
        BODY_SECONDS = 10.0

        def setup(self) -> None:
            super().setup()
            self.connection.settimeout(self.BODY_SECONDS)

        def log_message(self, fmt: str, *args: Any) -> None:  # quiet
            pass

        def _send(self, status: int, payload: bytes, content_type: str) -> None:
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(payload)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("X-Frame-Options", "DENY")
            self.send_header("Content-Security-Policy", "frame-ancestors 'none'")
            self.send_header("Cross-Origin-Resource-Policy", "same-origin")
            self.end_headers()
            self.wfile.write(payload)

        def _json(self, status: int, data: Any) -> None:
            self._send(status, json.dumps(data).encode("utf-8"), "application/json")

        #: Discard at most this much of a rejected body, for at most this long.
        DRAIN_BYTES = 64 * 1024
        DRAIN_SECONDS = 0.25

        def _drain_body(self) -> None:
            """Discard a rejected request's body before the connection closes.

            Closing a socket that still holds unread bytes is an abortive close,
            and the reset discards the response written just before it, so the
            client reports a connection error instead of reading the refusal.

            Never wait on a body that was promised but not sent: a declared
            length is not evidence that the bytes are coming, so the drain is
            bounded in both size and time and gives up rather than blocking.
            """
            lengths = self.headers.get_all("Content-Length", [])
            if self.headers.get_all("Transfer-Encoding") or len(lengths) != 1:
                return
            raw = lengths[0]
            if not (raw.isascii() and raw.isdigit() and len(raw) <= 10):
                return
            if getattr(self, "_body_read_failed", False):
                return  # A timed-out buffered socket is no longer readable.
            remaining = min(
                max(0, int(raw) - getattr(self, "_body_bytes_read", 0)), self.DRAIN_BYTES
            )
            if not remaining:
                return
            previous = self.connection.gettimeout()
            deadline = monotonic() + self.DRAIN_SECONDS
            try:
                while remaining > 0:
                    time_left = deadline - monotonic()
                    if time_left <= 0:
                        return
                    self.connection.settimeout(time_left)
                    # read() can perform many raw reads as bytes trickle in.
                    # read1() returns after at most one, letting us recheck time.
                    chunk = self.rfile.read1(min(remaining, 4096))
                    if not chunk:
                        return
                    remaining -= len(chunk)
            except OSError:
                return
            finally:
                try:
                    self.connection.settimeout(previous)
                except OSError:
                    pass

        def _reject(self, status: int, message: str) -> bool:
            # Do not reuse a connection with an unread, rejected request body.
            self._drain_body()
            self.close_connection = True
            self._json(status, {"error": message})
            return False

        def _trusted_request(self) -> bool:
            # Binding to loopback alone does not stop CSRF or DNS rebinding.
            # Compare authorities literally: no suffix matching, DNS resolution,
            # forwarded headers, userinfo, alternative IP spellings or other ports.
            port = self.server.server_port
            allowed_hosts = {f"127.0.0.1:{port}", f"localhost:{port}"}
            if port == 80:
                allowed_hosts.update({"127.0.0.1", "localhost"})
            hosts = self.headers.get_all("Host", [])
            if len(hosts) != 1 or hosts[0].lower() not in allowed_hosts:
                return self._reject(403, "invalid local editor host")
            origins = self.headers.get_all("Origin", [])
            if origins and (len(origins) != 1 or origins[0] != f"http://{hosts[0].lower()}"):
                return self._reject(403, "cross-origin editor request forbidden")
            sites = self.headers.get_all("Sec-Fetch-Site", [])
            if (self.command == "POST" or self.path.startswith("/api/")) and sites:
                if len(sites) != 1 or sites[0] not in ("same-origin", "none"):
                    return self._reject(403, "cross-site editor request forbidden")
            # Non-browser local clients need not send Origin/Fetch Metadata.
            # Requiring non-simple JSON even for an empty POST closes the browser
            # fallback: HTML forms/no-cors fetch cannot send it without preflight.
            # We deliberately never grant CORS/preflight access.
            if self.command == "POST":
                types = self.headers.get_all("Content-Type", [])
                if len(types) != 1 or types[0].split(";", 1)[0].strip().lower() != (
                    "application/json"
                ):
                    return self._reject(415, "editor requests require application/json")
            return True

        def _body(self) -> dict[str, Any]:
            lengths = self.headers.get_all("Content-Length", [])
            if self.headers.get_all("Transfer-Encoding") or len(lengths) > 1:
                raise ValueError("unsupported or ambiguous request framing")
            raw_length = lengths[0] if lengths else "0"
            if not (raw_length.isascii() and raw_length.isdigit() and len(raw_length) <= 10):
                raise ValueError("invalid request length")
            length = int(raw_length)
            if length > MAX_JSON_BYTES:
                raise ValueError("request body larger than 2 MB")
            if not length:
                return {}
            payload = bytearray()
            previous = self.connection.gettimeout()
            deadline = monotonic() + self.BODY_SECONDS
            try:
                while len(payload) < length:
                    time_left = deadline - monotonic()
                    if time_left <= 0:
                        raise TimeoutError("request body timed out")
                    self.connection.settimeout(time_left)
                    chunk = self.rfile.read1(min(length - len(payload), 64 * 1024))
                    if not chunk:
                        raise ValueError("incomplete request body")
                    payload.extend(chunk)
                    self._body_bytes_read = len(payload)
            except OSError:
                self._body_read_failed = True
                raise
            finally:
                self.connection.settimeout(previous)
            return json.loads(payload.decode("utf-8"))

        def do_GET(self) -> None:  # noqa: N802 (http.server API)
            if not self._trusted_request():
                return
            if self.path in ("/", "/index.html"):
                html = resources.files("duplotrain").joinpath("static/editor.html")
                self._send(200, html.read_bytes(), "text/html; charset=utf-8")
            elif self.path in ("/api/state", "/api/export"):
                with session.lock:
                    self._json(200, dispatch_session(session, self.path, {}))
            else:
                self._json(404, {"error": f"no route {self.path}"})

        def do_POST(self) -> None:  # noqa: N802
            self._body_bytes_read = 0
            self._body_read_failed = False
            if not self._trusted_request():
                return
            try:
                body = self._body()
                with session.lock:
                    result = dispatch_session(session, self.path, body)
                self._json(200, result)
            except RevisionConflictError as exc:
                # The comparison above happened under the same lock as edits.
                # Return current state, but never replay the rejected mutation.
                with session.lock:
                    current = session.state()
                self._json(409, {"error": str(exc), "code": "stale_revision", "state": current})
            except UnknownRouteError as exc:
                self._json(404, {"error": str(exc)})
            except TimeoutError:
                self._reject(408, "request body timed out")
            except (
                ValueError, KeyError, TypeError, IndexError, OverflowError, RecursionError
            ) as exc:
                self._reject(409, str(exc))

        def do_OPTIONS(self) -> None:  # noqa: N802
            self._reject(403, "cross-origin editor access is not enabled")

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
