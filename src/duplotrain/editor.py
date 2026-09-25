"""Editor state and JSON API shared by the local host and Pyodide worker.

Full exact layouts and candidates live here. Presentation payloads are disposable;
HTTP framing, host validation and desktop launch belong to :mod:`duplotrain.gui`.
"""

from __future__ import annotations

import itertools
import json
import math
import secrets
import threading
from collections.abc import Mapping
from dataclasses import dataclass, field
from functools import lru_cache
from typing import Any

from .bridge_completion import bridge_completion
from .catalog import ACCESSORIES, STONE_MOUNTS, default_catalog
from .collision import DEFAULT_CLEARANCE
from .completion_search import solve_completion as solve
from .editor_tools import switch_choices
from .geometry import ORIGIN, Pose, steps_to_degrees
from .lattice import LatticePoint, from_alg_xy, z_from_alg
from .layout import End, Layout, Placement, layout_from_dict, layout_to_dict
from .pieces import PieceType
from .sets import SETS, inventory_for_sets
from .solver import (
    Solution,
    SolverConfig,
    _flat,
    _lattice_rotations,
    _lattice_step,
    _moves_for,
    _OverlapAudit,
    _pose_to_lattice,
)
from .validation import MAX_SNAPSHOT_BYTES
from .validation import check_layout_json as check_layout_json

__all__ = ["Session", "dispatch_session", "RevisionConflictError", "UnknownRouteError"]

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

# An opt-in presentation contract; saved layouts and full previews do not change.
PREVIEW_FORMAT = "duplotrain-preview/1"


def _count(value: object) -> int:
    """Parse an inventory count without silently truncating fractional values."""
    if isinstance(value, str) and value.isascii() and value.isdigit() and len(value) <= 5:
        value = int(value)
    if type(value) is not int or not 0 <= value <= MAX_INVENTORY_COUNT:
        raise ValueError(f"counts must be whole numbers from 0 to {MAX_INVENTORY_COUNT}")
    return value


def _index(value: object, name: str) -> int:
    """Reject coercible values (including booleans) before any editor mutation."""
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    return value


def _end(value: object, name: str) -> End:
    """Validate both indices before equality or membership can alias 0/1 to bool."""
    if not isinstance(value, (list, tuple)) or len(value) != 2:
        raise ValueError(f"{name} must be a [placement, port] integer pair")
    return _index(value[0], f"{name} placement"), _index(value[1], f"{name} port")


def _signed_degrees(dheading: int) -> int:
    degrees = steps_to_degrees(dheading)
    return degrees - 360 if degrees >= 180 else degrees


@lru_cache(maxsize=2048)
def _drawing_lines(placement: Placement) -> tuple:
    """Immutable presentation geometry only; never retain a Session or its links."""
    return tuple(
        tuple((round(x, 2), round(y, 2), round(z, 2)) for x, y, z in line)
        for line in placement.centrelines(spacing=10.0)
    )


@lru_cache(maxsize=32)
def _drawing_size(placements: tuple[Placement, ...]) -> tuple[float, float]:
    """Bounded footprint reuse for immutable geometry, independent of topology."""
    return Layout(placements).size()


class _ExactArcGeometry:
    """Pose arithmetic for the arc oracle in the exact field (any catalogue)."""

    def __init__(self, catalog: Mapping[str, PieceType], start: Pose, target: Pose) -> None:
        self._catalog = catalog
        self.start, self.target = start, target
        self._runs: dict[tuple, list] = {}

    def step(self, pid: str, entry: int, exit_port: int):
        delta = self._catalog[pid].exit_delta(entry, exit_port)
        return lambda pose: pose.then(*delta)

    def run(self, pid: str, entry: int, exit_port: int, count: int):
        """One transform equal to *count* steps, composed once and reused."""
        runs = self._runs.setdefault((pid, entry, exit_port), [ORIGIN])
        step = self.step(pid, entry, exit_port)
        while len(runs) <= count:
            runs.append(step(runs[-1]))
        pose = runs[count]
        x, y, z, heading = pose.x, pose.y, pose.z, pose.heading
        return lambda cursor: cursor.then(x, y, z, heading)

    @staticmethod
    def reverse(pose: Pose) -> Pose:
        return pose.reversed()

    @staticmethod
    def heading(pose: Pose) -> int:
        return pose.heading


class _LatticeArcGeometry:
    """The same arithmetic on the integer lattice: a step is one tuple addition.

    Poses are the solver's flat lattice tuples, which are equal exactly when the
    field poses are, so the oracle's exact matching of prefixes against suffixes
    is unchanged. Available only when the ends and every traversal fit the
    30-degree lattice; standard track always does.
    """

    STEPS = tuple((pid, entry, 1 - entry)
                  for pid in ("straight", "curve", "ramp", "span") for entry in (0, 1))

    @classmethod
    def compile(cls, catalog: Mapping[str, PieceType], start: Pose, target: Pose):
        start_l, target_l = _pose_to_lattice(start), _pose_to_lattice(target)
        if start_l is None or target_l is None:
            return None
        steps = {}
        for pid, entry, exit_port in cls.STEPS:
            dx, dy, dz, dheading = catalog[pid].exit_delta(entry, exit_port)
            delta, rise = from_alg_xy(dx, dy), z_from_alg(dz)
            if dheading % 2 or delta is None or rise is None:
                return None
            steps[pid, entry, exit_port] = (_lattice_rotations(delta), rise, dheading // 2)
        geometry = cls()
        geometry.start, geometry.target = _flat(start_l), _flat(target_l)
        geometry._steps = steps
        geometry._runs: dict[tuple, list] = {}
        geometry._run_steps: dict[tuple, tuple] = {}
        return geometry

    def step(self, pid: str, entry: int, exit_port: int):
        return _lattice_step(*self._steps[pid, entry, exit_port])

    def run(self, pid: str, entry: int, exit_port: int, count: int):
        key = (pid, entry, exit_port)
        cached = self._run_steps.get((key, count))
        if cached is None:
            runs = self._runs.setdefault(key, [(0, 0, 0, 0, 0, 0)])
            step = self.step(*key)
            while len(runs) <= count:
                runs.append(step(runs[-1]))
            a, b, c, d, z, heading = runs[count]
            cached = self._run_steps[key, count] = _lattice_step(
                _lattice_rotations(LatticePoint(a, b, c, d)), z, heading)
        return cached

    @staticmethod
    def reverse(pose: tuple) -> tuple:
        return (*pose[:5], (pose[5] + 6) % 12)

    @staticmethod
    def heading(pose: tuple) -> int:
        return pose[5] * 2


@dataclass(frozen=True)
class _EditState:
    """Small history record; exact immutable layouts remain structurally shared."""

    inventory: tuple[tuple[str, int], ...]
    stones: tuple[tuple[str, int], ...]
    unlimited: bool
    label: str


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
    #: Revisions restart at 0 in every engine process or worker; this random id
    #: tells a restarted engine's revision 3 from the one a stale tab saw.
    instance: str = field(default_factory=lambda: secrets.token_hex(8), init=False)
    _candidate_revision: int | None = None
    _history_state: list[_EditState] = field(default_factory=list, init=False, repr=False)
    _interactive_job: object = field(default=None, init=False, repr=False)
    _future: list[tuple[Layout, _EditState]] = field(default_factory=list, init=False, repr=False)

    def __post_init__(self) -> None:
        if not self.history:
            self.history = [Layout()]
        self._history_state = [self._edit_state("layout change") for _ in self.history]

    def _edit_state(self, label: str) -> _EditState:
        return _EditState(tuple(self.inventory.items()), tuple(self.stones.items()),
                          self.unlimited, label)

    def _sync_history(self) -> None:
        # ``Session(history=[...])`` and callers that assign ``history`` directly
        # give layouts without edit states; give them some.
        if len(self._history_state) != len(self.history):
            self._history_state = [self._edit_state("layout change") for _ in self.history]
            self._future.clear()
        self._history_state[-1] = self._edit_state(self._history_state[-1].label)

    def _restore_edit(self, edit: _EditState) -> None:
        self.inventory, self.stones = dict(edit.inventory), dict(edit.stones)
        self.unlimited = edit.unlimited

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
        job, self._interactive_job = self._interactive_job, None
        if job is not None:
            job.close()
        self.revision += 1
        self.candidates = []
        self._candidate_revision = None

    def set_unlimited(self, on: bool) -> None:
        if type(on) is not bool:
            raise ValueError("unlimited must be a boolean")
        if self.unlimited != on:
            self._commit(self.layout, unlimited=on, label="sandbox change")

    @staticmethod
    def _check_snapshot(snapshot: dict[str, Any]) -> None:
        """An accepted edit must be readable by our own import/recovery parser."""
        check_layout_json(snapshot["layout"])
        # ASCII escaping and default whitespace bound the smaller browser JSON
        # representation too; reserve space for its versioned save envelope.
        if len(json.dumps(snapshot, ensure_ascii=True).encode("utf-8")) > MAX_SNAPSHOT_BYTES:
            raise ValueError("session is too large to save; remove pieces before adding more")

    def _commit(
        self, layout: Layout, *, inventory: dict[str, int] | None = None,
        stones: dict[str, int] | None = None, unlimited: bool | None = None,
        label: str = "layout change",
    ) -> None:
        inventory = dict(self.inventory if inventory is None else inventory)
        stones = dict(self.stones if stones is None else stones)
        unlimited = self.unlimited if unlimited is None else unlimited
        self._check_snapshot({**self.snapshot(layout=layout), "inventory": inventory,
                              "stones": stones, "unlimited": unlimited})
        # Validation is complete before any history, ownership or revision changes.
        self._sync_history()
        self.history.append(layout)
        self.inventory, self.stones, self.unlimited = inventory, stones, unlimited
        self._history_state.append(self._edit_state(label))
        if len(self.history) > 200:
            # The oldest kept state becomes the base: every undo step left
            # reverts exactly the one edit its label names.
            del self.history[0]
            del self._history_state[0]
        self._future.clear()
        self._invalidate()

    def _push(self, layout: Layout, label: str = "layout change") -> None:
        self._commit(layout, label=label)

    # -- serialisation for the front end ----------------------------------------

    @staticmethod
    def _drawing_json(placement: Placement) -> dict[str, Any]:
        """Disposable drawing data, never a substitute for the exact placement."""
        return {
            "width": placement.piece.width,
            "lines": [[list(point) for point in line] for line in _drawing_lines(placement)],
        }

    def _layout_json(
        self, layout: Layout, port_poses: Mapping[End, Pose] | None = None
    ) -> dict[str, Any]:
        placements = []
        for index, placement in enumerate(layout):
            drawing = self._drawing_json(placement)
            lines = drawing["lines"]
            ports = []
            for port in range(len(placement.piece.ports)):
                pose = (
                    placement.port_pose(port)
                    if port_poses is None
                    else port_poses[(index, port)]
                )
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
                    **drawing,
                    "ports": ports,
                    "mid": [mid[0], mid[1]],
                    "stone_ok": placement.piece.id in STONE_MOUNTS,
                    "stone_marks": [
                        {"id": sid, "at": pos}
                        for sid, pos in layout.stone_entries_on(index)
                    ],
                }
            )
        width, height = _drawing_size(layout.placements)
        joint_issues = layout.joint_issues(port_poses)
        return {
            "placements": placements,
            "closed": layout.is_closed,  # topological; exactly_closed also audits joints
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

    def restore(self, data: object, *, new_history: bool = False) -> None:
        """Restore a validated checkpoint atomically. Never partially mutate on error.

        Opening a project is one undoable change. Recovering a session into an
        engine (autosave on a fresh engine, a worker or server restart) starts a
        *new_history* instead: undoing it could only empty the engine again, and
        autosave would then replace the recovered checkpoint with that.
        """
        if not isinstance(data, dict) or data.get("format") != "duplotrain-session/1":
            raise ValueError("unrecognised session format")
        inventory = self._validated_counts(data.get("inventory"), self.catalog)
        stones = self._validated_counts(data.get("stones"), ACCESSORIES)
        unlimited = data.get("unlimited")
        if type(unlimited) is not bool:
            raise ValueError("unlimited must be a boolean")
        layout = layout_from_dict(data.get("layout"), self.catalog)
        # _commit validates the complete proposed snapshot before any mutation.
        self._commit(layout, inventory=inventory, stones=stones, unlimited=unlimited,
                     label="project restore")
        if new_history:
            del self.history[:-1]
            del self._history_state[:-1]

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

    def state(self, *, preview_format: str | None = None) -> dict[str, Any]:
        """Return fresh state; compact previews are explicitly negotiated by clients."""
        if preview_format is not None and preview_format != PREVIEW_FORMAT:
            raise ValueError("unsupported preview format")
        layout = self.layout
        port_poses = {
            (index, port): placement.port_pose(port)
            for index, placement in enumerate(layout)
            for port in range(len(placement.piece.ports))
        }
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
                    "junction": piece.is_junction,
                    "provisional": piece.provisional,
                    "variants": variants,
                }
            )
        mates = [[list(a), list(b)] for a, b in layout.matable_pairs(port_poses)]
        return {
            "layout": self._layout_json(layout, port_poses),
            "open_ends": [list(end) for end in layout.connectable_ends()],
            "matable": mates,
            "train_switches": switch_choices(layout),
            "inventory": {
                "owned": {pid: self.inventory.get(pid, 0) for pid in self.catalog},
                "remaining": self.remaining(),
                "unlimited": self.unlimited,
            },
            "stones": {
                "catalog": {sid: dict(info) for sid, info in ACCESSORIES.items()},
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
            "can_redo": bool(self._future),
            "undo_label": self._history_state[-1].label if len(self.history) > 1 else None,
            "redo_label": self._future[-1][1].label if self._future else None,
            "revision": self.revision,
            "instance": self.instance,
            "snapshot": self.snapshot(),
            "candidates": [
                self._candidate_json(i, s, preview_format=preview_format)
                for i, s in enumerate(self.candidates)
            ],
        }

    def _candidate_json(
        self, index: int, sol: Solution, *, preview_format: str | None = None
    ) -> dict[str, Any]:
        if preview_format == PREVIEW_FORMAT:
            base = self.layout.placements
            # Only share an identical geometry prefix. A future solver that moves
            # existing track falls back to drawing the whole candidate, not a lie.
            shared = len(base) if sol.layout.placements[:len(base)] == base else 0
            preview = {
                "format": PREVIEW_FORMAT,
                "base_revision": self._candidate_revision,
                "base_count": shared,
                "placements": [self._drawing_json(p) for p in sol.layout.placements[shared:]],
            }
            width, height = _drawing_size(sol.layout.placements)
            size_cm = [round(width / 10, 1), round(height / 10, 1)]
        else:
            preview = self._layout_json(sol.layout)
            size_cm = list(preview["size_cm"])
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
            "size_cm": size_cm,
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
        if at is not None:
            at = _end(at, "at")
        if at is not None and at not in self.layout.connectable_ends():
            raise ValueError("pick an open, unsealed end to attach to")
        if self.layout.placements:
            if at is None:
                raise ValueError("pick an open end to attach to")
            layout, _ = self.layout.attach(piece, entry, at)
        else:
            layout, _ = self.layout.with_piece(piece, piece.frame_for(entry, ORIGIN))
        self._push(layout, "attach piece")

    def join(self, a: End, b: End) -> None:
        a, b = _end(a, "a"), _end(b, "b")
        opens = self.layout.connectable_ends()
        if a == b or a not in opens or b not in opens:
            raise ValueError("pick two distinct open ends to join")
        self._push(self.layout.join(a, b), "join ends")

    def remove_piece(self, placement: int) -> None:
        self._push(self.layout.remove(_index(placement, "placement")), "remove piece")

    def undo(self) -> None:
        if len(self.history) > 1:
            self._sync_history()
            self._future.append((self.history.pop(), self._history_state.pop()))
            self._restore_edit(self._history_state[-1])
            self._invalidate()

    def redo(self) -> None:
        if self._future:
            layout, edit = self._future.pop()
            self.history.append(layout)
            self._history_state.append(edit)
            self._restore_edit(edit)
            self._invalidate()

    def clear(self) -> None:
        # Clearing nothing is not an edit: preserve redo, candidates and revision.
        # Deliberate import/restore and candidate publication keep their semantics.
        if self.layout.placements:
            self._push(Layout(), "clear layout")

    def set_inventory(self, counts: Mapping[str, Any]) -> None:
        validated = self._validated_counts(counts, {**self.catalog, **ACCESSORIES})
        inventory, stones = dict(self.inventory), dict(self.stones)
        for pid, n in validated.items():
            (inventory if pid in self.catalog else stones)[pid] = n
        if inventory != self.inventory or stones != self.stones:
            self._commit(self.layout, inventory=inventory, stones=stones,
                         label="inventory change")

    def add_set(self, code: str) -> None:
        """Add one boxed set, applying the same atomic count checks as manual edits."""
        pieces, stones = inventory_for_sets([code])
        self.set_inventory({
            **{pid: self.inventory.get(pid, 0) + n for pid, n in pieces.items()},
            **{sid: self.stones.get(sid, 0) + n for sid, n in stones.items()},
        })

    def toggle_stone(
        self, placement: int, stone_id: str, at_port: int | None = None,
        *, remove_only: bool = False,
    ) -> None:
        """Toggle a stone at the selected position, or remove only that marker."""
        if stone_id not in ACCESSORIES:
            raise ValueError(f"unknown action stone {stone_id!r}")
        placement = _index(placement, "placement")
        if not 0 <= placement < len(self.layout.placements):
            raise ValueError(f"no placement {placement}")
        piece = self.layout.placements[placement].piece
        if at_port is not None and (
            type(at_port) is not int or not 0 <= at_port < len(piece.ports)
        ):
            raise ValueError("pick a valid stone position")
        if type(remove_only) is not bool:
            raise ValueError("remove must be a boolean")
        if (stone_id, at_port) in self.layout.stone_entries_on(placement):
            self._push(self.layout.without_accessory(placement, stone_id, at_port=at_port),
                       "remove stone")
            return
        if remove_only:
            raise ValueError("no such stone at the selected position")
        if piece.id not in STONE_MOUNTS:
            raise ValueError(f"action stones clip onto straights, not {piece.id!r}")
        if self.stones_remaining().get(stone_id, 0) <= 0:
            raise ValueError(f"no {stone_id!r} left (edit the inventory)")
        self._push(self.layout.with_accessory(placement, stone_id, at_port=at_port), "place stone")

    def _arc_closures(self, grow: End, close: End, max_results: int,
                      max_pieces: int = 26) -> list[Solution]:
        """Synchronous compatibility wrapper around the cooperative arc oracle."""
        return [item for item in self._arc_events(grow, close, max_results, max_pieces)
                if item is not None]

    def _arc_events(
        self, grow: End, close: End, max_results: int, max_pieces: int = 26
    ):
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
        # Thousands of exact pose checks: on the lattice each is one tuple add.
        geometry = (
            _LatticeArcGeometry.compile(self.catalog, base.pose_of(grow), target)
            or _ExactArcGeometry(self.catalog, base.pose_of(grow), target)
        )
        s_back = geometry.step("straight", 1, 0)
        unit_steps = {
            (pid, side): geometry.step(pid, side, 1 - side)
            for pid in ("ramp", "span") for side in (0, 1)
        }

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

        def apply_unit(pose, seq):
            # Rigid motions compose associatively, so stepping through a unit
            # gives exactly the pose its composed transform gave.
            for pid, side in seq:
                pose = unit_steps[pid, side](pose)
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

        start, target = geometry.start, geometry.target
        want_heading = (geometry.heading(target) + 12) % 24
        audit = _OverlapAudit(base, DEFAULT_CLEARANCE, 8.0)
        found: list[Solution] = []
        seen_pre = {}
        prefixes = {}
        suffixes = {}
        # Build each relative run once, then compose it into any prefix's frame.
        # Rigid transforms associate, so this replaces j+k transforms per trial
        # with at most two without changing placements or template order.
        seen_layouts = set()
        for pre, post in pairs:
            yield None  # cooperative boundary between bounded template groups
            if post not in suffixes:
                # Walk the suffix BACK from the target once. Matching a prefix
                # is then an exact pose lookup, not up to nine repeated chains
                # of costly radical transforms for every prefix/post pair.
                reverse_post = tuple((pid, 1 - side) for pid, side in reversed(post))
                cursor = apply_unit(target, reverse_post)
                matches = {}
                for m in range(min(8, remaining.get("straight", 0)) + 1):
                    matches.setdefault(geometry.reverse(cursor), []).append(m)
                    cursor = s_back(cursor)
                suffixes[post] = matches
            if pre not in seen_pre:
                seen_pre[pre] = apply_unit(start, pre)
            start_pre = seen_pre[pre]
            for entry, turn in ((0, 2), (1, -2)):
                for k in range(0 if (pre or post) else 1, 14):
                    if (geometry.heading(start_pre) + turn * k) % 24 != want_heading:
                        continue
                    if k > remaining.get("curve", 0):
                        break
                    for j in range(min(8, remaining.get("straight", 0)) + 1):
                        if len(pre) + len(post) + j + k > max_pieces:
                            break
                        # Different post-units reuse the same exact prefix.
                        prefix = (pre, j, k, entry)
                        if prefix not in prefixes:
                            pose = start_pre
                            if j:
                                pose = geometry.run("straight", 0, 1, j)(pose)
                            if k:
                                pose = geometry.run("curve", entry, 1 - entry, k)(pose)
                            prefixes[prefix] = pose
                        pose = prefixes[prefix]
                        for m in suffixes[post].get(pose, ()):
                            if len(pre) + len(post) + j + k + m > max_pieces:
                                continue
                            if j + m > remaining.get("straight", 0):
                                continue
                            if not pre and not post and not k:
                                continue
                            try:
                                closed = build(pre, j, k, entry, m, post)
                            except ValueError:
                                continue
                            if audit.overlaps(closed):
                                continue
                            # Different prefix/suffix splits (especially k=0)
                            # can describe exactly the same added pieces.
                            key = closed.placements[n_base:]
                            if key in seen_layouts:
                                continue
                            seen_layouts.add(key)
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
                            yield found[-1]
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
        search_effort: int = 1,
        cancel_check: object = None,
    ) -> dict:
        """Search for completions; returns {found, aborted, searched[, reason]}.

        An instant arc oracle runs first (ring closures the DFS misses), then
        the staged search: plain running track (curves + straights) first --
        that closes almost every real gap within a few thousand nodes -- then
        one complete standard bridge plus plain track, then the whole box only
        if needed. Search effort scales every stage's node budget independently
        of the real-piece depth limit. A depth-first search over a BROAD
        inventory otherwise drowns exploring exotic-piece subtrees before
        finding the obvious answer.
        """
        if type(search_effort) is not int or not 1 <= search_effort <= 16:
            raise ValueError("search effort must be a whole number from 1 to 16")
        if type(max_pieces) is not int or not 1 <= max_pieces <= 128:
            raise ValueError("search depth must be a whole number from 1 to 128")
        if type(max_results) is not int or not 1 <= max_results <= 50:
            raise ValueError("max_results must be a whole number from 1 to 50")
        if type(slop) not in (int, float) or not math.isfinite(slop) or slop < 0:
            raise ValueError("slop must be a finite, non-negative number")
        if type(reversing) is not bool:
            raise ValueError("reversing must be a boolean")
        if grow is not None:
            grow = _end(grow, "grow")
        if close is not None:
            close = _end(close, "close")
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
        if self.layout.pose_of(grow).connects_to(self.layout.pose_of(close)):
            raise ValueError(
                "those ends already mate exactly; join them with Layout.join instead"
            )

        def publish(candidates: list[Solution], outcome: dict) -> dict:
            if cancel_check is not None:
                cancel_check(final=True)  # the last point at which it may stop
            # Candidate indices change even on unchanged geometry. Publish only
            # after all validation/search work succeeds: failed oracle, solver or
            # progress callbacks must leave revision and previous candidates alone.
            self._invalidate()
            self.candidates = candidates
            self._candidate_revision = self.revision
            return {**outcome, "search_effort": search_effort}

        remaining = self.remaining()
        reason = None if reversing else self._height_gap_reason(grow, close, remaining)
        if reason is not None:
            return publish([], {
                "found": 0,
                "aborted": False,
                "searched": 0,
                "complete": True,
                "stop_reason": "height_impossible",
                "max_pieces_searched": 0,
                "reason": reason,
            })

        if not reversing:
            arcs = self._arc_closures(grow, close, max_results, max_pieces)
            if arcs:
                return publish(arcs, {
                    "found": len(arcs), "aborted": False, "searched": 0,
                    "complete": False, "stop_reason": "heuristic",
                    "max_pieces_searched": max_pieces,
                })
        plain = {
            pid: n
            for pid, n in remaining.items()
            if pid in ("curve", "straight") and n > 0
        }
        full = {pid: n for pid, n in remaining.items() if n > 0}
        stages = [plain, full] if plain and plain != full else [full]

        searched = 0
        aborted = False
        candidates = []
        # One closing problem: every stage tries first the direction that
        # settled the previous one; reverse tables carry over between turns of a
        # stage, and between stages only where they share the stock.
        memo: dict = {}

        def stage_progress(nodes: int) -> None:
            if cancel_check is not None:
                cancel_check()
            if progress is not None:
                progress(searched + nodes)

        for stage_index, inventory in enumerate(stages):
            if inventory == full:
                bridge = bridge_completion(
                    self.layout, self.catalog, remaining, grow, close,
                    max_pieces=max_pieces, max_results=max_results,
                    max_nodes=250_000 * search_effort, progress=stage_progress,
                    memo=memo,
                )
                if bridge is not None:
                    searched += bridge.stats.nodes
                    if bridge.solutions:
                        return publish(bridge.solutions, {
                            "found": len(bridge.solutions), "searched": searched,
                            "aborted": bridge.stats.aborted, "complete": False,
                            "stop_reason": "bridge_search",
                            "max_pieces_searched": bridge.stats.max_pieces_searched,
                        })
            budget = 25_000 if stage_index == 0 and len(stages) > 1 else 60_000
            budget *= search_effort
            result = solve(
                inventory,
                self.catalog,
                SolverConfig(
                    slop=slop,
                    min_pieces=0,
                    max_pieces=max_pieces,
                    max_results=max_results,
                    max_nodes=budget,
                    reversing_loops=reversing and inventory == full,
                    progress=stage_progress,
                ),
                base=self.layout,
                grow_from=grow,
                close_onto=close,
                memo=memo,
            )
            searched += result.stats.nodes
            aborted = result.stats.aborted
            if result.solutions:
                candidates = result.solutions[:max_results]
                break
        return publish(candidates, {
            "found": len(candidates),
            "aborted": aborted,
            "searched": searched,
            "complete": result.stats.complete and inventory == full,
            "stop_reason": (result.stats.stop_reason if inventory == full else "staged_search"),
            "max_pieces_searched": result.stats.max_pieces_searched,
        })

    def _height_gap_reason(self, grow: End, close: End,
                           remaining: Mapping[str, int]) -> str | None:
        """Why no ordinary completion can join two ends at different heights, if so.

        Inventory alone bounds height only when no open preplaced junction route
        can change elevation for free. Use the same eligible stub ends as the core
        solver; defer to its conservative bounds otherwise.
        """
        dz = abs(float(self.layout.pose_of(grow).z) - float(self.layout.pose_of(close).z))
        if dz <= 1e-9:
            return None
        stub_ends = set(self.layout.connectable_ends()) - {grow, close}
        if any(
            placement.piece.ports[entry].pose.z != placement.piece.ports[exit_].pose.z
            for index, placement in enumerate(self.layout.placements)
            if placement.piece.is_junction
            for entry in range(len(placement.piece.ports))
            if (index, entry) in stub_ends
            for exit_, _route in placement.piece.transit(entry)
            if (index, exit_) in stub_ends
        ):
            return None
        lift = sum(
            max((abs(float(m.dz)) for m in _moves_for(self.catalog[pid])), default=0.0) * n
            for pid, n in remaining.items()
        )
        if dz <= lift + 1e-6:
            return None
        return (f"impossible: those ends differ by {dz:.0f} mm in height and the "
                f"remaining pieces can climb at most {lift:.0f} mm — the track up "
                "there can never come back down")

    def apply_candidate(self, index: int, revision: int | None = None) -> None:
        if self._candidate_revision != self.revision or (
            revision is not None and revision != self.revision
        ):
            raise ValueError("candidate is stale (solve again)")
        index = _index(index, "index")
        if not 0 <= index < len(self.candidates):
            raise ValueError("no such candidate (solve again)")
        chosen = self.candidates[index].layout
        used, remaining = self.layout.piece_counts, self.remaining()
        if any(n - used.get(pid, 0) > remaining.get(pid, 0)
               for pid, n in chosen.piece_counts.items()):
            raise ValueError("candidate exceeds the current inventory (solve again)")
        self._push(chosen, "apply completion")


# --------------------------------------------------------------------------------------
# Shared API dispatch
# --------------------------------------------------------------------------------------


class SearchCancelledError(ValueError):
    """A cooperative cancellation left the last confirmed session untouched."""


class UnknownRouteError(ValueError):
    """The editor API does not expose this route."""


class RevisionConflictError(ValueError):
    """The client is attempting to edit a state it has not seen."""


MUTATING_ROUTES = frozenset({
    "/api/attach", "/api/join", "/api/undo", "/api/remove", "/api/clear",
    "/api/inventory", "/api/unlimited", "/api/add_set", "/api/stone",
    "/api/solve", "/api/apply", "/api/import", "/api/restore", "/api/redo",
    "/api/project/open",
    *("/api/search/" + action for action in (
        "start", "tick", "page", "continue", "pause", "resume", "publish", "discard")),
    *("/api/routes/" + action for action in ("start", "tick", "pause", "resume", "discard")),
})


def dispatch_session(
    session: Session, path: str, body: object, progress: object = None,
    cancel_check: object = None,
) -> dict[str, Any]:
    """Shared HTTP/Pyodide API. Call with the session lock on threaded hosts."""
    if not isinstance(body, dict):
        raise ValueError("request body must be a JSON object")
    preview_format = body.get("preview_format")
    if preview_format is not None and preview_format != PREVIEW_FORMAT:
        raise ValueError("unsupported preview format")
    if path == "/api/state":
        return session.state(preview_format=preview_format)
    if path == "/api/export":
        return layout_to_dict(session.layout)
    if path not in MUTATING_ROUTES and path not in ("/api/check", "/api/drive"):
        raise UnknownRouteError(f"no route {path}")
    revision = body.get("revision")
    # The editor also names the engine instance it saw; older API clients may omit it.
    if (type(revision) is not int or revision != session.revision
            or body.get("instance", session.instance) != session.instance):
        raise RevisionConflictError(
            "The session changed in another tab, or this page is out of date. "
            "Your action was not applied. Review the refreshed layout and try again."
        )
    if path.startswith("/api/search/"):
        from .editor_search import dispatch_search

        return dispatch_search(session, path, body)
    if path.startswith("/api/routes/"):
        from .editor_routes import dispatch_routes

        return dispatch_routes(session, path, body)
    if path == "/api/attach":
        session.attach(body["piece"], body["entry"], body.get("at"))
    elif path == "/api/join":
        session.join(body["a"], body["b"])
    elif path == "/api/undo":
        session.undo()
    elif path == "/api/redo":
        session.redo()
    elif path == "/api/remove":
        session.remove_piece(body["placement"])
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
            body["placement"], str(body["id"]),
            body.get("at_port"), remove_only=body.get("remove", False),
        )
    elif path == "/api/solve":
        if cancel_check is not None:
            cancel_check()
        outcome = session.solve_gap(
            body.get("grow"), body.get("close"),
            body.get("slop", 0.0), body.get("max_results", 10),
            reversing=body.get("reversing", False), progress=progress,
            max_pieces=body.get("max_pieces", 26),
            search_effort=body.get("search_effort", 1), cancel_check=cancel_check,
        )
        return {**outcome, **session.state(preview_format=preview_format)}
    elif path == "/api/apply":
        session.apply_candidate(body["index"], body.get("revision"))
    elif path == "/api/import":
        session._push(layout_from_dict(body.get("data"), session.catalog), "import layout")
    elif path == "/api/restore":
        session.restore(body.get("data"), new_history=True)
    elif path == "/api/project/open":
        from .editor_tools import validate_project

        project = validate_project(body.get("data"), session.catalog)
        session.restore(project["session"])
        return {**session.state(preview_format=preview_format),
                "project": {"name": project["name"], "preferences": project["preferences"]}}
    elif path == "/api/check":
        from .editor_tools import check_session

        return check_session(session)
    elif path == "/api/drive":
        from .editor_tools import trace_train

        return trace_train(session, body.get("start"), body.get("max_steps", 10000),
                           switch_states=body.get("switch_states"))
    else:
        raise UnknownRouteError(f"no route {path}")
    return session.state(preview_format=preview_format)
