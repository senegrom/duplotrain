"""Bounded interactive completion jobs, independent of the saved editor content.

A job owns suspended exact solver generators; ticks only advance those generators.
Candidates are checked against the job's base, stock, size, joints and room before
they leave the job. Each candidate's final placements are audited for overlaps
exactly once, by whatever produced them: the core search's replay audit, the arc
oracle, or, for an expanded bridge macro, before it counts as a result. No
candidate event is an edit: publication/application remains revision checked and
atomic.
"""
from __future__ import annotations

import hashlib
import json
import math
import time
import uuid
from collections import Counter
from dataclasses import dataclass, replace
from typing import Any

from .bridge_completion import _BRIDGE_ID, _bridge, _expand
from .collision import DEFAULT_CLEARANCE
from .exact import ZERO
from .layout import Layout, layout_to_dict
from .solver import (
    SearchLimits,
    Solution,
    SolverConfig,
    _OverlapAudit,
    _solution_overlaps,
    solve_steps,
)
from .validation import MAX_LINKS, MAX_PLACEMENTS, MAX_SNAPSHOT_BYTES, check_layout_json

MAX_RESULTS = 50
MAX_JOB_SECONDS = 1200
SORTS = ("discovery", "pieces", "footprint", "scarce", "junctions", "bridges")


def integer(value, low, high, name):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f"{name} must be an integer from {low} to {high}")
    return value


def rectangle(value):
    if (not isinstance(value, (list, tuple)) or len(value) != 4
            or any(type(v) not in (int, float) or not math.isfinite(v) or abs(v) > 1e7
                   for v in value) or value[0] >= value[2] or value[1] >= value[3]):
        raise ValueError("a rectangle must be [xmin,ymin,xmax,ymax] in mm with positive area")
    return tuple(float(v) for v in value)


def search_options(data, catalog):
    """Validate optional goals without mutating the user's owned inventory."""
    if data is None:
        data = {}
    if not isinstance(data, dict):
        raise ValueError("search options must be an object")
    unknown = set(data) - {"sort", "exclude", "room", "keep_out"}
    if unknown:
        raise ValueError("unknown search options")
    sort = data.get("sort", "discovery")
    if sort not in SORTS:
        raise ValueError("unknown candidate sort order")
    exclude = data.get("exclude", [])
    if (not isinstance(exclude, list) or len(exclude) > len(catalog)
            or any(not isinstance(pid, str) or pid not in catalog for pid in exclude)):
        raise ValueError("excluded pieces must be catalogue identifiers")
    keep = data.get("keep_out", [])
    if not isinstance(keep, list) or len(keep) > 32:
        raise ValueError("use at most 32 keep-out rectangles")
    return {"sort": sort, "exclude": sorted(set(exclude)),
            "room": rectangle(data["room"]) if data.get("room") is not None else None,
            "keep_out": [rectangle(r) for r in keep]}


def _segment_box(a, b, box):
    """Closed segment against a closed 2D box, including boundary contact."""
    low, high = 0.0, 1.0
    for axis in (0, 1):
        delta = b[axis] - a[axis]
        if delta == 0:
            if not box[axis] <= a[axis] <= box[axis + 2]:
                return False
        else:
            u, v = (box[axis] - a[axis]) / delta, (box[axis + 2] - a[axis]) / delta
            low, high = max(low, min(u, v)), min(high, max(u, v))
            if low > high:
                return False
    return True


def fits_space(layout, options):
    """Conservative sampled *width-inclusive* floor footprint, at every elevation.

    Rectangles are floor-to-ceiling restrictions, not collision-rule replacements.
    Sampling at 4mm and padding by half that interval conservatively covers the
    path between samples. This may reject borderline fits; it never moves track.
    """
    room, keep = options["room"], options["keep_out"]
    if room is None and not keep:
        return True
    for placement in layout:
        pad = placement.piece.width / 2 + placement.piece.end_overhang + 2.000001
        for line in placement.centrelines(4.0):
            if not math.isfinite(pad) or any(not math.isfinite(v) for point in line for v in point):
                return False
            if room is not None and any(
                x - pad < room[0] or y - pad < room[1]
                or x + pad > room[2] or y + pad > room[3] for x, y, _ in line
            ):
                return False
            for r in keep:
                box = (r[0] - pad, r[1] - pad, r[2] + pad, r[3] + pad)
                if (any(_segment_box(a, b, box) for a, b in zip(line, line[1:], strict=False))
                        or (len(line) == 1 and _segment_box(line[0], line[0], box))):
                    return False
    return True


def layout_key(layout):
    """Exact anchored layout identity, independent of placement emission order."""
    data = layout_to_dict(layout)
    order = sorted(range(len(data["placements"])), key=lambda i: json.dumps(
        data["placements"][i], sort_keys=True, separators=(",", ":")))
    remap = {old: new for new, old in enumerate(order)}
    links = []
    for a, ap, b, bp in data["links"]:
        left, right = sorted(((remap[a], ap), (remap[b], bp)))
        links.append((*left, *right))
    # Accessories on the unchanged base also follow the reindexing. Their saved
    # representation is not assumed here; exact full tuples are normalized.
    stones = sorted(((remap[entry[0]], *entry[1:]) for entry in layout.accessories),
                    key=lambda entry: json.dumps(entry, separators=(",", ":")))
    normal = {"placements": [data["placements"][i] for i in order],
              "links": sorted(links), "accessories": stones}
    return hashlib.sha256(json.dumps(normal, sort_keys=True, separators=(",", ":"))
                          .encode()).hexdigest()


def physical_key(layout, start=0):
    """Identity of the track from placement *start* on, over a shared prefix.

    Connectors have no gender: a piece placed from its other end has another
    frame and port order but lies in the same place. So a piece is its id with
    the set of its world connector poses, and a link joins two such poses or a
    connector of the shared prefix, named by index.
    """
    placements = layout.placements

    def end(placement, port):
        return (placement, port) if placement < start else placements[placement].port_pose(port)

    pieces = Counter((p.piece.id, frozenset(map(p.port_pose, range(len(p.piece.ports)))))
                     for p in placements[start:])
    links = frozenset(frozenset((end(*a), end(*b))) for a, b in layout.links.items())
    return frozenset(pieces.items()), links, layout.accessories


def valid_extension(base, candidate, stock, max_pieces, options, *, audit=None):
    """Acceptance checks of one candidate over *base*.

    *base* already fits the room and keep-out limits: a job checks its layout
    once, and the partial bases of a plan consist of accepted additions. So only
    the added placements are checked against them.
    *audit*, the problem's shared overlap auditor, is for geometry nobody audited
    yet: an expanded bridge macro. Every other producer already audited exactly
    these placements with the same clearance and spacing.
    """
    layout = candidate.layout
    if (layout.placements[:len(base)] != base.placements
            or any(layout.links.get(a) != b for a, b in base.links.items())
            or layout.accessories != base.accessories
            or len(layout) - len(base) > max_pieces
            or any(n - base.piece_counts.get(pid, 0) > stock.get(pid, 0)
                   for pid, n in layout.piece_counts.items())
            or not fits_space(layout.placements[len(base):], options)):
        return False
    # Audit only the joints the candidate adds: the base's own, deliberate forced
    # fits among them, are not the candidate's claim.
    new_issues = Layout(layout.placements, {a: b for a, b in layout.links.items()
                                            if a not in base.links}).joint_issues()
    if (any(issue["problems"] != ["planar gap"] for issue in new_issues)
            or (new_issues and candidate.exact)
            or sum(issue["gap_mm"] for issue in new_issues) > candidate.gap + 1e-6):
        return False
    return audit is None or not audit.overlaps(layout)


@dataclass
class Cursor:
    iterator: Any
    limits: SearchLimits
    stage: str
    cap: int
    overhead: int = 0
    nodes: int = 0
    depth: int = 0
    blocked: bool = False
    exhausted: bool = False
    expand: Any = None
    direction: int = 0  # 0 grows from the chosen end, 1 from the other one

    def advance(self):
        try:
            event = next(self.iterator)
        except StopIteration as done:
            self.exhausted = True
            if done.value is not None:
                self.nodes = done.value.stats.nodes
                self.depth = done.value.stats.max_pieces_searched
            return {"kind": "exhausted"}
        self.nodes = event.get("nodes", self.nodes)
        self.depth = event.get("depth", self.depth)
        if event["kind"] == "node_limit":
            if self.limits.max_nodes < self.cap:
                self.limits.max_nodes = min(self.cap, max(self.nodes + 1, self.nodes * 2))
            else:
                self.blocked = True
        elif event["kind"] in ("piece_limit", "result_limit"):
            self.blocked = True
        elif event["kind"] == "solution" and self.expand is not None:
            event = {**event, "solution": self.expand(event["solution"])}
        return event

    def close(self):
        self.iterator.close()
        self.expand = None


class PairSearch:
    """Resumable, alternating-end stages of one closing search."""

    def __init__(self, base, catalog, stock, grow, close, depth, effort, slop, reversing,
                 options):
        from .editor import Session

        self.base, self.catalog, self.stock = base, catalog, stock
        self.depth, self.effort = depth, effort
        self.grow, self.close_end = grow, close
        self.cursors: list[Cursor] = []
        self.active = 0
        self.arc_session = Session(catalog=dict(catalog), history=[base], inventory={
            pid: n + base.piece_counts.get(pid, 0) for pid, n in stock.items()
        })
        # A search allowing reversing loops skips the arc templates: its
        # ordinary stages then find the same closures first.
        self.arc = (iter(()) if reversing else
                    self.arc_session._arc_events(grow, close, MAX_RESULTS, depth))
        self.arc_done = False
        self.slop, self.reversing, self.options = slop, reversing, options
        # Expanded bridge macros are new geometry: audit them before they count.
        self.audit = _OverlapAudit(base, DEFAULT_CLEARANCE, 8.0)
        self._build()

    @property
    def nodes(self):
        return sum(c.nodes for c in self.cursors)

    def _build(self):
        base, catalog, stock = self.base, self.catalog, self.stock
        plain = {pid: n for pid, n in stock.items() if pid in ("curve", "straight") and n}
        full = {pid: n for pid, n in stock.items() if n}
        stages = []
        if plain and plain != full:
            stages.append(("plain track", plain, catalog, 25_000, 0, None))
        bridge = _bridge(catalog)
        if (bridge is not None and stock.get("ramp", 0) >= 2
                and stock.get("span", 0) >= 2
                and base.pose_of(self.grow).z == ZERO and base.pose_of(self.close_end).z == ZERO):
            macro, parts = bridge
            stages.append(("standard bridge", {**plain, _BRIDGE_ID: 1},
                           {**catalog, _BRIDGE_ID: macro}, 250_000, 3, parts))
        stages.append(("full inventory", full, catalog, 60_000, 0, None))
        for name, inventory, pieces, budget, overhead, parts in stages:
            # Plain and bridge stages look for ordinary closures; only the full
            # inventory also searches reversing ones. Forced fits and reversing
            # closures are not direction-equivalent: those stages grow from the
            # chosen end only.
            reversing = self.reversing and name == "full inventory"
            directions = [(self.grow, self.close_end)]
            if not self.slop and not reversing:
                directions.append((self.close_end, self.grow))
            for direction, (grow, close) in enumerate(directions):
                cap = budget * self.effort
                limits = SearchLimits(min(1024, cap), MAX_RESULTS, max(1, self.depth - overhead))

                def expand(sol, parts=parts):
                    if parts is None:
                        return sol
                    return replace(sol, layout=_expand(sol.layout, parts), steps=(),
                                   signature=("standard_bridge", sol.signature))

                def accept(sol, expand=expand, parts=parts):
                    sol = expand(sol)
                    if parts is not None and any(
                        p.frame.z != ZERO for p in sol.layout.placements[len(base):]
                        if p.piece.id in ("curve", "straight", "ramp")
                    ):
                        return False
                    return valid_extension(base, sol, stock, self.depth, self.options,
                                           audit=self.audit if parts is not None else None)

                iterator = solve_steps(inventory, pieces,
                    SolverConfig(min_pieces=0, max_pieces=limits.max_pieces,
                                 max_results=MAX_RESULTS, max_nodes=cap, slop=self.slop,
                                 reversing_loops=reversing,
                                 solution_filter=accept),
                    base=base, grow_from=grow, close_onto=close, limits=limits)
                self.cursors.append(Cursor(iterator, limits, name, cap, overhead,
                                           blocked=bool(overhead and self.depth < 4),
                                           expand=expand, direction=direction))

    def step(self):
        if not self.arc_done:
            try:
                candidate = next(self.arc)
                if candidate is not None and valid_extension(
                    self.base, candidate, self.stock, self.depth, self.options
                ):
                    return {"kind": "solution", "solution": candidate, "stage": "templates"}
                return {"kind": "progress", "stage": "templates"}
            except StopIteration:
                self.arc_done = True
        available = [i for i, c in enumerate(self.cursors) if not c.blocked and not c.exhausted]
        if not available:
            return {"kind": "limited" if any(c.blocked for c in self.cursors) else "exhausted"}
        if self.active not in available:
            self.active = available[0]
        cursor = self.cursors[self.active]
        stage = [c for c in self.cursors if c.stage == cursor.stage]
        remaining_budget = cursor.cap - sum(c.nodes for c in stage)
        if remaining_budget <= 0:
            for c in stage:
                c.blocked = True
            return {"kind": "progress", "stage": cursor.stage}
        cursor.limits.max_nodes = min(cursor.limits.max_nodes, cursor.nodes + remaining_budget)
        event = cursor.advance()
        # One exact direction exhausting a contour proves the reversed problem
        # has no further candidates at that bound. Keep the opposite suspended
        # stack for a raised bound, and try this successful direction first in
        # the next stage.
        if event["kind"] in ("piece_limit", "exhausted"):
            for peer in stage:
                if peer is cursor:
                    continue
                if event["kind"] == "exhausted":
                    peer.close()
                    peer.exhausted = True
                else:
                    peer.blocked = True
            left = [i for i, c in enumerate(self.cursors) if not c.blocked and not c.exhausted]
            if left:
                first_stage = self.cursors[left[0]].stage
                self.active = next((i for i in left if self.cursors[i].stage == first_stage
                                    and self.cursors[i].direction == cursor.direction), left[0])
        elif event["kind"] in ("node_limit", "result_limit"):
            left = [i for i, c in enumerate(self.cursors) if not c.blocked and not c.exhausted]
            other = next((i for i in left if i != self.active
                          and self.cursors[i].stage == cursor.stage), None)
            if other is not None:
                self.active = other
            elif len(stage) == 1 and self.active in left:
                pass  # a one-direction stage runs until its own limits stop it
            elif left:
                self.active = next((i for i in left if i != self.active), left[0])
        # A single cursor stopping is not a whole-problem exhaustion verdict.
        if event["kind"] == "exhausted":
            event = {"kind": "progress"}
        return {**event, "stage": cursor.stage}

    def harder(self):
        old_depth = self.depth
        self.depth, self.effort = min(128, self.depth * 2), min(16, self.effort * 2)
        for cursor in self.cursors:
            if cursor.exhausted:
                continue
            cursor.cap = min(cursor.cap * 2, (250_000 if cursor.overhead else
                              25_000 if cursor.stage == "plain track" else 60_000) * 16)
            cursor.limits.max_nodes = cursor.cap
            cursor.limits.max_pieces = max(1, self.depth - cursor.overhead)
            cursor.blocked = bool(cursor.overhead and self.depth < 4)
        if self.depth > old_depth:
            if hasattr(self.arc, "close"):
                self.arc.close()
            self.arc = (iter(()) if self.reversing else self.arc_session._arc_events(
                self.grow, self.close_end, MAX_RESULTS, self.depth))
            self.arc_done = False
        self.active = 0

    def close(self):
        if hasattr(self.arc, "close"):
            self.arc.close()
        for cursor in self.cursors:
            cursor.close()
        self.cursors.clear()
        self.arc_session = self.audit = None


class SearchJob:
    def __init__(self, session, body):
        from .editor import _end

        self.id = uuid.uuid4().hex
        self.revision = session.revision
        self.base, self.catalog = session.layout, dict(session.catalog)
        self.stock = session.remaining()
        snapshot = session.snapshot()
        self.snapshot_metadata = {key: value for key, value in snapshot.items()
                                  if key != "layout"}
        # Every candidate keeps the base's placements, links and stones: the base's
        # snapshot is checked once here, and _saveable checks only the rest.
        try:
            session._check_snapshot(snapshot)
        except ValueError:
            self.spare_bytes = -1  # nothing that extends an unsaveable base is saveable
        else:
            self.spare_bytes = MAX_SNAPSHOT_BYTES - len(
                json.dumps(snapshot, ensure_ascii=True).encode("utf-8"))
        self.options = search_options(body.get("options"), self.catalog)
        for pid in self.options["exclude"]:
            self.stock[pid] = 0
        self.depth = integer(body.get("max_pieces", 26), 1, 128, "max_pieces")
        self.effort = integer(body.get("search_effort", 1), 1, 16, "search effort")
        self.target = integer(body.get("max_results", 8), 1, MAX_RESULTS, "max_results")
        slop, reversing = body.get("slop", 0), body.get("reversing", False)
        if type(slop) not in (int, float) or not math.isfinite(slop) or not 0 <= slop <= 1e9:
            raise ValueError("slop must be finite and non-negative")
        if type(reversing) is not bool or type(body.get("all_gaps", False)) is not bool:
            raise ValueError("reversing and all_gaps must be booleans")
        self.all_gaps = body.get("all_gaps", False)
        opens = self.base.connectable_ends()
        if self.all_gaps:
            if slop or reversing:
                raise ValueError("Close all gaps currently requires exact, non-reversing joins")
            if len(opens) < 2 or len(opens) > 10:
                raise ValueError("Close all gaps requires 2–10 open ends")
        else:
            grow, close = body.get("grow"), body.get("close")
            if grow is None or close is None:
                if len(opens) != 2:
                    raise ValueError("pick two open ends, or use Close all gaps")
                grow, close = opens[-1], opens[0]
            grow, close = _end(grow, "grow"), _end(close, "close")
            if grow == close or grow not in opens or close not in opens:
                raise ValueError("pick two distinct open ends")
        issues = self.base.joint_issues()
        if (any(issue["problems"] != ["planar gap"] for issue in issues)
                or (self.all_gaps and issues)):
            raise ValueError("Fix incompatible existing joints before starting this search")
        # A plan must be overlap-free as a whole, which no addition can make it.
        if self.all_gaps and _solution_overlaps(self.base, 0, DEFAULT_CLEARANCE, 8.0):
            raise ValueError("The existing track overlaps itself; Check layout lists the "
                             "pieces. Fix it before closing all gaps")
        if not fits_space(self.base, self.options):
            raise ValueError(
                "Existing track crosses the room/keep-out limits; no pieces were moved")
        self.solutions: list[Solution] = []
        self.reason: str | None = None  # a proof that no ordinary completion exists
        self.keys: set = set()
        # Per solution index, computed when first shown or ranked.
        self.ids: dict[int, str] = {}
        self.costs: dict[str, list] = {}
        self.last_touch = time.monotonic()
        self.status = "running"
        self.stage = "templates"
        self.complete = False
        self.multi_nodes = 0
        self.multi_cap = 335_000 * self.effort
        self.pool = None
        if self.all_gaps:
            self.multi = self._all_gaps(self.base, self.stock, self.depth)
        elif self.base.pose_of(grow).connects_to(self.base.pose_of(close)):
            closed = self.base.join(grow, close)
            self._accept(Solution(closed, (), 0, True, len(closed.connectable_ends()), ("join",)))
            self.status = "direct_join"
        elif not reversing and (reason := session._height_gap_reason(grow, close, self.stock)):
            self.reason, self.status, self.complete = reason, "exhausted", True
        else:
            self.pool = PairSearch(self.base, self.catalog, self.stock, grow, close,
                                   self.depth, self.effort, slop, reversing, self.options)

    @property
    def nodes(self):
        return self.multi_nodes if self.all_gaps else self.pool.nodes if self.pool else 0

    def _accept(self, candidate):
        # Its producer has checked the extension already: a pair search's stage or
        # template, each addition of a Close-all plan, or the exact direct join.
        # The same track found from either end is one alternative.
        key = physical_key(candidate.layout, len(self.base))
        if key in self.keys or not self._saveable(candidate.layout):
            return
        self.keys.add(key)
        self.solutions.append(candidate)

    def _saveable(self, layout):
        """Session._check_snapshot's verdict on an extension of the checked base.

        A streamed candidate must be importable and applicable under the save and
        import guards: never offer an unsaveable plan. The guards check each entry
        on its own, so only the added placements and links need checking, with the
        totals; the size of what they add bounds the growth of the snapshot.
        """
        if self.spare_bytes < 0 or len(layout) > MAX_PLACEMENTS:
            return False
        links = self.base.links
        added = layout_to_dict(Layout(layout.placements[len(self.base):]))["placements"]
        rows = [[*a, *b] for a, b in layout.links.items() if a < b and a not in links]
        try:
            check_layout_json({"format": "duplotrain-layout/1", "placements": added,
                               "links": rows})
        except ValueError:
            return False
        if len(links) // 2 + len(rows) > MAX_LINKS:
            return False
        # Each addition adds its JSON and one separator to the base's snapshot.
        if len(json.dumps([added, rows], ensure_ascii=True).encode("utf-8")) <= self.spare_bytes:
            return True
        from .editor import Session

        try:  # near the size limit: the full check decides
            Session._check_snapshot({**self.snapshot_metadata, "layout": layout_to_dict(layout)})
        except ValueError:
            return False
        return True

    def _all_gaps(self, base, stock, slots):
        """Try complete pair alternatives, debit stock, then backtrack on failure."""
        opens = base.connectable_ends()
        if not opens:
            yield {"kind": "solution", "solution": Solution(base, (), 0, True, 0, ("all_gaps",))}
            return
        # Most constrained end first: fewest plausible mates within remaining reach.
        def distance(a, b):
            pa, pb = base.pose_of(a), base.pose_of(b)
            return math.hypot(float(pa.x - pb.x), float(pa.y - pb.y))
        span = sum(n * max((math.hypot(float(p.pose.x), float(p.pose.y))
                           for p in self.catalog[pid].ports), default=0)
                   for pid, n in stock.items() if n)
        grow = min(opens, key=lambda a: (sum(distance(a, b) <= span + 1e-6
                                             for b in opens if b != a), a))
        for close in sorted((b for b in opens if b != grow), key=lambda b: (distance(grow, b), b)):
            if base.pose_of(grow).connects_to(base.pose_of(close)):
                try:
                    joined = base.join(grow, close)
                except ValueError:
                    continue  # coincident but catalogue-incompatible connectors
                yield from self._all_gaps(joined, stock, slots)
                continue
            if slots <= 0:
                continue
            pair = PairSearch(base, self.catalog, stock, grow, close, slots, self.effort, 0,
                              False, self.options)
            seen = set()
            try:
                while len(seen) < 8:
                    while self.multi_nodes >= self.multi_cap:
                        yield {"kind": "limited"}
                    before = pair.nodes
                    event = pair.step()
                    self.multi_nodes += pair.nodes - before
                    yield {"kind": "progress", "stage": f"close all: {len(opens)} open ends"}
                    if event["kind"] in ("limited", "exhausted"):
                        break
                    if event["kind"] != "solution":
                        continue
                    candidate = event["solution"]
                    key = physical_key(candidate.layout, len(base))
                    if key in seen or len(candidate.layout.connectable_ends()) >= len(opens):
                        continue
                    seen.add(key)
                    used = {pid: n - base.piece_counts.get(pid, 0)
                            for pid, n in candidate.layout.piece_counts.items()}
                    remaining = {pid: n - used.get(pid, 0) for pid, n in stock.items()}
                    yield from self._all_gaps(candidate.layout, remaining,
                                              slots - (len(candidate.layout) - len(base)))
            finally:
                pair.close()

    def tick(self):
        if self.status != "running":
            return
        deadline = time.perf_counter() + 0.02
        for _ in range(32):
            if self.all_gaps:
                try:
                    event = next(self.multi)
                except StopIteration:
                    self.status = "bounded_complete"
                    break
            elif self.pool:
                event = self.pool.step()
            else:
                break
            self.stage = event.get("stage", self.stage)
            if event["kind"] == "solution":
                self._accept(event["solution"])
                if len(self.solutions) >= self.target:
                    self.status = "results_ready"
                    break
            elif event["kind"] in ("limited", "exhausted"):
                self.status = event["kind"]
                self.complete = not self.all_gaps and event["kind"] == "exhausted"
                break
            if time.perf_counter() >= deadline:
                break

    def more(self, *, harder=False):
        if not harder and self.status in ("limited", "bounded_complete", "exhausted"):
            return  # a larger result quota does not lift an exhausted work/depth limit
        if self.pool is None and not self.all_gaps:
            return  # a direct zero-piece join has no suspended search frontier
        if len(self.solutions) >= MAX_RESULTS:
            self.status = "result_cap"
            return
        if harder:
            if self.pool:
                self.pool.harder()
                self.depth, self.effort = self.pool.depth, self.pool.effort
            else:
                # New depth contours of multi-gap orchestration are a new bounded
                # plan search; ordinary DFS resumes at its saved exact checkpoint.
                self.multi.close()
                self.depth = min(128, self.depth * 2)
                self.effort = min(16, self.effort * 2)
                self.multi_cap = self.multi_nodes + 335_000 * self.effort
                self.multi = self._all_gaps(self.base, self.stock, self.depth)
            self.complete = False
        self.target = min(MAX_RESULTS, max(self.target * 2, len(self.solutions) + 8))
        if self.status != "exhausted" or harder:
            self.status = "running"

    def _cost(self, goal, sol):
        added = {pid: n - self.base.piece_counts.get(pid, 0)
                 for pid, n in sol.layout.piece_counts.items()}
        if goal == "pieces":
            return sum(added.values())
        if goal == "footprint":
            w, h = sol.layout.size()
            return w * h
        if goal == "scarce":
            return sum(n / max(1, self.stock.get(pid, 0)) for pid, n in added.items())
        if goal == "junctions":
            return sum(n for pid, n in added.items() if self.catalog[pid].is_junction)
        if goal == "bridges":
            return sum(n for pid, n in added.items() if self.catalog[pid].category == "bridge")
        return 0

    def ordered(self):
        # Solutions are only ever appended: each cost is computed once per goal.
        goal = self.options["sort"]
        costs = self.costs.setdefault(goal, [])
        costs.extend(self._cost(goal, sol) for sol in self.solutions[len(costs):])
        return sorted(enumerate(self.solutions),
                      key=lambda item: (not item[1].exact, costs[item[0]], item[0]))

    def response(self, session, body):
        if "sort" in body:
            if body["sort"] not in SORTS:
                raise ValueError("unknown candidate sort order")
            self.options["sort"] = body["sort"]
        page = integer(body.get("page", 0), 0, 6, "page")
        shown = []
        for index, candidate in self.ordered()[page * 8:(page + 1) * 8]:
            item = session._candidate_json(index, candidate,
                                           preview_format=body.get("preview_format"))
            item["revision"] = self.revision
            if "base_revision" in item["preview"]:  # a compact preview
                item["preview"]["base_revision"] = self.revision
            if index not in self.ids:
                self.ids[index] = layout_key(candidate.layout)
            item["candidate_id"] = self.ids[index]
            shown.append(item)
        return {"job_id": self.id, "revision": self.revision, "status": self.status,
                "stage": self.stage, "searched": self.nodes, "found": len(self.solutions),
                "target": self.target, "page": page, "candidates": shown,
                "complete": self.complete, "optimal": False, "reason": self.reason,
                "options": {"sort": self.options["sort"],
                            "exclude": list(self.options["exclude"]),
                            "room": list(self.options["room"]) if self.options["room"] else None,
                            "keep_out": [list(r) for r in self.options["keep_out"]]},
                "scope": "best among found candidates; no global optimum guaranteed",
                "max_pieces": self.depth, "search_effort": self.effort,
                # At the result cap a harder search would have no room to report.
                "can_harden": ((self.pool is not None or self.all_gaps)
                               and len(self.solutions) < MAX_RESULTS),
                "resumable": self.status not in (
                    "exhausted", "bounded_complete", "result_cap", "direct_join", "limited")}

    def publish(self, session):
        session._interactive_job = None
        session._invalidate()
        session.candidates = list(self.solutions)
        session._candidate_revision = session.revision
        self.revision = session.revision
        if self.status == "running":
            self.status = "paused"
        session._interactive_job = self

    def close(self):
        if self.pool:
            self.pool.close()
        if self.all_gaps and hasattr(self, "multi"):
            self.multi.close()
        self.status = "discarded"
        self.solutions.clear()
        self.keys.clear()
        self.ids.clear()
        self.costs.clear()


def dispatch_search(session, path, body):
    """Caller has validated the request revision and holds the session lock."""
    action = path.removeprefix("/api/search/")
    # Reject invalid presentation/control fields before replacing/publishing a job.
    integer(body.get("page", 0), 0, 6, "page")
    if "sort" in body and body["sort"] not in SORTS:
        raise ValueError("unknown candidate sort order")
    if type(body.get("harder", False)) is not bool:
        raise ValueError("harder must be a boolean")
    old = session._interactive_job
    if action == "start":
        job = SearchJob(session, body)  # validate before replacing prior search
        if old is not None:
            old.close()
        session._interactive_job = job
        # This job's previews carry the current revision, as the last published
        # suggestions do: withdraw those, so an index names only this job's.
        session.candidates, session._candidate_revision = [], None
    else:
        if (not isinstance(old, SearchJob) or body.get("job_id") != old.id
                or old.revision != session.revision):
            raise ValueError("This search is no longer active; start a new search")
        job = old
        if time.monotonic() - job.last_touch > MAX_JOB_SECONDS:
            job.close()
            session._interactive_job = None
            raise ValueError("Search expired after 20 minutes of inactivity; start again")
        job.last_touch = time.monotonic()
        if action == "tick":
            try:
                job.tick()
            except Exception:
                job.close()
                session._interactive_job = None
                raise
        elif action == "continue":
            job.more(harder=body.get("harder", False))
        elif action == "pause":
            if job.status == "running":
                job.status = "paused"
        elif action == "resume":
            if job.status == "paused":
                job.status = "running"
        elif action == "publish":
            job.publish(session)
            return {**session.state(preview_format=body.get("preview_format")),
                    "search_job": job.response(session, body)}
        elif action == "discard":
            job.close()
            session._interactive_job = None
            return {"discarded": True, "revision": session.revision}
        elif action != "page":
            raise ValueError("unknown search job action")
    return job.response(session, body)
