"""Bounded interactive completion jobs, independent of the saved editor content.

A job owns suspended exact solver generators; ticks only advance those generators.
Candidates are checked against the job's base, stock, size, joints and room before
they leave the job. Each candidate's final placements are audited for overlaps
exactly once, by whatever produced them: the core search's final overlap audit,
the arc oracle, or, for an expanded bridge macro, before it counts as a result. No
candidate event is an edit: publication/application remains revision checked and
atomic.
"""
from __future__ import annotations

import json
import math
import time
import uuid
from collections import Counter
from dataclasses import dataclass, replace
from functools import lru_cache
from typing import Any

from .bridge_completion import _BRIDGE_ID, _bridge, _expand
from .collision import DEFAULT_CLEARANCE
from .layout import _BRIDGE_JOINT, Layout, layout_to_dict
from .solver import (
    SearchLimits,
    Solution,
    SolverConfig,
    _OverlapAudit,
    _placeable_stock,
    _solution_overlaps,
    _walk_ends,
    solve_steps,
)
from .symmetry import placement_key
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
    keep = data.get("keep_out")
    if keep is None:  # like a null room: no restriction
        keep = []
    if not isinstance(keep, list):
        raise ValueError("keep-out rectangles must be a list")
    if len(keep) > 32:
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
            xs, ys = [x for x, _, _ in line], [y for _, y, _ in line]
            x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
            if room is not None and (x0 - pad < room[0] or y0 - pad < room[1]
                                     or x1 + pad > room[2] or y1 + pad > room[3]):
                return False
            for r in keep:
                box = (r[0] - pad, r[1] - pad, r[2] + pad, r[3] + pad)
                if x1 < box[0] or x0 > box[2] or y1 < box[1] or y0 > box[3]:
                    continue  # the line's extent cannot reach this rectangle
                if any(_segment_box(a, b, box) for a, b in zip(line, line[1:], strict=False)):
                    return False
    return True


def physical_key(layout, base):
    """Identity of the track *layout* adds to *base*, which it extends unchanged.

    Reversing a symmetric piece can change its frame and port numbering without
    changing its shape. Conversely, equal connector poses can bound different
    paths of an asymmetric piece. Use the solver's exact path/route/kind identity,
    and keep links to the unchanged base distinguished by their original indices.
    The base's own links and stones are common to every extension and left out.
    """
    placements, start = layout.placements, len(base)

    def end(placement, port):
        return (placement, port) if placement < start else placements[placement].port_pose(port)

    pieces = Counter(map(_piece_identity, placements[start:]))
    links = frozenset(frozenset((end(*a), end(*b))) for a, b in layout.links.items()
                      if a not in base.links)
    return frozenset(pieces.items()), links


@lru_cache(maxsize=4096)
def _piece_identity(placement):
    """One added piece's identity: candidates of one search share their placements."""
    return placement.piece.id, placement_key(placement.piece, placement.frame)


def valid_extension(base, candidate, stock, max_pieces, options, *, audit=None):
    """Acceptance checks of one candidate over *base*.

    *base* already fits the room and keep-out limits: a job checks its layout
    once, and the partial bases of a plan consist of accepted additions. So only
    the added placements are checked against them.
    *audit*, the problem's shared overlap auditor, is for geometry nobody audited
    yet: an expanded bridge macro. Every other producer already audited exactly
    these placements with the same clearance and spacing.
    """
    layout, base_counts = candidate.layout, base.piece_counts
    if (layout.placements[:len(base)] != base.placements
            or any(layout.links.get(a) != b for a, b in base.links.items())
            or layout.accessories != base.accessories
            or len(layout) - len(base) > max_pieces
            or any(n - base_counts.get(pid, 0) > stock.get(pid, 0)
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
    budget: int  # the stage's node budget at search effort 1
    overhead: int = 0
    nodes: int = 0
    blocked: bool = False
    exhausted: bool = False
    cut: bool = False  # a walk too long for the recursion limit: no bound lifts it
    expand: Any = None
    direction: int = 0  # 0 grows from the chosen end, 1 from the other one

    def advance(self):
        try:
            event = next(self.iterator)
        except StopIteration as done:
            self.exhausted = True
            if done.value is not None:
                self.nodes = done.value.stats.nodes
            return {"kind": "exhausted"}
        self.nodes = event.get("nodes", self.nodes)
        if event["kind"] == "node_limit":
            if self.limits.max_nodes < self.cap:
                self.limits.max_nodes = min(self.cap, max(self.nodes + 1, self.nodes * 2))
            else:
                self.blocked = True
        elif event["kind"] in ("piece_limit", "result_limit"):
            self.blocked = True
        elif event["kind"] == "walk_limit":
            # No bound lifts the cut: the suspended search can only repeat it.
            self.blocked = self.cut = True
            self.close()
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
        self.base, self.catalog, self.stock = base, catalog, stock
        self.depth, self.effort = depth, effort
        self.grow, self.close_end = grow, close
        self.cursors: list[Cursor] = []
        self.active = 0
        self.arc_session = None  # the arc templates' session, built when they run
        self.slop, self.reversing, self.options = slop, reversing, options
        # One overlap auditor of the base, built when first needed, serves the arc
        # templates and the bridge stage's expanded macros (new geometry).
        self.audit = None
        # A search allowing reversing loops skips the arc templates: its
        # ordinary stages then find the same closures first.
        self.arc = iter(()) if reversing else self._templates()
        self.arc_done = False
        self._build()

    def _auditor(self):
        if self.audit is None:
            self.audit = _OverlapAudit(self.base, DEFAULT_CLEARANCE, 8.0)
        return self.audit

    def _templates(self):
        # A generator, so that the session is built when the first template is asked for.
        if self.arc_session is None:
            from .editor import Session

            self.arc_session = Session(catalog=dict(self.catalog), history=[self.base],
                                       inventory={pid: n + self.base.piece_counts.get(pid, 0)
                                                  for pid, n in self.stock.items()})
        yield from self.arc_session._arc_events(self.grow, self.close_end, MAX_RESULTS,
                                                self.depth, auditor=self._auditor)

    @property
    def nodes(self):
        return sum(c.nodes for c in self.cursors)

    def _build(self):
        base, catalog, stock = self.base, self.catalog, self.stock
        plain = {pid: n for pid, n in stock.items() if pid in ("curve", "straight") and n}
        # The solver drops pieces no walk can place: with those alone beside plain
        # track, a plain stage would search the full stage's problem.
        full = _placeable_stock(stock, catalog, base, _walk_ends(base, self.grow, self.close_end))
        stages = []
        if plain and plain != full:
            stages.append(("plain track", plain, catalog, 25_000, 0, None))
        bridge = _bridge(catalog)
        floor = base.floor(catalog.values())
        if (bridge is not None and stock.get("ramp", 0) >= 2
                and stock.get("span", 0) >= 2
                and base.pose_of(self.grow).z == floor and base.pose_of(self.close_end).z == floor):
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

                expand = None  # only a bridge stage's macro becomes its parts
                if parts is not None:
                    def expand(sol, parts=parts):
                        return replace(sol, layout=_expand(sol.layout, parts), steps=(),
                                       signature=("standard_bridge", sol.signature))

                def accept(sol, expand=expand):
                    if expand is None:
                        return valid_extension(base, sol, stock, self.depth, self.options)
                    return valid_extension(base, expand(sol), stock, self.depth, self.options,
                                           audit=self._auditor())

                # The limits bound nodes, results and depth; max_nodes still sizes
                # the reverse tables' base allowance.
                iterator = solve_steps(inventory, pieces,
                    SolverConfig(min_pieces=0, max_nodes=cap, slop=self.slop,
                                 reversing_loops=reversing, solution_filter=accept),
                    base=base, grow_from=grow, close_onto=close, limits=limits)
                self.cursors.append(Cursor(iterator, limits, name, cap, budget, overhead,
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
        # A direction running out of search proves that the reversed problem has
        # nothing more, and the full inventory's that no stage has: the others
        # search subsets of its stock and moves. Those are settled, whatever stopped
        # them. A piece limit keeps the opposite suspended stack for a raised bound.
        # Either way this direction goes first in the next stage.
        if event["kind"] in ("piece_limit", "exhausted"):
            settled = (self.cursors if event["kind"] == "exhausted"
                       and cursor.stage == "full inventory" else stage)
            for peer in settled:
                if peer is cursor:
                    continue
                if event["kind"] == "exhausted":
                    peer.close()
                    peer.exhausted, peer.blocked, peer.cut = True, False, False
                else:
                    peer.blocked = True
            left = [i for i, c in enumerate(self.cursors) if not c.blocked and not c.exhausted]
            if left:
                first_stage = self.cursors[left[0]].stage
                self.active = next((i for i in left if self.cursors[i].stage == first_stage
                                    and self.cursors[i].direction == cursor.direction), left[0])
        elif event["kind"] in ("node_limit", "result_limit", "walk_limit"):
            left = [i for i, c in enumerate(self.cursors) if not c.blocked and not c.exhausted]
            other = next((i for i in left if i != self.active
                          and self.cursors[i].stage == cursor.stage), None)
            if other is not None:
                self.active = other
            elif self.active in left:
                pass  # a stage's last direction runs until its own limits stop it
            elif left:
                self.active = next((i for i in left if i != self.active), left[0])
        # A single cursor stopping is not a whole-problem exhaustion verdict.
        if event["kind"] == "exhausted":
            event = {"kind": "progress"}
        return {**event, "stage": cursor.stage}

    def harder(self):
        old_depth = self.depth
        self.depth, self.effort = _harder(self.depth, self.effort)
        for cursor in self.cursors:
            if cursor.exhausted or cursor.cut:
                continue
            cursor.cap = min(cursor.cap * 2, cursor.budget * 16)
            # The doubling turns go on: the two ends of an exact stage still take
            # turns, now within the raised budget.
            cursor.limits.max_nodes = max(cursor.limits.max_nodes,
                                          min(cursor.cap, cursor.nodes * 2))
            cursor.limits.max_pieces = max(1, self.depth - cursor.overhead)
            # A direction stopped at its result limit (repeats of one track from
            # the other end, say) resumes too.
            cursor.limits.max_results *= 2
            cursor.blocked = bool(cursor.overhead and self.depth < 4)
        if self.depth > old_depth:
            if hasattr(self.arc, "close"):
                self.arc.close()
            self.arc = iter(()) if self.reversing else self._templates()
            self.arc_done = False
        self.active = 0

    def close(self):
        if hasattr(self.arc, "close"):
            self.arc.close()
        for cursor in self.cursors:
            cursor.close()
        self.cursors.clear()
        self.arc_session = self.audit = None


def _meeting_ends_joined(layout):
    """*layout* with its exactly meeting ends joined, as a plan joins them."""
    for a, b in layout.matable_pairs():
        try:
            layout = layout.join(a, b)
        except ValueError:
            pass  # a third end at the same point: the first pair joined keeps it
    return layout


def _harder(depth, effort):
    """Search harder: twice the depth and the effort, up to 128 pieces and 16."""
    return min(128, depth * 2), min(16, effort * 2)


def _cost(goal, sol, base, stock, catalog):
    """*goal*'s cost of candidate *sol* over *base*; the lower ranks first."""
    base_counts = base.piece_counts
    added = {pid: n - base_counts.get(pid, 0) for pid, n in sol.layout.piece_counts.items()}
    if goal == "pieces":
        return sum(added.values())
    if goal == "footprint":
        w, h = sol.layout.size()
        return w * h
    if goal == "scarce":
        return sum(n / max(1, stock.get(pid, 0)) for pid, n in added.items())
    if goal == "junctions":
        return sum(n for pid, n in added.items() if catalog[pid].is_junction)
    if goal == "bridges":
        return sum(n for pid, n in added.items() if catalog[pid].category == "bridge")
    return 0


def _ranked(solutions, goal, costs, base, stock, catalog):
    """Exact candidates first, then *goal*'s cost, then the order found.

    *costs* holds the costs already computed, one per solution index.
    """
    costs.extend(_cost(goal, sol, base, stock, catalog) for sol in solutions[len(costs):])
    return sorted(enumerate(solutions),
                  key=lambda item: (not item[1].exact, costs[item[0]], item[0]))


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
        # Every candidate keeps the base's placements, links and stones, which
        # passed the save check when they were committed: _saveable checks the rest.
        self.spare_bytes = MAX_SNAPSHOT_BYTES - len(
            json.dumps(snapshot, ensure_ascii=True).encode("utf-8"))
        self.options = search_options(body.get("options"), self.catalog)
        for pid in self.options["exclude"]:
            self.stock[pid] = 0
        self.depth = integer(body.get("max_pieces", 26), 1, 128, "max_pieces")
        self.effort = 1  # Search harder raises it
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
            if grow is None and close is None:
                if len(opens) != 2:
                    raise ValueError("pick two open ends, or use Close all gaps")
                grow, close = opens[-1], opens[0]
            grow, close = _end(grow, "grow"), _end(close, "close")
            if grow == close or grow not in opens or close not in opens:
                raise ValueError("pick two distinct open ends")
        if any(issue["problems"] != ["planar gap"] for issue in self.base.joint_issues()):
            raise ValueError("Fix incompatible existing joints before starting this search")
        # Close all gaps would join every pair of meeting ends: they must be able to.
        for a, b in (self.base.meeting_pairs() if self.all_gaps else ()):
            if not self.base._kinds_mate(a, b):
                raise ValueError(f"Pieces #{a[0] + 1} and #{b[0] + 1} meet but cannot join "
                                 f"({_BRIDGE_JOINT}); move one before closing all gaps")
        # A plan must be overlap-free as a whole, which no addition can make it.
        if self.all_gaps and _solution_overlaps(_meeting_ends_joined(self.base), 0,
                                                DEFAULT_CLEARANCE, 8.0):
            raise ValueError("The existing track overlaps itself; Check layout lists the "
                             "pieces. Fix it before closing all gaps")
        if not fits_space(self.base, self.options):
            raise ValueError(
                "Existing track crosses the room/keep-out limits; no pieces were moved")
        self.solutions: list[Solution] = []
        # Why nothing, or not everything, found is offered: an impossibility proof,
        # or closures beyond the save limits.
        self.reason: str | None = None
        self.keys: set = set()
        self.unsaveable = False  # a closure was found too large to save
        self.costs: dict[str, list] = {}  # per ranking goal, one per solution index
        self.last_touch = time.monotonic()
        self.status = "running"
        self.stage = "templates"
        self.complete = False
        self.multi_nodes = 0
        self.multi_cap = 335_000 * self.effort
        self.pool = self.multi = None  # a refusal or a direct join starts no search
        if self.all_gaps and (reason := session._joint_gap_reason(opens, self.stock)):
            self.reason, self.status, self.complete = reason, "exhausted", True
            self.stage = "joint check"
        elif self.all_gaps:
            self.stage = f"close all: {len(opens)} open ends left"
            self.multi = self._all_gaps(self.base, self.stock, self.depth)
        elif self.base.pose_of(grow).connects_to(self.base.pose_of(close)):
            closed = self.base.join(grow, close)
            self._accept(Solution(closed, (), 0, True, len(closed.connectable_ends()), ("join",)))
            self.status, self.stage = "direct_join", "direct join"
        elif not reversing and (reason := session._joint_gap_reason((grow, close), self.stock)):
            self.reason, self.status, self.complete = reason, "exhausted", True
            self.stage = "joint check"
        elif not reversing and (reason := session._height_gap_reason(grow, close, self.stock)):
            self.reason, self.status, self.complete = reason, "exhausted", True
            self.stage = "height check"
        else:
            self.pool = PairSearch(self.base, self.catalog, self.stock, grow, close,
                                   self.depth, self.effort, slop, reversing, self.options)
            if reversing:  # the arc templates do not run
                self.stage = self.pool.cursors[0].stage

    @property
    def nodes(self):
        return self.multi_nodes if self.all_gaps else self.pool.nodes if self.pool else 0

    def _accept(self, candidate):
        # Its producer has checked the extension already: a pair search's stage or
        # template, each addition of a Close-all plan, or the exact direct join.
        # The same track found from either end is one alternative.
        key = physical_key(candidate.layout, self.base)
        if key in self.keys:
            return
        if not self._saveable(candidate.layout):
            # Not offered, but it exists: the search proves nothing impossible.
            self.unsaveable = True
            self.reason = ("Some closures would make the session too large to save "
                           f"({MAX_PLACEMENTS:,} pieces or 2 MB); they are not offered.")
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
        if len(layout) > MAX_PLACEMENTS:
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
        base_counts = base.piece_counts
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
                    yield {"kind": "progress",
                           "stage": f"close all: {len(opens)} open ends left"}
                    if event["kind"] in ("limited", "exhausted"):
                        break
                    if event["kind"] != "solution":
                        continue
                    candidate = event["solution"]
                    key = physical_key(candidate.layout, base)
                    if key in seen or len(candidate.layout.connectable_ends()) >= len(opens):
                        continue
                    seen.add(key)
                    used = {pid: n - base_counts.get(pid, 0)
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
            else:  # a job that runs has a pair search or a plan search
                event = self.pool.step()
            self.stage = event.get("stage", self.stage)
            if event["kind"] == "solution":
                self._accept(event["solution"])
                if len(self.solutions) >= self.target:
                    self.status = "results_ready"
                    break
            elif event["kind"] in ("limited", "exhausted"):
                self.status = event["kind"]
                self.complete = (not self.all_gaps and event["kind"] == "exhausted"
                                 and not self.unsaveable)
                break
            if time.perf_counter() >= deadline:
                break
        # From the live cursors at every stop, results found included: a settlement
        # may have covered a cut walk since an earlier stop.
        if self.status != "running" and self.pool and not self.unsaveable:
            self.reason = ("Some walks pass through more existing junctions than a "
                           "search can follow; closures along them were not searched."
                           if any(c.cut for c in self.pool.cursors) else None)

    def more(self, *, harder=False):
        if not harder and self.status in ("limited", "bounded_complete", "exhausted"):
            return  # a larger result quota does not lift an exhausted work/depth limit
        if self.pool is None and (not self.all_gaps or self.complete):
            return  # a direct join or an impossibility proof has no search to continue
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
                self.depth, self.effort = _harder(self.depth, self.effort)
                self.multi_cap = self.multi_nodes + 335_000 * self.effort
                self.multi = self._all_gaps(self.base, self.stock, self.depth)
            self.complete = False
        self.target = min(MAX_RESULTS, max(self.target * 2, len(self.solutions) + 8))
        self.status = "running"

    def ordered(self):
        # Solutions are only ever appended: each cost is computed once per goal.
        goal = self.options["sort"]
        return _ranked(self.solutions, goal, self.costs.setdefault(goal, []),
                       self.base, self.stock, self.catalog)

    def response(self, session, body):
        if "sort" in body:  # validated by dispatch_search
            self.options["sort"] = body["sort"]
        page = integer(body.get("page", 0), 0, 6, "page")
        shown = []
        for index, candidate in self.ordered()[page * 8:(page + 1) * 8]:
            item = session._candidate_json(index, candidate)
            item["revision"] = item["preview"]["base_revision"] = self.revision
            shown.append(item)
        return {"job_id": self.id, "revision": self.revision, "status": self.status,
                "stage": self.stage, "searched": self.nodes, "found": len(self.solutions),
                "page": page, "sort": self.options["sort"], "candidates": shown,
                "complete": self.complete, "reason": self.reason,
                "options": {"room": list(self.options["room"]) if self.options["room"] else None,
                            "keep_out": [list(r) for r in self.options["keep_out"]]},
                "max_pieces": self.depth,
                # A harder search needs room to report, limits left to raise and
                # something left to search: not every direction exhausted or cut short.
                "can_harden": (len(self.solutions) < MAX_RESULTS
                               and (self.depth, self.effort) != _harder(self.depth, self.effort)
                               and (self.all_gaps and not self.complete
                                    or (self.pool is not None and not all(
                                        c.exhausted or c.cut for c in self.pool.cursors)))),
                "resumable": len(self.solutions) < MAX_RESULTS and self.status not in (
                    "exhausted", "bounded_complete", "direct_join", "limited")}

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
        if self.multi is not None:
            self.multi.close()
        self.status = "discarded"
        self.solutions.clear()
        self.keys.clear()
        self.costs.clear()


def published_page(session, body):
    """A page of the suggestions a search published, ranked as the search ranks them.

    They outlive the search, which a train analysis replaces and inactivity
    expires, until the next edit or search. The session's layout and remaining
    stock are the search's base and stock; the stock differs only in excluded
    pieces, which no suggestion adds, so every cost is the search's.
    """
    goal = body.get("sort", "discovery")
    page = integer(body.get("page", 0), 0, 6, "page")
    ranked = _ranked(session.candidates, goal, [], session.layout, session.remaining(),
                     session.catalog)
    shown = [session._candidate_json(index, candidate)
             for index, candidate in ranked[page * 8:(page + 1) * 8]]
    return {"revision": session.revision, "status": "published",
            "found": len(session.candidates), "page": page, "sort": goal,
            "candidates": shown}


def job_action(session, job, action, expired):
    """The steps every interactive job shares; whether *action* was one of them.

    A job idle for MAX_JOB_SECONDS is released and the request fails with the
    message *expired*; any other request keeps the job alive. A failed tick
    releases the job too.
    """
    if time.monotonic() - job.last_touch > MAX_JOB_SECONDS:
        job.close()
        session._interactive_job = None
        raise ValueError(expired)
    job.last_touch = time.monotonic()
    if action == "tick":
        try:
            job.tick()
        except Exception:
            job.close()
            session._interactive_job = None
            raise
    elif action == "pause":
        if job.status == "running":
            job.status = "paused"
    elif action == "resume":
        if job.status == "paused":
            job.status = "running"
    else:
        return False
    return True


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
        active = isinstance(old, SearchJob) and old.revision == session.revision
        if not active or body.get("job_id") != old.id:
            # The search is gone; what it published stays until the next edit.
            if action == "page" and not active and (
                    session._candidate_revision == session.revision):
                return published_page(session, body)
            raise ValueError("This search is no longer active; start a new search")
        job = old
        if job_action(session, job, action,
                      "Search expired after 20 minutes of inactivity; start again"):
            pass  # tick, pause or resume
        elif action == "continue":
            job.more(harder=body.get("harder", False))
        elif action == "publish":
            job.publish(session)
            # The state leaves out the full list: the editor shows the job's page, and
            # the engine still holds every exact layout.
            return {**session.state(include_candidates=False),
                    "search_job": job.response(session, body)}
        elif action != "page":
            raise ValueError("unknown search job action")
    return job.response(session, body)
