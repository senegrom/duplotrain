"""Read-only editor diagnostics, portable project validation and bounded train traces.

No report here changes track or substitutes for the solver's acceptance checks.
"""

from __future__ import annotations

import math
from collections import Counter
from dataclasses import asdict
from typing import TYPE_CHECKING, Any

from .catalog import ACCESSORIES
from .collision import DEFAULT_CLEARANCE, CollisionField, bounds_of
from .drive import DriveLimitError, _tongue_choices, drivable_universe, drive

if TYPE_CHECKING:
    from .editor import Session
    from .layout import Layout

PROJECT_FORMAT = "duplotrain-project/1"


def _number(value: object, low: float, high: float, name: str) -> float:
    if (type(value) not in (int, float) or not low <= value <= high
            or not math.isfinite(value)):
        raise ValueError(f"{name} must be a finite number from {low} to {high}")
    return float(value)


def validate_project(data: object, catalog) -> dict[str, Any]:
    """Validate preferences before the caller atomically restores the session."""
    if not isinstance(data, dict) or data.get("format") != PROJECT_FORMAT:
        raise ValueError("unrecognised project format")
    name = data.get("name")
    if not isinstance(name, str) or not 1 <= len(name.strip()) <= 80:
        raise ValueError("project name must contain 1–80 characters")
    session, prefs = data.get("session"), data.get("preferences", {})
    if not isinstance(session, dict) or session.get("format") != "duplotrain-session/1":
        raise ValueError("project must contain a session")
    if not isinstance(prefs, dict):
        raise ValueError("project preferences must be an object")
    result = {}
    if "view" in prefs:
        view = prefs["view"]
        if not isinstance(view, dict):
            raise ValueError("project view must be an object")
        result["view"] = {
            "x": _number(view.get("x"), -1e10, 1e10, "view x"),
            "y": _number(view.get("y"), -1e10, 1e10, "view y"),
            "scale": _number(view.get("scale"), 0.000001, 4, "view scale"),
        }
    if "search" in prefs:
        search = prefs["search"]
        if not isinstance(search, dict):
            raise ValueError("project search settings must be an object")
        pieces, reversing = search.get("max_pieces"), search.get("reversing")
        if type(pieces) is not int or not 1 <= pieces <= 128:
            raise ValueError("max_pieces must be an integer from 1 to 128")
        if type(reversing) is not bool:
            raise ValueError("reversing must be a boolean")
        result["search"] = {
            "max_pieces": pieces, "reversing": reversing,
            "slop": _number(search.get("slop"), 0, 1e9, "slop"),
        }
        if "options" in search:
            from .editor_search import search_options
            result["search"]["options"] = search_options(search["options"], catalog)
    return {"format": PROJECT_FORMAT, "name": name.strip(),
            "session": session, "preferences": result}


def check_session(session: Session) -> dict[str, Any]:
    """Report distinct connector, sampled-overlap and stock conditions.

    At most 200 overlap pairs are returned. Reaching that limit is explicitly
    incomplete, never a collision-free verdict. Accepted layouts already have
    a 1500-piece bound. Direct neighbours use the solver's existing exemption.
    """
    layout = session.layout
    opens = [list(end) for end in layout.connectable_ends()]
    joints = layout.joint_issues()
    neighbours: dict[int, set[int]] = {}
    for (a, _), (b, _) in layout.links.items():
        neighbours.setdefault(a, set()).add(b)
    overlaps = []
    clouds = []
    # Small layouts test every pair. On larger layouts the shared deferred field
    # indexes bounds to shortlist pairs, and the one-piece fields apply the same
    # narrow-phase predicates in the same pair order.
    spatial = CollisionField(clearance=DEFAULT_CLEARANCE) if len(layout) >= 128 else None
    complete = True
    for i, placement in enumerate(layout):
        points = placement.centreline_points(8.0)
        width = placement.piece.width / 2
        bounds = bounds_of(points)
        candidates = (spatial.nearby_placements(bounds, width)
                      if spatial is not None else range(len(clouds)))
        for j in candidates:
            if j in neighbours.get(i, ()):
                continue
            cloud = clouds[j]
            if cloud.near(bounds, width, set()) and cloud.clashes(
                points, width, set(), underpass=placement.piece.underpass,
            ):
                overlaps.append([j, i])
                if len(overlaps) >= 200:
                    complete = False
                    break
        if not complete:
            break
        cloud = CollisionField(clearance=DEFAULT_CLEARANCE)
        cloud.add(i, points, width, underpass=placement.piece.underpass)
        clouds.append(cloud)
        if spatial is not None:
            spatial.add_deferred(i, points, (0.0, 0.0, 0.0), width, bounds,
                                 underpass=placement.piece.underpass)
    used_stones = Counter(entry[1] for entry in layout.accessories)
    missing = []
    for used, owned, catalog in (
        (layout.piece_counts, session.inventory, session.catalog),
        (used_stones, session.stones, ACCESSORIES),
    ):
        for pid, count in used.items():
            have = owned.get(pid, 0)
            if count > have:
                info = catalog[pid]
                name = info.name if hasattr(info, "name") else info["name"]
                indices = ([i for i, p in enumerate(layout) if p.piece.id == pid]
                           if pid in session.catalog else
                           sorted({entry[0] for entry in layout.accessories if entry[1] == pid}))
                missing.append({"piece": pid, "name": name, "used": count,
                                "owned": have, "missing": count - have, "placements": indices})
    provisional = [i for i, p in enumerate(layout) if p.piece.provisional]
    return {"revision": session.revision, "open_ends": opens, "joint_issues": joints,
            "connector_closed": layout.is_closed and not joints,
            "overlaps": overlaps, "overlap_check_complete": complete,
            "missing": missing, "sandbox": session.unlimited, "provisional": provisional,
            "model_note": "Sampled model check (8 mm); not a physical-clearance guarantee."}


def switch_choices(layout: Layout) -> list[dict[str, Any]]:
    """The drive model's facing-port choices, not external connector links."""
    return [{"placement": index, "default": min(options),
             "options": [{"port": p, "name": layout.placements[index].piece.ports[p].name}
                         for p in sorted(options)]}
            for index, options in _tongue_choices(layout)]


def _initial_switches(layout: Layout, settings: object) -> dict[int, int]:
    choices = {c["placement"]: c for c in switch_choices(layout)}
    states = {i: c["default"] for i, c in choices.items()}
    if settings is None:
        return states
    if not isinstance(settings, dict):
        raise ValueError("initial switch choices must be an object")
    seen = set()
    for key, port in settings.items():
        # JSON object keys are strings; reject bools, floats and noncanonical
        # spellings rather than coercing them to another piece's switch.
        if type(key) is int:
            index = key
        elif isinstance(key, str) and key.isascii() and key.isdecimal() and len(key) <= 5:
            index = int(key)
            if str(index) != key:
                raise ValueError("invalid switch placement")
        else:
            raise ValueError("invalid switch placement")
        if index not in choices or index in seen:
            raise ValueError("pick a valid switch placement once")
        if type(port) is not int or port not in {p["port"] for p in choices[index]["options"]}:
            raise ValueError("pick a valid switch exit port")
        seen.add(index)
        states[index] = port
    return states


def trace_train(
    session: Session, start: object, max_steps: object = 10000, *, switch_states: object = None,
) -> dict[str, Any]:
    """One selected inward start and initial switches, never a universal claim."""
    from .editor import _end

    start = _end(start, "start")
    index, port = start
    layout = session.layout
    if not 0 <= index < len(layout):
        raise ValueError("pick a valid train starting piece")
    piece = layout.placements[index].piece
    if not 0 <= port < len(piece.ports) or port in piece.sealed:
        raise ValueError("pick an unsealed entry port for the train")
    if type(max_steps) is not int or not 1 <= max_steps <= 10000:
        raise ValueError("train trace limit must be 1–10000 steps")
    initial = _initial_switches(layout, switch_states)
    if layout.joint_issues():
        raise ValueError("Fix incompatible joints before testing the train")
    universe = drivable_universe(layout)
    common = {"revision": session.revision, "start": list(start),
              "initial_switch_states": initial, "total_pieces": len(layout),
              "drivable_count": len(universe), "terminal": None}
    try:
        report = drive(layout, start=start, switch_states=initial, max_steps=max_steps)
    except DriveLimitError:
        # No partial/unvisited coverage or terminal-position claim at the limit.
        return {**common, "outcome": "limit", "steps": [], "limit": max_steps,
                "complete": False, "visited": [], "visited_drivable": [],
                "unvisited": None, "cycle_pieces": [], "cycle_start": None, "period": None}
    cycle = (report.steps[report.cycle_start:] if report.cycle_start is not None else ())
    return {**common, "outcome": report.outcome,
            "steps": [list(step) for step in report.steps], "cycle_start": report.cycle_start,
            "period": report.period, "reversals": report.reversals,
            "visited": sorted(report.visited), "covers": report.visited >= universe,
            "visited_drivable": sorted(report.visited & universe),
            "unvisited": sorted(universe - report.visited),
            "cycle_pieces": sorted({step[0] for step in cycle}),
            "terminal": asdict(report.terminal) if report.terminal is not None else None,
            "final_switch_states": dict(report.final_switch_states), "complete": True}
