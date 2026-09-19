"""Read-only editor diagnostics, portable project validation and bounded train traces.

No report here changes track or substitutes for the solver's acceptance checks.
"""

from __future__ import annotations

import math
from collections import Counter
from typing import TYPE_CHECKING, Any

from .catalog import ACCESSORIES
from .collision import DEFAULT_CLEARANCE, CollisionField, bounds_of
from .drive import DriveLimitError, drive

if TYPE_CHECKING:
    from .editor import Session

PROJECT_FORMAT = "duplotrain-project/1"


def _number(value: object, low: float, high: float, name: str) -> float:
    if (type(value) not in (int, float) or not low <= value <= high
            or not math.isfinite(value)):
        raise ValueError(f"{name} must be a finite number from {low} to {high}")
    return float(value)


def validate_project(data: object) -> dict[str, Any]:
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
    complete = True
    for i, placement in enumerate(layout):
        points = [p for line in placement.centrelines(8.0) for p in line]
        width = placement.piece.width / 2
        bounds = bounds_of(points)
        for j, cloud in enumerate(clouds):
            if j in neighbours.get(i, ()):
                continue
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
            "connector_closed": bool(len(layout)) and layout.is_closed and not joints,
            "overlaps": overlaps, "overlap_check_complete": complete,
            "missing": missing, "sandbox": session.unlimited, "provisional": provisional,
            "model_note": "Sampled model check (8 mm); not a physical-clearance guarantee."}


def trace_train(session: Session, start: object, max_steps: object = 10000) -> dict[str, Any]:
    """One selected inward start and default switch tongues, not a universal claim."""
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
    if layout.joint_issues():
        raise ValueError("Fix incompatible joints before testing the train")
    try:
        report = drive(layout, start=start, max_steps=max_steps)
    except DriveLimitError:
        return {"revision": session.revision, "start": list(start), "outcome": "limit",
                "steps": [], "limit": max_steps, "complete": False}
    return {"revision": session.revision, "start": list(start), "outcome": report.outcome,
            "steps": [list(step) for step in report.steps], "cycle_start": report.cycle_start,
            "period": report.period, "reversals": report.reversals,
            "visited": sorted(report.visited), "covers": report.covers(layout),
            "final_switch_states": dict(report.final_switch_states), "complete": True}
