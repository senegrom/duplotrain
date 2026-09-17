"""Collision broad-phase scaling without changing the completion problem.

Run with PYTHONPATH=src, or point it at a previous checkout's src to compare.
Remote closed circles are synthetic stress geometry, not the user's original scene.
Timing is native Python (not browser timing); every candidate is independently audited.
"""

import argparse
import json
import platform
from pathlib import Path
from statistics import median
from time import perf_counter

import duplotrain.collision as collision
from duplotrain import Pose, build_chain, default_catalog
from duplotrain.gui import Session
from duplotrain.layout import Layout, layout_from_dict
from duplotrain.solver import _solution_overlaps


def scene(extra_loops):
    catalog = default_catalog()
    base = layout_from_dict(json.loads((Path(__file__).resolve().parents[1]
                                       / "tests/fixtures/bridge-gap.json").read_text()), catalog)
    ends = base.connectable_ends()
    for i in range(extra_loops):
        remote = build_chain([(catalog["curve"], 0, 1)] * 12,
                             start=Pose.make(4000 + (i % 8) * 1024, 1500 + (i // 8) * 1024))
        remote = remote.join((0, 0), (11, 1))
        offset = len(base)
        links = {**base.links, **{(a[0] + offset, a[1]): (b[0] + offset, b[1])
                                 for a, b in remote.links.items()}}
        base = Layout(base.placements + remote.placements, links, base.accessories)
    assert base.connectable_ends() == ends
    return base, ends[-1], ends[0]


def run(base, grow, close):
    session = Session(history=[base], unlimited=True)
    started = perf_counter()
    outcome = session.solve_gap(grow, close, 0.0, 8)
    elapsed = perf_counter() - started
    assert len(session.candidates) == 8
    for candidate in session.candidates:
        layout = candidate.layout
        assert len(layout) - len(base) == 24
        assert layout.placements[:len(base)] == base.placements
        assert all(layout.links[a] == b for a, b in base.links.items())
        assert layout.is_closed and not layout.joint_issues()
        assert not _solution_overlaps(layout, 0, 120.0, 8.0)
    return elapsed, outcome


def bound_work(base, grow, close):
    """Separate untimed run; count clouds sent to the exact AABB rejection test."""
    name = "_near_clouds" if hasattr(collision.CollisionField, "_near_clouds") else "near"
    original = getattr(collision.CollisionField, name)
    total = 0

    def measured(field, bounds, half, *args):
        nonlocal total
        result = original(field, bounds, half, *args)
        total += len(result) if name == "_near_clouds" else len(field._clouds)
        return result

    setattr(collision.CollisionField, name, measured)
    try:
        run(base, grow, close)
    finally:
        setattr(collision.CollisionField, name, original)
    return total


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--extra-loops", type=int, nargs="+", default=[0, 10, 40])
    parser.add_argument("--count-bounds", action="store_true")
    args = parser.parse_args()
    if args.repeats < 1 or any(n < 0 or n > 100 for n in args.extra_loops):
        parser.error("use positive repeats and 0-100 extra loops")
    print(json.dumps({"source": collision.__file__, "python": platform.python_version(),
                      "repeats": args.repeats, "max_pieces": 26, "max_results": 8,
                      "slop": 0, "inventory": "unlimited"}), flush=True)
    for loops in args.extra_loops:
        base, grow, close = scene(loops)
        times = []
        for _ in range(args.repeats):
            elapsed, outcome = run(base, grow, close)
            times.append(elapsed)
        row = {"base_pieces": len(base), "synthetic_extra_loops": loops,
               "seconds": round(median(times), 4), "nodes": outcome["searched"],
               "found": outcome["found"]}
        if args.count_bounds:
            row["bounds_considered"] = bound_work(base, grow, close)
        print(json.dumps(row), flush=True)


if __name__ == "__main__":
    main()
