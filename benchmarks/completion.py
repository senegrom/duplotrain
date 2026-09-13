"""Reproducible completion cases; run with PYTHONPATH=src python benchmarks/completion.py.

Use --lookahead 0 for the reference without lookahead, or run against an older
checkout via PYTHONPATH. Output includes the imported source path for that reason.
Wall times are observations, never test assertions.
"""

import argparse
import hashlib
import json
from dataclasses import dataclass
from statistics import median

import duplotrain.solver as solver_module
from duplotrain import (
    ORIGIN,
    Layout,
    Pose,
    SolverConfig,
    build_chain,
    default_catalog,
    parse_piece,
    solve,
)

CASES = [
    ("half_circle", ["curve"] * 6, {"curve": 6, "straight": 4}, False),
    ("winding_circle", ["curve"] * 2, {"curve": 22, "straight": 8}, False),
    ("mixed_gap", ["straight"] * 2 + ["curve"] * 4, {"curve": 12, "straight": 6}, False),
    ("bridge_gap", ["curve"] * 6 + ["ramp"],
     {"curve": 6, "straight": 4, "ramp": 1, "span": 2}, False),
    ("bridge_full", ["curve"] * 6 + ["ramp"],
     {"curve": 18, "straight": 8, "ramp": 1, "span": 2, "switch": 2,
      "crossing": 1, "slope": 2, "level_crossing": 2}, True),
    ("mixed_full", ["straight"] * 2 + ["curve"] * 4,
     {"curve": 20, "straight": 6, "ramp": 2, "span": 2, "switch": 2,
      "crossing": 1, "slope": 2}, True),
    ("switch_tail", ["switch"], {"curve": 12, "straight": 4}, True),
    ("switch_full", ["switch"],
     {"curve": 12, "straight": 4, "switch": 1, "crossing": 1, "ramp": 2, "span": 2}, True),
    ("long_gap", ["straight"] * 4 + ["curve"] * 2, {"curve": 14, "straight": 8}, False),
]


@dataclass
class Case:
    name: str
    base: Layout
    inventory: dict
    reversing: bool = False
    slop: float = 0.0
    ends: dict | None = None
    suite: str = "exact"


def cases(catalog):
    """Fixed inputs shared by the timing runner and correctness regressions."""
    result = []
    for name, chain, inventory, reversing in CASES:
        base = build_chain([(catalog[pid], 0, 1) for pid in chain])
        ends = dict(grow_from=(0, 1), close_onto=(0, 0)) if chain[0] == "switch" else {}
        result.append(Case(name, base, inventory, reversing, ends=ends))
        # The same input with play enabled should still find its exact closures.
        if name in {"half_circle", "bridge_full", "mixed_full", "switch_full", "long_gap"}:
            for slop in (1.0, 5.0):
                result.append(Case(f"{name}_slop_{slop:g}", base, inventory, reversing,
                                   slop, ends, "slippage"))

    # Two disconnected halves of a circle: the selected ends differ by a 3-4-5 mm
    # translation. There are no pre-existing forced links to contaminate gap totals.
    first = build_chain([(catalog["curve"], 0, 1)] * 3)
    second = build_chain([(catalog["curve"], 0, 1)] * 3,
                         start=first.pose_of((2, 1)).then(3, 4, 0, 0))
    base = Layout(first.placements + second.placements,
                  {**first.links, **{(i + 3, p): (j + 3, q)
                                     for (i, p), (j, q) in second.links.items()}})
    for slop in (4.9, 5.0, 10.0):
        result.append(Case(f"offset_circle_slop_{slop:g}", base,
                           {"curve": 6, "straight": 4}, slop=slop,
                           ends=dict(grow_from=(5, 1), close_onto=(0, 0)), suite="slippage"))
    result.append(Case("offset_full_slop_5", base, dict(CASES[5][2]), reversing=True,
                       slop=5, ends=dict(grow_from=(5, 1), close_onto=(0, 0)), suite="slippage"))
    first = build_chain([(catalog["straight"], 0, 1)] * 3)
    second = build_chain([(catalog[pid], 0, 1) for pid in ("straight", "curve", "curve")],
                         start=first.pose_of((2, 1)).then(3, 4, 0, 0))
    base = Layout(first.placements + second.placements,
                  {**first.links, **{(i + 3, p): (j + 3, q)
                                     for (i, p), (j, q) in second.links.items()}})
    result.append(Case("offset_long_slop_5", base, {"curve": 14, "straight": 8}, slop=5,
                       ends=dict(grow_from=(5, 1), close_onto=(0, 0)), suite="slippage"))

    # Climb through a preplaced junction, spending 1 mm at entry and 2 mm at exit.
    catalog["ramp_switch"] = parse_piece({"id": "ramp_switch", "width": 64, "paths": [
        {"segments": [{"type": "ramp", "run": 128, "rise": 64}]},
        {"segments": [{"type": "arc", "radius": 256, "degrees": 30}]},
    ]})
    base, _junction = Layout().with_piece(catalog["ramp_switch"], ORIGIN)
    base, left = base.with_piece(catalog["straight"], Pose.make(x=-129))
    base, right = base.with_piece(catalog["straight"], Pose.make(x=130, z=64))
    for slop in (2.9, 3.0):
        result.append(Case(f"transit_slop_{slop:g}", base, {}, slop=slop,
                           ends=dict(grow_from=(left, 1), close_onto=(right, 0)),
                           suite="slippage"))

    catalog["fine"] = parse_piece({"id": "fine", "paths": [{"segments": [
        {"type": "arc", "radius": "1537/3", "degrees": 15},
    ]}]})
    base = build_chain([(catalog["fine"], 0, 1)] * 20)
    result.append(Case("fifteen_degree_slop_1", base, {"fine": 4, "straight": 2},
                       slop=1.0, suite="slippage"))
    return result


def result_digest(result):
    """Order-sensitive fingerprint; compare layouts separately in regression tests."""
    values = [(s.signature, s.kind, s.exact, s.gap) for s in result.solutions]
    return hashlib.sha256(repr(values).encode()).hexdigest()[:16]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lookahead", type=int, default=SolverConfig().completion_lookahead)
    parser.add_argument("--max-nodes", type=int, default=25_000)
    parser.add_argument("--repeats", type=int, default=1, help="report the median of N searches")
    parser.add_argument("--suite", choices=("exact", "slippage", "all"), default="all")
    parser.add_argument("--case", action="append", help="run only this case (repeatable)")
    parser.add_argument("--engine", choices=("auto", "lattice", "field"), default="auto")
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    catalog = default_catalog()
    selected = cases(catalog)
    if args.case:
        unknown = set(args.case) - {case.name for case in selected}
        if unknown:
            parser.error(f"unknown cases: {', '.join(sorted(unknown))}")
    selected = [case for case in selected
                if (args.suite == "all" or case.suite == args.suite)
                and (not args.case or case.name in args.case)]
    if not selected:
        parser.error("no cases selected")
    print(json.dumps({"source": solver_module.__file__, "lookahead": args.lookahead,
                      "max_nodes": args.max_nodes, "max_pieces": 20, "max_results": 8,
                      "repeats": args.repeats, "engine": args.engine, "suite": args.suite}))
    for case in selected:
        config = SolverConfig(min_pieces=0, max_pieces=20, max_results=8,
                              max_nodes=args.max_nodes, reversing_loops=case.reversing,
                              slop=case.slop, engine=args.engine,
                              completion_lookahead=args.lookahead)
        times = []
        digests = set()
        for _ in range(args.repeats):
            result = solve(case.inventory, catalog, config, base=case.base, **(case.ends or {}))
            times.append(result.stats.duration_s)
            digests.add(result_digest(result))
        if len(digests) != 1:
            raise RuntimeError(f"non-deterministic results for {case.name}")
        print(json.dumps({
            "case": case.name, "slop_mm": case.slop, "engine": result.stats.engine,
            "inventory": case.inventory, "reversing": case.reversing,
            "nodes": result.stats.nodes, "found": len(result.solutions),
            "forced": sum(not s.exact for s in result.solutions),
            "gaps_mm": [round(s.gap, 9) for s in result.solutions],
            "result_digest": next(iter(digests)),
            "stop": result.stats.stop_reason, "seconds": round(median(times), 4),
            "seconds_min": round(min(times), 4), "seconds_max": round(max(times), 4),
            "pruned_completion": result.stats.pruned_completion,
            "max_pieces_searched": result.stats.max_pieces_searched,
            "completion_work": getattr(result.stats, "completion_work", None),
            "completion_bound_depth": getattr(result.stats, "completion_bound_depth", None),
            "completion_bound_states": getattr(result.stats, "completion_bound_states", None),
            "completion_checks": getattr(result.stats, "completion_checks", None),
            "completion_cache_hits": getattr(result.stats, "completion_cache_hits", None),
        }), flush=True)


if __name__ == "__main__":
    main()
