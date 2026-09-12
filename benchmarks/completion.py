"""Reproducible completion cases; run with PYTHONPATH=src python benchmarks/completion.py.

Use --lookahead 0 for the reference without lookahead, or run against an older
checkout via PYTHONPATH. Output includes the imported source path for that reason.
Wall times are observations, never test assertions.
"""

import argparse
import json

import duplotrain.solver as solver_module
from duplotrain import SolverConfig, build_chain, default_catalog, solve

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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lookahead", type=int, default=SolverConfig().completion_lookahead)
    parser.add_argument("--max-nodes", type=int, default=25_000)
    args = parser.parse_args()
    catalog = default_catalog()
    print(json.dumps({"source": solver_module.__file__, "lookahead": args.lookahead,
                      "max_nodes": args.max_nodes, "max_pieces": 20, "max_results": 8}))
    for name, chain, inventory, reversing in CASES:
        base = build_chain([(catalog[pid], 0, 1) for pid in chain])
        config = SolverConfig(min_pieces=0, max_pieces=20, max_results=8,
                              max_nodes=args.max_nodes, reversing_loops=reversing,
                              completion_lookahead=args.lookahead)
        ends = dict(grow_from=(0, 1), close_onto=(0, 0)) if chain[0] == "switch" else {}
        result = solve(inventory, catalog, config, base=base, **ends)
        print(json.dumps({
            "case": name, "nodes": result.stats.nodes, "found": len(result.solutions),
            "stop": result.stats.stop_reason, "seconds": round(result.stats.duration_s, 4),
            "max_pieces_searched": result.stats.max_pieces_searched,
            "completion_work": getattr(result.stats, "completion_work", None),
            "completion_bound_depth": getattr(result.stats, "completion_bound_depth", None),
            "completion_bound_states": getattr(result.stats, "completion_bound_states", None),
        }), flush=True)


if __name__ == "__main__":
    main()
