"""Editor benchmarks, including both orientations of the reported bridge gap.

Run PYTHONPATH=src python benchmarks/editor_completion.py --repeats 3.
Point PYTHONPATH at an older checkout to compare the same fixtures and settings.
Wall times are observations only; search-node counts are the regression contracts.
"""

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from statistics import median
from time import perf_counter, process_time

import duplotrain.gui as gui
from duplotrain import build_chain, default_catalog
from duplotrain.editor_search import SearchJob
from duplotrain.layout import layout_from_dict, layout_to_dict
from duplotrain.solver import _solution_overlaps


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    catalog = default_catalog()
    data = json.loads((Path(__file__).resolve().parents[1]
                       / "tests/fixtures/bridge-gap.json").read_text())
    bridge = layout_from_dict(data, catalog)
    cases = []
    for name, chain in (
        ("half_circle", ["curve"] * 6),
        ("winding_circle", ["curve"] * 2),
        ("mixed_gap", ["straight"] * 2 + ["curve"] * 4),
        ("half_built_bridge", ["curve"] * 6 + ["ramp"]),
    ):
        base = build_chain([(catalog[pid], 0, 1) for pid in chain])
        ends = base.connectable_ends()
        cases.append((name, base, ends[-1], ends[0], True, None))
    for unlimited in (False, True):
        for reverse in (False, True):
            ends = bridge.connectable_ends()
            grow, close = (ends[0], ends[1]) if reverse else (ends[1], ends[0])
            spare = {"curve": 16, "straight": 4, "ramp": 2, "span": 2}
            owned = dict(Counter(bridge.piece_counts) + Counter(spare))
            cases.append((f"reported_{'unlimited' if unlimited else 'finite'}"
                          f"_{'reverse' if reverse else 'forward'}",
                          bridge, grow, close, unlimited, owned))
    print(json.dumps({"source": gui.__file__, "repeats": args.repeats,
                      "max_pieces": 26, "max_results": 8, "slop": 0}))
    for name, base, grow, close, unlimited, owned in cases:
        timings = []
        cpu_timings = []
        for _ in range(args.repeats):
            session = gui.Session(history=[base], unlimited=unlimited,
                                  **({"inventory": owned} if owned is not None else {}))
            started = perf_counter()
            cpu_started = process_time()
            job = SearchJob(session, {"grow": grow, "close": close})
            while job.status == "running":
                job.tick()
            cpu_timings.append(process_time() - cpu_started)
            timings.append(perf_counter() - started)
            for candidate in job.solutions:
                assert candidate.layout.placements[:len(base)] == base.placements
                assert all(candidate.layout.links[a] == b for a, b in base.links.items())
                assert not candidate.layout.joint_issues()
                assert not _solution_overlaps(candidate.layout, 0, 120, 8)
        # The ordered exact layouts and signatures must agree across checkouts,
        # not merely the number of solutions. This is outside the timed region.
        evidence = [(layout_to_dict(s.layout), repr(s.signature), s.gap, s.exact, s.kind)
                    for s in job.solutions]
        digest = hashlib.sha256(json.dumps(evidence, sort_keys=True).encode()).hexdigest()
        print(json.dumps({"case": name, "seconds": round(median(timings), 4),
                          "cpu_seconds": round(median(cpu_timings), 4),
                          "solutions_sha256": digest,
                          "nodes": job.nodes, "found": len(job.solutions),
                          "added": [len(s.layout) - len(base) for s in job.solutions],
                          "stage": job.stage, "status": job.status}), flush=True)


if __name__ == "__main__":
    main()
