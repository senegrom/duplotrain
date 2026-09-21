"""Benchmark diagnostics and warm presentation responses, independently of search.

Run PYTHONPATH=src python benchmarks/editor_presentation.py --repeats 7.
Use the SAME script with PYTHONPATH pointing at an older checkout to compare.
Large scenes add widely separated closed rings to the reported completed bridge;
they are synthetic scaling cases, not additional user layouts or browser timings.
"""

import argparse
import hashlib
import json
from pathlib import Path
from statistics import median
from time import perf_counter

from duplotrain import build_chain, default_catalog
from duplotrain.collision import CollisionField
from duplotrain.editor import PREVIEW_FORMAT, Session
from duplotrain.editor_tools import check_session
from duplotrain.geometry import Pose
from duplotrain.layout import Layout, Placement, layout_from_dict


def expanded(base, rings):
    catalog = default_catalog()
    ring = build_chain([(catalog["curve"], 0, 1)] * 12).join((0, 0), (11, 1))
    placements, links = list(base.placements), dict(base.links)
    for i in range(rings):
        offset = len(placements)
        dx, dy = 5000 + 1200 * (i % 10), 1200 * (i // 10)
        placements.extend(Placement(p.piece, Pose(
            p.frame.x + dx, p.frame.y + dy, p.frame.z, p.frame.heading,
        )) for p in ring)
        links.update({(a[0] + offset, a[1]): (b[0] + offset, b[1])
                      for a, b in ring.links.items()})
    return Layout(tuple(placements), links, base.accessories)


def encoded(value):
    return json.dumps(value, separators=(",", ":"))


def timed(call, repeats):
    expected = call()  # untimed warm-up
    times = []
    for _ in range(repeats):
        start = perf_counter()
        result = call()
        times.append((perf_counter() - start) * 1000)
        assert result == expected
    return expected, median(times)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=7)
    parser.add_argument("--states-dir", type=Path, help="optional raw states for JS profiling")
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("repeats must be positive")
    catalog = default_catalog()
    fixtures = Path(__file__).resolve().parents[1] / "tests/fixtures"
    completed = layout_from_dict(json.loads((fixtures / "bridge-completed.json").read_text()),
                                 catalog)
    gap = layout_from_dict(json.loads((fixtures / "bridge-gap.json").read_text()), catalog)
    sessions = [(f"completed_{len(layout)}", Session(history=[layout], unlimited=True))
                for layout in (completed, expanded(completed, 38), expanded(completed, 118))]
    session = Session(history=[gap], unlimited=True)
    outcome = session.solve_gap(None, None, 0, 8, max_pieces=26)
    assert outcome["found"] == 8 and outcome["searched"] == 1878
    sessions.append(("gap_8_candidates", session))
    if args.states_dir:
        args.states_dir.mkdir(parents=True, exist_ok=True)
    for name, session in sessions:
        report, check_ms = timed(lambda session=session: check_session(session), args.repeats)
        body, state_ms = timed(lambda session=session: encoded(session.state(preview_format=PREVIEW_FORMAT)),
                               args.repeats)
        pair_checks, original = 0, CollisionField.near

        def counted(*a, original=original, **kw):
            nonlocal pair_checks
            pair_checks += 1
            return original(*a, **kw)

        # Instrumentation is outside timing, and never escapes this benchmark.
        CollisionField.near = counted
        try:
            assert check_session(session) == report
        finally:
            CollisionField.near = original
        if args.states_dir:
            (args.states_dir / f"{name}.json").write_text(body)
        print(encoded({"case": name, "pieces": len(session.layout),
                       "check_ms": check_ms, "state_ms": state_ms,
                       "pair_checks": pair_checks,
                       "report_sha256": hashlib.sha256(encoded(report).encode()).hexdigest(),
                       "state_sha256": hashlib.sha256(body.encode()).hexdigest(),
                       "compact_bytes": len(body.encode()),
                       "spaced_bytes": len(json.dumps(json.loads(body)).encode())}), flush=True)


if __name__ == "__main__":
    main()
