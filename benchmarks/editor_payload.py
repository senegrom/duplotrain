"""Measure state serialization and preview payloads, excluding solver work.

Run PYTHONPATH=src python benchmarks/editor_payload.py --repeats 7.
Times are native Python observations, not browser or network-transfer timings.
"""

import argparse
import json
from pathlib import Path
from statistics import median
from time import perf_counter

from duplotrain.catalog import default_catalog
from duplotrain.editor import PREVIEW_FORMAT, Session
from duplotrain.editor_search import SearchJob
from duplotrain.layout import layout_from_dict


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=7)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("repeats must be positive")
    fixture = Path(__file__).resolve().parents[1] / "tests/fixtures/bridge-gap.json"
    base = layout_from_dict(json.loads(fixture.read_text()), default_catalog())
    session = Session(history=[base], unlimited=True)
    job = SearchJob(session, {"max_pieces": 26})
    while job.status == "running":
        job.tick()
    job.publish(session)
    print(json.dumps({"base": len(base), "candidates": len(job.solutions),
                      "search_nodes": job.nodes}))
    for label, preview_format in (("legacy", None), ("compact", PREVIEW_FORMAT)):
        timings = []
        for _ in range(args.repeats):
            started = perf_counter()
            data = json.dumps(session.state(preview_format=preview_format),
                              separators=(",", ":")).encode()
            timings.append(perf_counter() - started)
        print(json.dumps({"contract": label, "bytes": len(data),
                          "median_ms": round(1000 * median(timings), 3)}))


if __name__ == "__main__":
    main()
