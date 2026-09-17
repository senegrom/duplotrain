# Spatial collision-screening review — 17 September 2026

Baseline: `8b8de0f03d1fdf1876634a71f57ae082005e4b89`.

## Change and correctness boundary

Completion search used a spatial grid for its detailed sampled-point collision
checks, but its preceding `CollisionField.near()` check scanned every placement's
bounds on every candidate. Large layouts therefore repeatedly examined distant
track that could not possibly interact with the candidate.

The broad phase now uses a separate 256 mm grid of sample bounding boxes when
there are at least 128 clouds. Queries expand by the candidate half-width plus
the greatest stored half-width minus the unchanged touching margin. Every returned
cloud is still tested with its own width, the original bounding-box inequalities,
and the original sampled-point checks. Outward rounding at grid boundaries avoids
losing borderline clouds. This is candidate screening, not a new collision model.

The grid is built lazily. Small fields retain linear scanning, and final audits
that call `clashes()` directly never construct it. Boxes spanning more than 64
cells are kept in a fallback list rather than filling an unbounded grid. Oversized
queries and queries whose cell work is disproportionate to the field use the
linear path. Deferred placements are indexed before their samples are binned;
all eligible deferred clouds are binned before the detailed check. Every pop
removes its bounds, including clouds whose samples were never materialized.

Clouds are deduplicated by identity, not by placement ID: callers may contribute
multiple clouds for one placement. The index is owned by one collision field,
not shared between layouts, searches or catalogues. No external dependency, UI,
save format, bridge-clearance threshold, search ordering, or search budget changes.
The collision module's introductory bridge description was also aligned with the
existing height-specific ramp/span behavior; the constants and predicates are unchanged.

## Reproducible evidence

Run `PYTHONPATH=src python benchmarks/collision_index.py --repeats 3 --count-bounds`.
For the baseline use the same script with `PYTHONPATH` pointing to the old source.
The 179- and 539-piece cases add 10 or 40 **synthetic remote closed circles** to the
reported 59-piece layout. They leave the same two open ends, inventory, gap and
completion problem. They are scaling tests, not additional user-supplied layouts.

Measurements below are medians of three sequential native CPython 3.13.5 runs,
not browser or iPhone timings. Bounds counts come from a separate untimed run.
All cases use unlimited pieces, zero slop, 26 added pieces and eight results.

| Base placements | Previous seconds | New seconds | Previous bounds considered | New bounds considered |
|---|---:|---:|---:|---:|
| 59, original layout | 1.6577 | 1.6488 | 1,862,440 | 1,862,440 |
| 179, with synthetic circles | 2.1915 | 1.8455 | 5,150,560 | 99,973 |
| 539, with synthetic circles | 3.4468 | 2.0589 | 15,014,920 | 99,973 |

The original layout retains the light linear path and is effectively unchanged.
The larger cases ran approximately 16% and 40% faster. All three still search
exactly 23,491 nodes and return eight 24-piece completions. Every timed candidate
is independently checked afterward for unchanged base placements/links, exact
joints, complete closure and whole-layout collisions. Fewer bounds inspected is
not fewer search nodes. This is not a universal speed-up or a minimum-piece claim.

## Regression coverage

Sixty new tests exercise negative coordinates, cell-edge touching, outward rounding,
variable widths, clearance and underpass flags, repeated placement IDs, deferred
clouds before and after indexing, ignored neighbours, multiple-cell deduplication,
wide-box fallbacks, oversized/nonfinite queries, maximum-width restoration,
index lifetime, and randomized push/pop/query sequences against a full linear scan.
Exhausted exact and forced-fit searches on both arithmetic engines, with and
without reversing targets, retain identical solutions and all non-timing counters.
The reported bridge gap also retains identical editor outcomes and candidate lists.

Search-deeper behavior is unchanged: it increases effort but still restarts rather
than retaining a search frontier. This pass targets collision-screening throughput.
