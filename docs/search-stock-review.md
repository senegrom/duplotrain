# Stock-aware completion review — 17 September 2026

Compared with deployed commit `b225fd8f47bb1fead2e4ab2dfa1421d2202b04e2`.

## Changes

### Use the pieces actually left in the box

For completion inventories without new junctions, the solver bounds the remaining
reach by the longest available pieces that fit the current piece contour. It
subtracts the candidate piece before checking a child's remaining reach. A single
standard bridge can no longer make every later move appear able to span a bridge's
length after that bridge is spent. Impossible children are rejected before tail
queries, collision sampling, and another DFS node. These are conservative pruning
bounds, not beam-width restrictions or changes to move ordering.

Existing junction transits retain their separate, conservative reach allowance.
The early child check is restricted to states without open stubs or reversing-loop
targets. Inventories containing new junctions retain the previous rules because a
junction may later supply additional free transits. Forced-position slack is still
included, and exact connector and collision checks remain authoritative.

### Do not invent spare routes from occupied base pieces

The feasibility tables previously included every route of every type in the base,
regardless of stock or occupied ports. They now include all stock traversals and
only usable routes of base-only junctions. Both route ports must be open on the
same placement; sealed, linked and selected endpoint ports cannot be used for a
transit. Routes are normalized through the existing exact canonical-traversal map.

No base piece is deleted or ignored as an obstacle. Ports needed for final targets
remain in the arithmetic engine. Free ports only disappear during growth, so the
initial allowed-route set stays an overapproximation throughout backtracking.

### Compose reusable arc runs

The template shortcut now computes each relative straight run and curved run once,
then composes those exact transforms into prefix frames. It also skips prefixes
that already exceed the piece limit or available straights. Previously, a new
prefix repeated every individual straight/curve transform despite already sharing
suffix lookups. The reported gap's shortcut makes 1,440 `Pose.then` calls rather
than 5,216. Template order, returned piece geometry, and final audits are unchanged.
These caches are local to one call, not persistent mutable session caches.

## Reproducible measurements

Run `PYTHONPATH=src python benchmarks/editor_completion.py --repeats 3`.
The baseline run uses the same benchmark script with `PYTHONPATH` pointed at the
previous checkout's `src`. Both runs below are sequential, with no parallel tests,
on the same local CPython 3.13.5 environment. Times are medians of three runs per
case, not browser/iPhone timings. Budgets are unchanged: 26 added pieces, eight
results and zero slop. The finite box is the original layout plus 16 curves, four
straights, two ramps and two spans.

| Case | Previous nodes | New nodes | Previous seconds | New seconds |
|---|---:|---:|---:|---:|
| Half circle | 0 | 0 | 0.0116 | 0.0095 |
| Winding circle | 0 | 0 | 0.1752 | 0.0500 |
| Mixed gap | 139 | 139 | 0.2129 | 0.0645 |
| Half-built bridge | 0 | 0 | 0.0117 | 0.0106 |
| Reported finite, forward | 25,369 | 23,355 | 1.4518 | 1.5222 |
| Reported finite, reverse | 2,765 | 740 | 0.2810 | 0.1673 |
| Reported unlimited, forward | 32,441 | 23,491 | 2.1798 | 1.6708 |
| Reported unlimited, reverse | 9,881 | 878 | 0.8824 | 0.2320 |

The default reported unlimited case uses 27.6% fewer nodes and is about 1.30x
faster. The reverse orientation uses 91.1% fewer nodes and is about 3.80x faster.
The winding-circle and mixed-gap cases are about 3.50x and 3.30x faster respectively.
The finite forward case is 4.9% slower in this sample despite 7.9% fewer nodes:
extra bound checks and adaptive table work are not free. This is not a universal
wall-time improvement. Both orientations and both inventory modes still return
eight exact 24-piece extensions; every benchmark candidate passes unchanged-base,
exact-joint and whole-layout collision audits.

## Validation and limits

Local validation: 1,486 Python tests passed (`not slow and not browser`), and all
61 JavaScript tests passed. The 47 added cases cover stock-span selection against
exhaustive subsets, spent bridges, isolated/occupied base pieces, canonical free
crossing routes, free ports on different switches, selected endpoints, zero-stock
base-junction transits, exact and forced joins on both arithmetic engines, finite
arc-result ordering, and an under-1,000-node reverse-gap regression in both inventory
modes. Differential tests disable the new bounds and compare fully exhausted result
lists, including layouts, signatures, gaps and ordering. Existing custom-junction,
reversing, collision, recovery and export tests remain enabled.

This pass changes the completion solver and arc shortcut only. Collision thresholds,
bridge clearance, the network enumerator, train-driving rules, UI, save formats and
production deployment workflow are unchanged. Search remains bounded: Search deeper
restarts rather than resumes, the bridge shortcut handles one complete standard
bridge, and no minimum-real-piece or physical-clearance guarantee is added.
