# Editor performance and worker packaging

Exact arithmetic remains in Q(sqrt(2), sqrt(3)). Rational products skip zero
cross-terms, subtraction works directly on coefficients, and existing Fraction
coefficients are reused. Alg now enforces its documented immutability so shared
exact values cannot corrupt geometry caches; copying and pickling still work.

The shared caches are bounded: 128 piece-traversal entries, 128 local centreline
sample entries, and 4,096 exact port transforms. Keys contain geometry, not just
catalogue ids. The port cache holds no Layout or Session. Public list containers
are fresh copies; cached samples are immutable tuples. No validation result,
revision check, collision decision or complete mutable session response is cached.

Ring/bridge completion composes repeated ramp/span units and reuses exact prefixes
within one search. Its enumeration order, inventory limits and collision checks
are unchanged. Candidate cards reuse the size already computed in their preview.

The frontend retains catalogue controls and candidate cards while their displayed
metadata is unchanged, updating counts, availability and selected-tool styling in
place. Redraws preserve focus and unsubmitted inventory values. Catalogue changes
rebuild the relevant controls; new candidate revisions clear stale selection. Card
comparison does not serialize preview geometry, and event handlers use current data.

The worker ZIP omits static/editor.html (already served separately), cli.py and
render.py. Those files remain in the desktop Python package. The worker archive
stays content-stamped, deterministic and self-hosted. Pyodide itself is unchanged.

Regression coverage lives in tests/test_performance_contracts.py,
tests/test_worker_bundle.py, tests/web/render-reuse.test.cjs and the browser suite.
Tests compare exact arithmetic, cache isolation/bounds, worker API round-trips and
DOM identity rather than making machine-dependent wall-clock assertions.

## Second-pass cold-start and search overhead

Port transforms split repeated local rotation from per-placement translation. Connector
geometry has only 24 possible headings, so exact radical multiplication is reused across
placements while every returned Pose remains exact. Floating centreline evaluation keeps
its original operation order; only the 24 sin/cos pairs are cached, so sampled float
values and borderline collision comparisons are bit-for-bit unchanged.

Alg hashes are memoized lazily. This avoids paying tuple/Fraction hashing for the many
short-lived exact values that are never dictionary keys, while repeated exact-position
lookups reuse a stable hash. Built-in catalogue parsing and solver symmetry/span metadata
are likewise bounded and cached; public catalogue mappings remain fresh caller-owned
objects and all cached piece objects are immutable.

Collision rollback now exploits its strict LIFO contract: the previous maximum piece
width is restored in O(1), and each grid cell removes the just-added contiguous suffix
instead of reverse-scanning once per sample point. The collision predicate, cell layout,
clearance rules, and sample coordinates are unchanged.

The Pyodide worker now uses a minimal package marker and excludes the desktop-only drive,
explore, network-enumeration and scoring helpers in addition to the CLI, renderer and
separately served editor HTML. Those modules remain in normal Python installs. The worker
still contains every transitive dependency of gui.Session/solve and its isolated API
round-trip test exercises state, edit, solve, apply, import, export and restore.


## Third-pass collision and editor-state reuse

Collision grid buckets group one placement's samples per occupied cell instead of
repeating placement metadata for every point. LIFO rollback removes one grouped cell
entry at a time, and each candidate query resolves a grid-cell neighbourhood once even
when many 8 mm samples share that same 96 mm cell. Collision thresholds, height and
underpass rules, neighbour exemptions, and sample coordinates are unchanged.

Layout footprint expansion is translation-invariant, so the sampled local footprint is
cached by immutable path geometry, width, overhang and one of the 24 headings; each
placement then contributes only a translated envelope. Editor state serialization also
computes each exact connector pose once and shares it between layout JSON, joint audits
and matable-pair detection. Returned JSON remains freshly owned by the caller.

## Fourth-pass single-pass collision preparation

Solver candidates now translate their cached local centreline samples and assign them
to collision grid cells in the same pass. That prepared grouping is used first for the
collision predicate and, when the candidate is accepted, inserted directly into the
field without scanning the samples again. Public ``CollisionField.add`` and ``clashes``
retain their original point-list interface.

Prepared queries are evaluated cell-first: each neighbouring grid bucket and each stored
placement's width/underpass metadata are resolved once for all candidate samples in that
cell. The collision predicate, sample coordinates, grid size, clearance/underpass rules
and neighbour exemptions are unchanged. Differential tests against the previous engine
cover randomized add/query/pop sequences plus lattice, field, crossing, elevation and
completion searches; ordinary regression tests keep the public behaviour covered.

## Completion search after PR #8

The reverse feasibility check now searches up to six traversals within the same
4096-expansion cap (also limited to `max_nodes // 8`). Exact planar poses and
heights are tracked separately, reducing the state multiplication from ramps.
Reversing targets share the table through exact coordinate transforms. Free
transits count only compatible ports on the same placement. Future junctions are
included both in the feasibility test and in conservative distance/turn bounds.

The table below compares merged commit `b3ba9d0` (four-step lookahead) with
`0864c91`, using the same 25,000-node limit, 20-piece limit and eight-result limit.
All previously returned candidates were retained in these cases.

| Case | Previous nodes | New nodes | Results before / after |
| --- | ---: | ---: | ---: |
| Half circle | 294 | 108 | 3 / 3, exhausted |
| Two-curve start | 4,083 | 1,599 | 8 / 8 |
| Mixed gap | 2,917 | 1,097 | 8 / 8 |
| Bridge gap | 11,837 | 3,749 | 8 / 8 |
| Bridge, broad inventory | 25,001 | 2,131 | 0 / 8 |
| Mixed gap, broad inventory | 25,001 | 25,001 | 0 / 0 |
| Switch plus plain spares | 22,428 | 1,587 | 8 / 8 |
| Switch, broad inventory | 25,001 | 25,001 | 0 / 0 |
| Long gap | 17,209 | 7,464 | 8 / 8 |

At that revision, the two remaining broad cases still hit the cap. More aggressive pruning can
examine more candidate moves before reaching a fixed DFS-node limit, so elapsed
time need not fall for every capped case. The editor's plain-track stage handles
both of these bases before trying a broad inventory.

Run `PYTHONPATH=src python benchmarks/completion.py` to reproduce the inputs and
report node counts, result counts, elapsed time and stop reasons. The output
identifies the imported source path. For comparison against an older checkout,
point `PYTHONPATH` at that checkout's `src` and pass `--lookahead 4`.
Performance regressions assert operation counts and retained solutions rather
than machine-dependent time thresholds.

## Completion search after PR #10

Heading-conditioned envelopes now extend pruning beyond the six-step exact table.
Each envelope retains minimum/maximum exact linear projections instead of every
reachable position. Translations compose directly at each heading; diagonal
projections preserve useful spatial constraints that coefficient intervals alone
miss. This works with both arithmetic engines, all eligible existing transits,
and present/future reversing targets. The envelopes and short tables share the
same `min(4096, max_nodes // 8)` preprocessing cap.

The same nine inputs and limits now give the following results against `5560675`
(PR #10's solver plus the icon-only PR #9). All previous candidates were retained.

| Case | Previous nodes | New nodes | Results before / after |
| --- | ---: | ---: | ---: |
| Half circle | 108 | 84 | 3 / 3, exhausted |
| Two-curve start | 1,599 | 133 | 8 / 8 |
| Mixed gap | 1,097 | 188 | 8 / 8 |
| Bridge gap | 3,749 | 372 | 8 / 8 |
| Bridge, broad inventory | 2,131 | 514 | 8 / 8 |
| Mixed gap, broad inventory | 25,001 | 22,155 | 0 / 8 |
| Switch plus plain spares | 1,587 | 204 | 8 / 8 |
| Switch, broad inventory | 25,001 | 11,318 | 0 / 8 |
| Long gap | 7,464 | 291 | 8 / 8 |

Both previously capped cases now produce eight audited solutions within the
existing 25,000-node budget. The long gap uses 96% fewer nodes and the bridge gap
90% fewer. Bounds reach 8–16 traversals in these cases while retaining at most
168 heading envelopes; total preprocessing stays below 2,900 expansions.

There is a small setup cost: the half circle took roughly 10 ms instead of 7 ms
in one local run. The broad mixed search also took longer (2.1 s versus 1.3 s),
but reached eight solutions instead of stopping without one. The long gap fell
from about 169 ms to 28 ms. These times are observations, not portable guarantees
or test assertions. The benchmark now reports bound depth and retained envelope
counts as well as total preprocessing work. Correctness and operation-count
regressions are in `tests/test_completion_bounds.py`; the real Pyodide browser
test closes, previews and applies the long gap under the production CSP.

## Completion search after PR #11: reuse repeated checks

Profiling `d6cbf01` showed 522,871 geometric reachability queries across the nine
benchmark cases. Many ask the same question at different branches or depth
contours. A per-search LRU cache now reuses those immutable geometric answers,
with at most 4096 entries. Junction transit allowances and target poses are also
computed once per DFS node, then reused by its candidate moves. Lattice target
rotations use direct exact integer formulas instead of a repeated rotation loop.

The cache is cleared in a `finally` block when traversal ends, including when a
progress callback raises. This promptly releases its poses even if the recursive
DFS closures have not yet been collected. Caches hold no layouts or sessions.

All nine cases retain the same ordered solutions, node counts, pruning counters,
preprocessing work, depth and stop reasons as `d6cbf01`. The largest cases show:

| Case | Previous evaluations | New evaluations | Previous median | New median |
| --- | ---: | ---: | ---: | ---: |
| Mixed gap, broad inventory | 315,339 | 11,897 | 2.095 s | 1.440 s |
| Switch, broad inventory | 196,709 | 21,922 | 1.249 s | 0.871 s |
| Bridge, broad inventory | 4,772 | 398 | 46.8 ms | 39.6 ms |

The two hardest cases take about 30% less time in this local three-run comparison;
96% and 89% of their geometry queries are served from the cache. This does not
increase the search or preprocessing budgets. Some small cases incur overhead:
the long gap measured 31 ms versus 23 ms, while the half circle was 8 ms versus
7 ms. Timings are observations rather than portable guarantees or assertions.

Use `PYTHONPATH=src python benchmarks/completion.py --repeats 3` for median timings.
The output includes `completion_checks` and `completion_cache_hits`. Regression
tests in `tests/test_completion_reuse.py` require identical enumeration and search
counters with caching disabled, bound the cache, verify all twelve rotations,
and exercise successful cleanup, callback errors, and catalogue isolation.

## Slippage completion after PR #12

Previously, any positive slop disabled all completion tables and linear bounds.
Slippage now uses outward physical intervals, widening each direction by the
remaining total gap budget. Complete short tables have an index of physical boxes
by heading and x position, with a Euclidean lower-bound distance test. Exact
heading/height constraints, cumulative joint gaps and the final collision audit
are unchanged. Geometry and future-target caches include the remaining slop;
indexes and query caches are released after each search, including callback errors.
Preprocessing retains the existing `min(4096, max_nodes // 8)` expansion cap.

The benchmark now contains the original nine exact cases plus **18 slippage
cases**: 1/5 mm budgets on several inventories, 3-4-5 mm offset endpoints, a 4.9 mm
near miss, broad and long forced closures, a climbing transit spending 1+2 mm,
and a fractional-radius 15° piece. Rows report settings, exact/forced result counts,
ordered result fingerprints, individual gaps, stop reasons, nodes, preprocessing,
and median/minimum/maximum timings. Repeated results must have identical fingerprints.

These are local Python 3.12 three-run medians against `3107f25`, using 20 added
pieces, eight results and 25,000 DFS nodes. A node-limit row reports 25,001 because
the existing counter records the visit that detects the limit.

| Case | Before nodes | After nodes | Before time | After time | Results before / after |
| --- | ---: | ---: | ---: | ---: | ---: |
| Half circle, 1 mm | 1,007 | 82 | 23.4 ms | 13.9 ms | 3 / 3 |
| Bridge, broad inventory, 5 mm | 25,001 | 514 | 866.3 ms | 49.5 ms | 0 / 8 |
| Long gap, 5 mm | 25,001 | 370 | 817.9 ms | 46.2 ms | 4 / 8 |
| Offset circle, insufficient 4.9 mm | 993 | 33 | 20.5 ms | 6.6 ms | 0 / 0 |
| Offset circle, 5 mm | 1,002 | 83 | 22.6 ms | 13.6 ms | 3 / 3 forced |
| Offset circle, broad inventory, 5 mm | 25,001 | 286 | 709.1 ms | 28.3 ms | 0 / 8 forced |
| Offset long gap, 5 mm | 25,001 | 295 | 818.9 ms | 41.4 ms | 5 / 8 forced |
| Switch, broad inventory, 5 mm | 25,001 | 19,899 | 738.5 ms | 1,875.5 ms | 0 / 8 |
| Mixed gap, broad inventory, 5 mm | 25,001 | 25,001 | 724.1 ms | 1,821.1 ms | 0 / 0 |
| Fractional 15° piece, 1 mm | 118 | 19 | 18.8 ms | 95.1 ms | 1 / 1 |

The broad and long offset cases take about **25× and 20× less time**, respectively,
while finding more forced fits. All nine exact cases retain their ordered result
fingerprints and node counts. Exhausted slippage cases retain their fingerprints;
regressions also compare complete layouts and retain the earlier candidates from
capped searches. Timings are observations, not portable promises or test thresholds.

Extra proof work is not free. In this pass the switch took longer but returned eight
results, while the mixed case reached the 25,000-node cap without a result. At the editor's
existing 60,000-node budget, the 1/5 mm mixed cases returned eight results in
29,936/30,339 states (2.23/2.33 s), whereas the previous solver returned none before
that cap. Small field searches can spend more time building bounds than they save;
the zero-inventory transit likewise grows from roughly 0.6 to 1.0 ms. These limits
are kept in the benchmark rather than excluded from the measurements.

Reproduce or select cases with:

```sh
PYTHONPATH=src python benchmarks/completion.py --suite slippage --repeats 3
PYTHONPATH=src python benchmarks/completion.py --case offset_long_slop_5 --lookahead 0
PYTHONPATH=src python benchmarks/completion.py --case mixed_full_slop_5 --max-nodes 60000
PYTHONPATH=src python benchmarks/completion.py --case offset_circle_slop_5 --engine field
```

For a historical comparison, run the current benchmark script with `PYTHONPATH`
pointing at the older checkout's `src`. Run timing comparisons sequentially, without
competing test processes. The output identifies the imported solver path. CI lints
the benchmark and runs operation-count, exhaustive-fit and real-worker regressions.

## Stock-aware turning bounds for mixed inventories

The next pass separates turning capacity from the relaxed number of traversals.
A free crossing route still advances the path, but contributes no turn. The bound
also accounts for scarce turning stock and the placement used to create a future
reversing target. Existing and future curved junction transits retain conservative
turn allowances. This rejects impossible tails before the geometric table query,
without adding preprocessing or changing candidate order.

The table compares local Python 3.12 three-run medians against `c320424`, using the
same 20-piece and eight-result limits. The baseline uses 60,000 nodes so the mixed
cases finish; the new solver uses the stricter 25,000-node limit. Both builds finish
all listed searches with eight identical ordered results and the same completed
preprocessing layers. Timings are observations, not test thresholds.

| Case | Before nodes | After nodes | Before time | After time |
| --- | ---: | ---: | ---: | ---: |
| Mixed gap, broad inventory, exact | 22,155 | 16,451 | 1,502.2 ms | 1,107.7 ms |
| Mixed gap, broad inventory, 1 mm | 29,936 | 24,111 | 2,429.0 ms | 1,839.9 ms |
| Mixed gap, broad inventory, 5 mm | 30,339 | 24,514 | 2,365.9 ms | 1,903.5 ms |
| Offset circle, broad inventory, 5 mm | 286 | 24 | 29.1 ms | 12.7 ms |
| Switch, broad inventory, 1 mm | 19,701 | 19,451 | 1,949.2 ms | 2,044.7 ms |
| Switch, broad inventory, 5 mm | 19,899 | 19,649 | 2,098.0 ms | 2,035.4 ms |

The mixed slippage cases now find all eight results under the benchmark's default
25,000-node cap, where the previous build found none. They use 19–20% fewer nodes
and take 20–24% less time to find the same results. Exact mixed search takes 26%
less time; the broad forced-offset case takes 56% less. All 27 existing cases
retain their ordered result fingerprints. Extra turn bookkeeping is not a
universal speedup: the 1 mm switch case is about 5% slower, and the small winding
case rises from 14.2 to 19.2 ms despite unchanged nodes.

Three additional cases bring the suite to **30 cases, including 20 with slippage**.
They close through a preplaced switch without any spare pieces, requiring its
30-degree turn with exact endpoints, a 5 mm forced joint, or an insufficient
4.9 mm allowance. Regressions also preserve these witnesses in both directions
and arithmetic engines, on both switch branches at rotated/elevated poses.
Scarce-stock exhaustive comparisons and a custom curved junction exercise
backtracking and later free transits.

```sh
PYTHONPATH=src python benchmarks/completion.py --case mixed_full_slop_1 --case mixed_full_slop_5 --repeats 3
PYTHONPATH=src python benchmarks/completion.py --case turn_transit --case turn_transit_slop_4.9 --case turn_transit_slop_5
```

## Deferred collision binning and cheaper candidate scoring

Profiling the two broad-inventory cases showed a quarter of the time in the
collision pipeline, almost all of it confirming that a candidate touches nothing:
only 3 % of point tests found an overlap. Every accepted placement was translated
and binned into the grid, and every candidate was tested against it, even though
a piece two joints back is already out of reach.

Placements are now stored with their sample bounds and binned lazily. A candidate
first compares its own bounds against every placement it may not ignore; when the
boxes are at least the interaction limit apart in `x` or `y`, or separated in
height by the blanket clearance, no sample pair can overlap and the point test is
skipped. Only placements whose boxes come within reach are binned, at most once.
The sampled model, its spacing, clearance and underpass rules are unchanged: the
box test can only say "no overlap is possible", never "overlap".

The candidate loop also converts each child pose to floats once, scores it
against the anchor and every open stub in one engine call, sorts without a key
function, computes the per-node tail allowances once instead of per candidate,
and memoises the transit bound of each junction port set.

Three-run local medians on Python 3.14 against `765ce29`, 25,000-node budget,
identical node counts, result fingerprints and pruning counters on all 30 cases:

| Case | Before | After |
| --- | ---: | ---: |
| Mixed gap, broad inventory, exact | 1.313 s | 1.119 s |
| Mixed gap, broad inventory, 1 mm | 2.834 s | 1.640 s |
| Switch, broad inventory, exact | 1.212 s | 0.598 s |
| Switch, broad inventory, 5 mm | 2.544 s | 1.646 s |
| Bridge, broad inventory, exact | 54 ms | 30 ms |
| Whole suite | 13.67 s | 8.66 s |

`tests/test_performance_contracts.py` pins the contract: samples are prepared
once per point test, once per deferred placement a later query reaches and once
per base piece, and a successful point test hands its grouped samples straight to
the field.

## Return-loop floors and a progressive table budget

Profiling the remaining hard cases showed that most of their nodes came from one
allowance: a crossing still in stock let every query count one extra traversal,
because the tail might place it and later pass through it for free. That is true
only if the tail can also drive a loop back to the crossing, and the reverse
tables already know how many traversals such a loop needs at least. The
allowance is now granted only when the remaining placements can fit the junction
and that loop; a transit through a junction already placed is only counted while
the walk can still reach one of its entries. Both rules are exact statements
about the same reachability the tables prove, so results are unchanged.

The tables are also built progressively: every search gets a base allowance of
`min(4096, max_nodes // 8)` expansions, earns 24 more per DFS node and is capped
at 262,144, with the exact horizon raised from six to ten placements. A depth not
yet affordable stays permissive and is asked again later; only decided answers
are cached. Short searches never pay for deep tables, long ones earn them.

Three-run local medians on Python 3.14, 25,000-node budget, identical result
fingerprints on all 30 cases against the deferred-binning build above:

| Case | Nodes before | Nodes after | Before | After |
| --- | ---: | ---: | ---: | ---: |
| Mixed gap, broad inventory, exact | 16,451 | 2,690 | 1.119 s | 0.183 s |
| Mixed gap, broad inventory, 1 mm | 24,111 | 3,080 | 1.640 s | 0.459 s |
| Mixed gap, broad inventory, 5 mm | 24,514 | 3,160 | 1.548 s | 0.465 s |
| Switch, broad inventory, exact | 11,068 | 3,999 | 0.598 s | 0.334 s |
| Switch, broad inventory, 5 mm | 19,649 | 4,098 | 1.646 s | 0.887 s |
| Bridge, broad inventory, exact | 514 | 79 | 30 ms | 16 ms |
| Whole suite | | | 8.66 s | 3.72 s |

Against `765ce29`, before any of today's changes, the suite went from 13.67 s to
3.72 s. The price is paid by the smallest searches: long gaps with slippage take
about 20 ms longer because they now build exact layers to depth eight or nine
that a 200-node search cannot use. In the mixed case the tables prove that a
return loop through the crossing needs more than seven traversals, so the
allowance only applies to the first two placements of a ten-piece completion.

## One-handed loop search

In loop mode the mirror image of every loop is another loop with the same
canonical signature, found again by a walk whose first turning move goes the
other way. When every stock traversal has a buildable mirror twin, the search
now skips right-handed moves until a turning move has been placed. Completion
searches never do this: a base breaks the symmetry. On the corpus enumerations
this halves the work exactly with identical results: the 12-curve, 2-straight
loop search fell from 6,539 to 3,271 nodes and the level-crossing search from
326,442 to 163,231. `stats.pruned_mirror` counts the skipped candidates.

## Congruence keys choose their frame in integer arithmetic

The exact-frame congruence key applied every lattice rotation and reflection to
the exact primitives with field arithmetic before choosing the canonical frame,
which made keying a layout about 3.5 times slower than the older sampled key.
The frame is now chosen in integer arithmetic: every centred point becomes
integer coefficient vectors over one common denominator, each rotation is an
integer bilinear map (four times the exact cosine and sine are integer vectors
in the same basis), and a frame's identity is reduced by the gcd of its entries
so congruent curves that arrive with different denominators still compare
equal. Only the chosen frame is then materialised exactly and sampled, so the
key of a curve is unchanged whenever the same frame wins. On the 671-layout
corpus, keying fell from 46.7 ms to 6.7 ms per layout, faster than the sampled
key it replaced (13.4 ms), with the same 611 classes and no merges or splits.
