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

## Cheaper tables: incremental slippage indexes, predecessor deltas, flat envelopes

Profiling the searches after the return-loop floors showed the reverse tables
themselves as the next cost: layer expansion reversed, moved and reversed every
pose for every move, slippage searches re-enclosed every pose of a cumulative
layer for every depth they queried, and the lattice envelope was built from
nested helpers and generator expressions once per pose of every layer.

Moves are rigid, so a predecessor is the pose plus a delta that depends only on
the heading; the deltas are tabulated once per search and expansion is one tuple
addition. Slippage indexes are built incrementally: each pose's physical box is
computed once, and the index of depth k extends the index of depth k-1 by the
poses that depth added. The lattice envelope is one flat function with the same
integer arithmetic (checked identical on 20,000 random poses). Each DFS node
also reverses its open stubs once for both the transit and the target queries.

Every node count, result fingerprint and pruning counter is unchanged on all 30
benchmark cases and the seven differentials. CPU time (process time, minimum
of five runs, so machine load does not distort it), 25,000-node budget:

| Case | Before | After |
| --- | ---: | ---: |
| Mixed gap, broad inventory, 1 mm | 0.39 s | 0.25 s |
| Mixed gap, broad inventory, 5 mm | 0.42 s | 0.25 s |
| Switch, broad inventory, exact | 0.36 s | 0.28 s |
| Switch, broad inventory, 5 mm | 0.91 s | 0.52 s |
| Long gap, 5 mm | 47 ms | 31 ms |
| Whole suite | 3.48 s | 2.20 s |

## Keying networks: cached primitives, shared rotation products

Profiling the network enumerator on the corpus showed nine tenths of its time
in congruence keys: 1,792 closed networks keyed for 109 classes, each key
rebuilding its placements' exact primitives with field arithmetic, rotating the
frame candidates, and re-rotating the winner. Three changes, all keeping every
key byte-identical (checked on all 671 corpus layouts):

- A placement's exact primitives (line intervals, arc sectors, isolated points)
  depend only on the piece and its frame, and an enumeration replays the same
  placements in thousands of candidates, so they are cached (bounded, cleared
  wholesale when full) and only the union is rebuilt per layout.
- The four integer products of a point with one cosine and sine serve all four
  quarter turns and both reflections, and one gcd serves the four quarter turns,
  so the 48 frames cost six product sets and twelve reductions.
- The winning frame's exact points are rebuilt from its integer vectors instead
  of rotating the primitives again in the field.

CPU time (minimum of two runs): keying the 671-layout corpus 4.47 s to 2.31 s;
enumerating the corpus network problem with 109 classes 12.0 s to 7.0 s, the
36-class switch problem 3.5 s to 2.3 s, identical result sets.

## Forward probes decide depths the tables have not built

The exact tables stop at the depth the progressive budget has bought, and every
query beyond it was answered by the loose envelopes. A pose reaches the anchor
within `depth + gap` moves exactly when some pose at most `gap` forward moves
ahead of it lies in the layer of `depth`, so a query up to three moves beyond
the deepest built layer is now decided by expanding the queried pose forward
and testing each frontier against that layer, with a cap of 1,024 expanded
poses per probe. Probes answer only the queries actually asked, so they cost
nothing for the tens of thousands of poses a deeper layer would hold, and
their answers are exact and final. The base allowance alone builds five to six
layers at once, so probes give exact answers at depths eight to nine from the
first node, and up to twelve or thirteen once the search has earned the deeper
layers.

Result fingerprints are identical on all 30 benchmark cases, the seven
differentials and the crossing-centric set. CPU time (process time, minimum of
five runs), 25,000-node budget:

| Case | Nodes before | Nodes after | Before | After |
| --- | ---: | ---: | ---: | ---: |
| Mixed gap, broad inventory, exact | 2,690 | 622 | 0.14 s | 0.05 s |
| Mixed gap, broad inventory, 5 mm | 3,160 | 636 | 0.34 s | 0.11 s |
| Switch, broad inventory, exact | 3,999 | 604 | 0.31 s | 0.05 s |
| Switch, broad inventory, 5 mm | 4,098 | 604 | 0.55 s | 0.19 s |
| Whole suite | | | 2.50 s | 0.83 s |

At the start of this work the mixed case took 16,451 nodes and 1.12 s.
`stats.completion_probes` reports the poses probes expanded.

## Loop searches use the reverse tables

Fresh-loop searches had only the reach and turn prunes: a walk was cut when the
remaining track could not span the distance home or swing the heading back, so
a 17-piece search with one switch and every piece required spent 1.85 million
nodes proving that no loop exists. A loop must return to its origin face exactly
as a completion must reach its selected end, so the reverse reachability tables,
envelopes, return-loop floors and forward probes now apply to both modes; the
only change is which anchor the tables are built for. The prune is conservative,
so complete and result-limited searches return the same solutions in the same
order, and searches that used to hit their node budget now finish.

CPU time (process time), single run, results identical unless noted:

| Loop search | Nodes before | Nodes after | Before | After |
| --- | ---: | ---: | ---: | ---: |
| 12 curves, 6 straights | 91,651 | 1,915 | 1.20 s | 0.14 s |
| 12 curves, 6 straights, 3 mm slop | 92,603 | 1,915 | 1.27 s | 0.20 s |
| 12 curves, 4 straights, 1 switch, all pieces | 1,848,103 | 11,488 | 31.2 s | 0.22 s |
| 10 curves, 4 straights, 1 crossing | 127,275 | 217 | 1.45 s | 0.03 s |
| 8 curves, 2 straights, 2 ramps, 1 span | 106,973 | 16 | 1.05 s | 0.00 s |
| 12 curves, 2 straights, 2 level crossings | 77,711 | 1,738 | 1.62 s | 0.12 s |
| 12 curves, 6 straights, field engine | 91,651 | 1,915 | 12.6 s | 1.12 s |
| 12 curves, 4 straights, 1 switch, 300,000-node cap | 300,001, 14 found | 11,488, 39 found, exhausted | 5.23 s | 0.58 s |
| 8 curves, 4 straights, 2 switches, reversing, cap | 300,001, none | 1,946, none, exhausted | 4.94 s | 0.06 s |
| 12 curves, 4 straights, 2 slopes, 2 ramps, 2 spans, cap | 300,001, 4 found | 4,481, 100 found | 7.16 s | 0.42 s |

Twelve curves and two straights with a switch, reversing closures and 3 mm
slop used to exhaust a two-million-node budget with 17 loops found; the search
now completes in 2,843 nodes with 52.

## Slippage probes: cached boxes and group rejection

With the forward probes in place, the slippage searches spent most of their
time in the probes' near tests: every frontier pose recomputed its physical
envelope and scanned the sorted boxes of its heading, and almost every probe
ends without any hit (351 of 354 in the switch case), so the scans were the
common path. Only 7,216 distinct poses stood behind 38,737 near tests, so each
queried pose's box is now cached alongside the layer poses' boxes, and every
heading group of a near index records the extremes of its boxes so a query
whose grown box lies outside them is rejected with four comparisons before any
scan. The probe's near test is inlined with the same pre-test. Each padding
tuple is computed once per slack value. The field engine's interval enclosure
sums integer numerators over one common denominator instead of normalising a
Fraction at every step; it returns the same integers (checked on 20,000 random
field values and 3,000 random poses).

Every answer, node count and result fingerprint is unchanged. CPU time (process
time, minimum of five runs), 25,000-node budget:

| Case | Before | After |
| --- | ---: | ---: |
| Switch, broad inventory, 1 mm | 0.14 s | 0.09 s |
| Switch, broad inventory, 5 mm | 0.19 s | 0.09 s |
| Mixed gap, broad inventory, 5 mm | 0.11 s | 0.08 s |
| Custom 15-degree piece, 1 mm (field engine) | 0.06 s | 0.03 s |

## Keying networks: screened frames, reused endpoints, cached keys

Profiling the network enumerator again showed nine tenths of its time still in
congruence keys, now split between choosing the frame, normalising the
primitives, sampling the chosen frame and replaying every closed network
through the layout constructors. Four changes, all leaving every key
byte-identical:

* A frame's identity orders lines, then circles, then isolated points, so a
  frame whose reduced scale or smallest primitive already exceeds the best
  one's cannot win; it is discarded before its sorted identity is built.
  Quarter turns permute and negate the reduced vectors, so each point is
  reduced once per base heading and reflection instead of once per quadrant.
* Merged line intervals end at original segment ends, and arc sectors are
  bounded by fixed lattice headings; the placement cache now holds those exact
  points, so normalising a layout no longer recomputes them in the field.
* The sampled key is a function of the exact canonical identity alone, so it
  is cached per identity: an enumeration that finds a class sixteen times
  samples it once.
* The enumerator assembles each closed network directly from its exact engine
  frames and its own link map instead of replaying every attachment and join.

CPU time (process time, minimum of two runs):

| Enumeration | Before | After |
| --- | ---: | ---: |
| Corpus keying, 671 layouts | 2.83 s | 1.70 s |
| 2 buffers, 3 straights, 3 curves, up to 8 pieces | 6.45 s | 2.69 s |
| 2 buffers, 1 switch, 3 straights, 2 curves, up to 8 | 2.16 s | 1.55 s |
| 2 buffers, 1 switch, 2 straights, 4 curves, up to 9 | 16.2 s | 10.1 s |
| 4 buffers, 2 switches, 2 straights, 2 curves, up to 8 | 6.69 s | 3.36 s |
| 12 curves, 2 straights, up to 14 | 13.4 s | 13.1 s |

The found layouts, their order, node counts and every congruence key are
identical to the previous tree on all of these and on the perfect-network
search.

## Network enumeration prunes with the reverse tables

The network enumerator had no reachability pruning at all: it grew every
partial network until its piece bound, so enumerating the networks of twelve
curves and two straights up to fourteen pieces spent 429,879 nodes on nine
closures. Every open end of a closed network is mated, so from any open end of
the current layout some walk over the new pieces reaches another current open
end, or a spare port of a junction the walk placed itself (see
`docs/search-correctness.md`); the loop solver's tables decide both questions
after the rigid motion that puts the target on the anchor. A piece with a
sealed or route-less port can cap an end instead, so a node is cut only when
more ends are stranded than the stock can cap. `NetworkConfig.lookahead`
(default 10, 0 disables) and `stats.pruned_reachability` expose the prune.

CPU time (process time), results identical:

| Enumeration | Nodes before | Nodes after | Before | After |
| --- | ---: | ---: | ---: | ---: |
| 12 curves, all pieces | 4,094 | 23 | 0.14 s | 0.00 s |
| 2 buffers, 3 straights, 3 curves, up to 8 | 3,863 | 3,863 | 3.3 s | 3.2 s |
| 2 buffers, 1 switch, 3 straights, 2 curves, up to 8 | 26,027 | 2,417 | 1.56 s | 0.62 s |
| 12 curves, 2 straights, up to 14 | 429,879 | 257 | 13.3 s | 0.05 s |
| 12 curves, 2 straights, 1 switch, up to 13 | 2,000,001 (capped, 1 found) | 79 (1 found) | 78 s | 0.02 s |

Enumerations whose stock keeps a buffer until the end gain little, because a
buffer can cap any stranded end; the prune bites once the caps are placed.

## Signatures by lazy minimum, solutions assembled from engine frames

With loop searches pruned, nearly half of a closure-heavy loop search went into
canonical signatures: every rotation of every closure, its reversal and its
mirror were normalised in full before taking the smallest. The minimum is now
built one element at a time, extending only the rotations still tied on the
prefix, so a rotation that loses on an early element is never normalised. The
result is the same tuple (checked against the exhaustive definition on 300
random step traces with transits).

Each solution's layout was replayed through the checked constructors, which
re-derive every frame in field arithmetic and re-check every joint: about 4 ms
per solution. Both engines keep exact frames and the step trace records every
joint, so the layout is now assembled directly, exactly as the network
enumerator does; the replay stays as the reference the regression compares
against on loops, reversing loops, slop fits, completions and transits.

CPU time (process time, minimum of three runs), results identical:

| Search | Before | After |
| --- | ---: | ---: |
| 12 curves, 6 straights, all loops | 0.109 s | 0.062 s |
| 12 curves, 2 straights, 2 level crossings | 0.109 s | 0.078 s |
| 12 curves, 4 straights, 1 switch, 39 loops | 0.516 s | 0.312 s |

## Network root passes withdraw the types already rooted

Each piece type roots the network search once, and a network was found by the
pass of every type it contains: the buffer-and-curve enumeration found 1,792
closed networks for 109 classes, and keyed every one of them. The pass of a type
finds every network containing that type, so a later pass withdraws every type
whose own pass came earlier; the subtrees it no longer visits could only
rediscover networks already found. The classes found, their representatives and
the order they are found in are unchanged, and when every piece is required only
the first pass can ever use the whole inventory. The enumerator also bins
collision samples only once some placement's bounds come within reach, exactly
as the loop solver does, instead of translating and binning every candidate
twice.

CPU time (process time, minimum of two runs); layouts, order and keys identical:

| Enumeration | Nodes before | Nodes after | Before | After |
| --- | ---: | ---: | ---: | ---: |
| 2 buffers, 3 straights, 3 curves, up to 8 | 3,863 | 770 | 2.66 s | 0.61 s |
| 2 buffers, 1 switch, 3 straights, 2 curves, up to 8 | 2,417 | 523 | 0.66 s | 0.16 s |
| 2 buffers, 1 switch, 2 straights, 4 curves, up to 9 | 12,541 | 2,558 | 4.61 s | 1.02 s |
| 4 buffers, 2 switches, 2 straights, 2 curves, 500 results | 12,734 | 12,734 | 3.73 s | 3.30 s |
| Perfect networks, 1 switch, 2 buffers | 2,417 | 523 | 0.75 s | 0.17 s |

The result-limited enumeration stops inside its first pass, so only the binning
helps it.

## Centring congruence keys in integers

Choosing the canonical frame starts by centring every exact point on the
translation origin and clearing denominators. Both steps used field arithmetic:
three exact subtractions per point and a Fraction product per coefficient, and
the origin itself was an exact average summed term by term. Every coefficient of
every point and of the origin is now put over one common denominator in
integers. A common factor left in the vectors cancels in the gcd reduction that
defines the identity, so the identity, the chosen frame and the key are
unchanged: all 671 corpus keys are byte-identical, and keying the corpus takes
about a tenth less CPU time (2.23 s to 2.00 s on a loaded machine).

## Loop closing tries both ends in doubling turns

The editor's direction portfolio gave the forward direction a quarter of a
stage's node allowance, the reverse direction a half, and any remainder to the
forward direction again. Which end is the hard one is not known in advance: on
the reported bridge gap, growing from one end proves the plain stage impossible
in 113 nodes and finds all eight bridge completions in 605, while the other end
wanders for as long as it is allowed. Closing that gap from the wrong end spent
6,250 nodes of the plain stage and 16,384 of the bridge stage on it before the
reverse turn settled each stage: 97% of 23,352 nodes.

The two directions now alternate, each turn with twice the previous budget,
starting at 1,024 nodes; the rest of the allowance goes to the turn it no longer
fits, a direction only gets a turn when that turn's budget exceeds its previous
one, each direction keeps its reverse tables between turns (a search can hand
its tables to the next search of the same ends and stock), a probe starts with
the table allowance of the whole stage rather than one eighth of its own small
budget, and the direction that settles a stage is tried first in the next stage.
Every turn boundary reports the shared node count, so long searches keep their
heartbeat.

Editor searches (`benchmarks/editor_completion.py` settings: eight results, 26
pieces, zero slop; CPU time of one `solve_gap` call); the same eight completions
are found in every case:

| Case | Nodes before | Nodes after | Before | After |
| --- | ---: | ---: | ---: | ---: |
| Reported gap, finite stock, forward | 23,352 | 1,742 | 1.67 s | 0.27 s |
| Reported gap, finite stock, reverse | 740 | 718 | 0.19 s | 0.20 s |
| Reported gap, unlimited, forward | 23,488 | 1,878 | 1.91 s | 0.38 s |
| Reported gap, unlimited, reverse | 878 | 854 | 0.34 s | 0.31 s |
| Mixed gap | 139 | 138 | | |

The reverse cases lose a few nodes because a probe now starts with the whole
stage's table allowance instead of one eighth of its own.

## Editor closings: the oracle on the lattice, audits over one base

With the search itself small, profiling whole editor closings showed the time
around it. On an ordinary plain-track gap the arc oracle took four fifths of
the closing: its prefix and suffix poses were composed with exact field
transforms, about 1,500 per call. Every candidate audit sampled and binned the
whole base again, and the narrow-phase collision check compared every sample
pair of neighbouring cells even when the two cell clouds could not reach each
other. Four changes, none of which alters a sampled float, a verdict or a
candidate:

* The oracle composes its poses on the integer lattice whenever the ends and
  the four track pieces fit it (standard track always does): a step is one
  tuple addition, and lattice poses are equal exactly when the field poses
  are, so the exact matching of prefixes against suffixes is unchanged. The
  exact geometry remains for custom catalogues, and the candidates are still
  built and audited exactly as before. Over 584 corpus closings the oracle
  returns byte-identical candidates in 2.3 s instead of 18.2 s.
* Each placement's sample cloud is cached per piece, frame and spacing, with
  the same multiply/add order as before, so every float is bit-identical.
* Each cell cloud records the box of its samples; a query cell whose own box is
  at least the pair's limit away in x or in y is skipped before the pairwise
  scan, which only ever rejects pairs the scan would have rejected.
* One overlap auditor per closing problem samples and bins the base once;
  every candidate's new placements are checked and pushed in the standalone
  audit's order and popped again, restoring the field exactly. The solver's own
  closures, the oracle's candidates and the bridge stage's expansions share it.

CPU time of one `solve_gap` call (process time, minimum of five runs; the
timer resolves 15.6 ms), same candidates in every case:

| Case | Before | After |
| --- | ---: | ---: |
| Winding circle (oracle) | 47 ms | under 1 ms |
| Mixed gap (oracle, then 138 nodes) | 47 ms | 16 ms |
| Reported bridge gap, forward | 250 ms | 219 ms |
| Reported bridge gap, reverse | 188 ms | 125 ms |

The arc oracle alone: winding circle 56 ms to 3.8 ms, mixed gap 53 ms to
2.8 ms, and the two cases that find eight candidates at once, whose remaining
cost is building and auditing them, 12 ms to 6 and 9 ms.
