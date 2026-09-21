# How the searches stay fast

Every speed-up keeps results identical: the same solutions in the same order,
the same node counts and pruning counters, byte-identical congruence keys and
bit-identical sampled floats. A change is verified by differentials against
the previous tree before it lands, and timing is process CPU time on one
machine, never a test assertion.

## Measuring

`PYTHONPATH=src python benchmarks/completion.py --repeats 3` runs the 30
completion cases (nine exact, 21 with slippage) and reports nodes, results,
stop reasons, preprocessing work and median times; `--suite`, `--case`,
`--lookahead 0` (the reference search without tables), `--engine field` and
`--max-nodes` select variants. `benchmarks/editor_completion.py` times whole
editor closings of the reported 59-piece bridge gap in both directions and
both inventory modes and hashes the ordered exact layouts,
`benchmarks/collision_index.py --count-bounds` scales that problem with
synthetic remote circles, `benchmarks/editor_payload.py` measures state
serialisation, and `benchmarks/editor_presentation.py` times Check layout and
warm state responses on the completed layout and on synthetic layouts of 539
and 1,499 pieces. Point `PYTHONPATH` at an older checkout to run the same script
against it, and compare CPU time rather than wall time when other work shares
the machine.

## Exact arithmetic and bounded caches

Poses live in Q(sqrt 2, sqrt 3) with Fraction coefficients. `Alg` is immutable,
so zero and one identities return an operand, a product of two values in
Q(sqrt 3) evaluates only its two nonzero coefficient formulas, quarter-turn
rotations swap and negate coordinates, and hashes are memoised lazily. Port
transforms split the 24 possible rotations from per-placement translation.
Caches are bounded and keyed by geometry, never by session: 128 piece
traversals, 128 local centreline samples, 4,096 port transforms, 4,096 exact
poses of lattice frames (equal frames give one object, so the placements
assembled from them hit the sample and primitive caches by identity instead of
comparing twelve coefficients), 2,048 sample clouds per piece, frame and
spacing, and the translation-invariant footprint of a piece at each of its 24
headings. No validation result, revision check,
collision decision or mutable session response is cached. The recursive DFS
clears its own closure reference when a search ends, so a finished collision
workspace is released at once rather than at the next cyclic collection.

## The lattice engine

When the ends and every piece fit the 30-degree lattice, as standard track
always does, poses are integer 6-tuples and every move, frame and port delta is
precomputed for all twelve headings, so the hot path is tuple additions and
compares; custom 15-degree geometry falls back to the exact field engine with
the same search. Reverse tables pack a planar lattice pose into one int, four
32-bit coordinate fields above the heading, so a layer grows by one int
addition per pose and move and every membership query hashes a small int.

## Reverse reachability tables

A completion must bring its walking end to the selected target and a loop must
bring it back to its origin face. Reverse breadth-first tables hold every
planar pose and, separately, every height that can reach that anchor in at
most k traversals, for k up to a horizon of ten, over the pooled moves of every
stock piece, every usable route of a base-only junction and the exact
retargeting of reversing loops. Tables are built progressively: a search gets
`min(4096, max_nodes // 8)` expansions at once, earns 24 more per DFS node up to
262,144, and a depth not yet affordable stays permissive and is asked again
later. Only decided answers enter the per-search LRU cache of 4,096 entries.

Beyond the built layers a query up to three moves deeper is decided exactly by
a forward probe: the cursor is expanded forward over the same moves and each
frontier is tested against the deepest layer, with at most 1,024 poses per
probe. Deeper still, heading-conditioned linear envelopes bound each
coordinate, the height and eight cardinal and diagonal projections per heading.

Free transits through junctions lend traversals only when they are possible: a
junction still in stock must be placed and reached again by a return loop,
whose minimum length the tables prove, and a junction already placed must have
a reachable spare entry. Turning capacity is bounded separately from the
traversal count, and an inventory without new junctions bounds the remaining
reach by the longest pieces actually left.

Slippage searches ask the same tables with physical distances: every layer
pose has a cached physical box, boxes are grouped by heading and sorted by
their left edge, each group records its extremes so that a query grown by the
remaining budget is rejected with four comparisons when it lies outside them,
and a binary search limits the scan otherwise.

## The candidate loop

Each DFS node computes its transit allowances, reversing targets and tail
budgets once and reuses them for every candidate move. A child pose is
converted to floats once and scored against the anchor and every open stub in
one engine call, the transit bound of each junction port set is memoised, and
an impossible child is rejected before any table query or collision sample.

## Collision checks

Centreline samples 8 mm apart are binned into 96 mm grid cells, grouped per
placement and cell, and removed in O(1) on backtracking. A placement is stored
with its sample bounds and binned only when a later candidate's box comes
within the interaction limit in x, y and height, so a piece two joints back
costs nothing. A prepared query resolves each neighbouring cell once for all
its samples, and a stored cell cloud whose box is at least the pair's limit
away is skipped before the pairwise scan. Fields of at least 128 clouds keep a
lazy 256 mm index of bounding boxes for the broad phase, with a fallback list
for boxes spanning more than 64 cells. One overlap auditor per search
samples and bins the base once, recognises the base's own placement objects
by identity, and keeps in its field the placements a candidate shares with the
previous one, so consecutive solutions of a depth-first search, which share
most of their placements, each audit only their own tail. The sampled model, its spacing,
clearance and underpass rules are the same everywhere; every shortcut only
skips pairs the point test would reject.

## Loops and networks

A fresh loop search skips right-handed moves until a turning move has been
placed whenever every stock traversal has a mirror twin, since the mirror loop
has the same canonical signature; `stats.pruned_mirror` counts the skipped
candidates. Signatures are found by a lazy lexicographic minimum that extends
only the rotations still tied on their prefix, and a solution's layout is
assembled directly from the engine's exact frames and the recorded joints
instead of being replayed through the checked constructors.

The network enumerator prunes with the same tables (`NetworkConfig.lookahead`,
default 10): every open end of a closed network must reach another open end or
a spare port of a junction the walk placed, so a node is cut when more ends are
stranded than the stock's buffers can cap. Each piece type roots the
enumeration once and a later pass withdraws the types rooted before it, whose
networks were all found already; collision samples are binned lazily as in the
loop solver.

Congruence keys, which name each class of closed networks, choose their
canonical frame in integer arithmetic: centred points become integer vectors
over one denominator, each of the 48 frames is an integer bilinear map reduced
by the gcd of its entries, a frame whose reduced scale or first primitive
already loses is discarded before its identity is built, a placement's exact
primitives are cached, and the sampled key is cached per exact identity.

## Editor closings

The editor first asks an arc oracle, which composes its prefix and suffix
poses on the lattice and matches them exactly; then it searches plain track,
one standard bridge as a four-piece macro, and finally the whole inventory,
with budgets of 25,000, 250,000 and 60,000 nodes scaled by `search_effort`.
Which end is the hard one is unknown in advance, so each stage alternates
directions in turns of doubling budget from 1,024 nodes, keeps each direction's
tables between turns and across stages, and tries first the direction that
settled the previous stage. Bridge candidates are expanded and audited before
they count toward the result limit, and only the joints among their new
placements are audited, since the base and its links are carried over
unchanged. Candidate previews use a compact drawing-only contract, and state
serialisation shares each connector pose between the layout, the joint audit
and the mating lists.

## Editor presentation

The drawing lines of an exact placement, rounded and route-preserving, are
cached in a 2,048-entry LRU and copied into fresh lists for every response, and
a 32-entry LRU keeps the footprint of a placement tuple, so a state or candidate
response does not resample or remeasure geometry it has already served; neither
cache holds a session, revision, link or ownership. Both hosts send compact
JSON, which leaves every parsed value unchanged and trims an eight-suggestion
response by an eighth. Check layout keeps its all-pairs scan below 128 pieces;
larger layouts shortlist candidate pairs through the collision field's bounds
index, a conservative superset, and run the unchanged pair tests on them, which
turns the quadratic scan of a 1,499-piece layout into a few thousand pair tests.
In the browser, flat chords are drawn whole and only climbing edges are
subdivided for paint order, one lazily built record per layout holds segments,
per-piece groups, batches and bounds, picking visits only the pieces whose
bounds contain the pointer, and the project indicator compares a cached session
string with a small settings key on explicit redraws only.

## Representative times

Process CPU time on one machine, the mean of many runs, with results
identical to the reference searches without tables.

| Search | Nodes | Time |
| --- | ---: | ---: |
| Completion benchmark suite, 30 cases | | 0.78 s |
| Reported bridge gap, finite stock, forward / reverse | 1,742 / 718 | 126 / 82 ms |
| Reported bridge gap, unlimited stock, forward / reverse | 1,878 / 854 | |
| Ordinary plain-track gap (oracle, then a short search) | 138 | 16 ms |
| All loops of 12 curves and 6 straights | 1,915 | 0.07 s |
| Reversing loops of 12 curves, 4 straights and 2 switches, 100 results | 793 | 57 ms |
| Loops of 16 curves, 8 straights, 2 switches and a crossing, 100 results | 350 | 27 ms |
| 17-piece loop search with one switch, every piece required | 11,488 | 0.22 s |
| Networks of 2 buffers, 3 straights and 3 curves up to 8 pieces, 109 classes | 770 | 0.61 s |
| Keying the 671-layout corpus | | 2.0 s |
| The arc oracle over 584 corpus closings | | 2.3 s |
| Check layout on a synthetic 1,499-piece layout | | 60 ms |
| Warm state with eight compact suggestions, reported gap | | 8.7 ms |

Before this work the loop search with a switch spent 1.85 million nodes and
31 s, the bridge gap 190,000 nodes and 8.5 s, and the suite 13.7 s.

## Regression contracts

Timing is never asserted. `tests/test_performance_contracts.py` pins operation
counts (samples prepared once per point test and once per deferred placement a
query reaches), cache bounds, bit-identical sample clouds and cache isolation.
Differential tests compare complete ordered solutions and every non-timing
counter against the reference search with tables disabled, on both engines,
with slippage and with reversing closures, and the browser suite closes,
previews and applies gaps through the real Pyodide worker under the production
content security policy.
