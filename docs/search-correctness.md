# Search correctness and input boundaries

## Potential joints are exact, not distance-based

Network placements do not move after attachment. Two placed pieces can become
directly linked later only when an unoccupied, unsealed connector on each already
mates exactly (position, height and opposite heading). During growth, the collision
checker therefore exempts the attached neighbour and those possible future
neighbours. The final audit exempts only actual links.

This uses the same whole-neighbour exemption as the final collision model, whatever
the joint radius or piece width. Regression tests
compare loop and network enumeration on wide circles, including a catalogue that
requires the general field engine. Collision checks remain sampled and inherit
the catalogue's geometry and underpass assumptions.

## Centreline identity is independent of piece boundaries

`congruence_key()` normalizes the union before sampling: touching and overlapping
collinear 3D segments become one interval, while arcs use the union of fixed
15-degree sectors on each circle. A single 256 mm straight and two 128 mm straights
therefore have the same curve key. The same holds for uneven segment splits,
ramps of equal grade, arc splits and duplicate routes.

The exact normalized geometry supplies the translation origin and canonical
orientation. Every rotation and reflection is applied to the exact primitives;
coefficient tuples choose a deterministic minimum before any float conversion.
Only that frame is sampled and rounded. This avoids rotating floating samples
across decimal ties: a 255.9 mm rail retains its key under all 24 lattice rotations
and reflection, as does the same geometry split into uneven shorter rails.
Line endpoint ordering and circular sector ordering are canonical too.

Rounded samples are a set, so repeated points cannot reweight the result. The
public `spacing` and `decimals` arguments still control the sampled, approximate
key; this is not an exact congruence proof. Unknown `Segment` subclasses have no
exact primitive descriptor: they retain their own sampling method and the
sampled-orbit fallback. Keys are implementation details rather than a persisted
layout format; regenerate cached keys after updating the implementation.

## Length includes the entire centreline union

`Layout.track_length()` uses the same normalized 3D union rather than just the
first path on each piece. A stock crossing contributes 256 mm, and a stock switch
contributes both curved branches. Shared collinear sections and circular sectors
are counted only once, including partially overlapping or differently segmented
routes. Intersections at isolated points remove no length; parallel tracks at
different elevations remain distinct. Multi-turn arcs trace their circle once.
For unknown `Segment` subclasses, the declared `length()` is used; overlapping
arbitrary custom shapes cannot be unioned without a primitive description. A
length needs no translation origin, so it never computes the exact centroid the
congruence key averages, whose denominator can grow with every distinct one in
the layout.

The returned value is a floating-point geometric length in millimetres, not the
length of a particular train itinerary. CLI length reports and the compactness
score include secondary junction routes.

The regressions in `tests/test_review_round4.py` exercise decimal ties across all
lattice symmetries, an exact independent oval oracle, shared-route length, and
CLI output. On Linux, explicitly unbounded classification of a connected
25-switch chain reaches its first simulation within an isolated process with only
64 MiB of additional address space; the test stops there, since lazy allocation
does not remove the exponential cost of complete classification.
`tests/test_review_boundaries.py` checks that the default budget refuses 24
switches before any simulation.

## Failed searches leave the editor unchanged

`Session.solve_gap()` validates mating endpoints before searching and publishes
candidates and a new revision only after a successful result. An already-mating
pair should be joined instead. Oracle, solver and progress-callback exceptions
leave the previous candidate list and revision untouched. A successful search,
including a zero-result search, publishes one new revision so old candidate
indices cannot be reused. The shared dispatcher gives HTTP and Pyodide the same
contract.

## Validate inventory before merging

CLI piece counts must be non-negative integers. JSON counts are validated before
being added to flags and boxed-set counts. Fractions, floats (including `12.0`),
booleans, numeric strings, negatives, unknown IDs and non-object documents are
rejected rather than truncated or silently discarded. Valid integer counts from
all three sources remain additive. File-read errors are reported as CLI errors.

The focused regressions are in `tests/test_review_round2.py`,
`tests/test_congruence.py`, `tests/test_solve_atomicity.py`, and
`tests/test_cli_inventory.py`.

## Completion paths can revisit all free junction ports

The loop/completion solver compares every unsealed, unoccupied candidate port
with the closing target and open junction stubs. A crossing can meet its target
on the route used only after a later re-entry. These possible neighbours are
exempt during placement; the independent final audit still requires actual
links. Sealed ports, incompatible overhangs, and unrelated obstacles receive no
such exemption. Forced fits use only the remaining slop budget.

In completion mode, `SolverConfig(min_pieces=0)` permits a path consisting only
of connections and transits through existing junctions. The search visits the
zero-new-piece depth contour even with an empty inventory, but never emits an
empty fresh loop. Minimum/use-all constraints and node/result caps still apply.
The editor also permits these no-new-inventory completions. Already-mating
selected endpoints should still be joined directly instead of searched.

## Exact reverse reachability is an overapproximation

For completion searches, reverse breadth-first tables contain all planar-pose
and height projections that can reach the anchor in at most k traversals, for
k up to the horizon of ten. Both arithmetic engines use exact values. Separating the projections
avoids multiplying states for bridge routes: each may admit a different route,
which enlarges the allowed set. The move pool includes routes through preplaced
pieces, even when none remain in inventory. Stock counts, placement frames and
collisions are also ignored. Absence from either complete projection proves a
tail impossible; membership still requires actual coupled 3D geometry, inventory,
replay and the final actual-link overlap check.

A transit consumes two compatible free ports on one placement and no new piece.
Each placement contributes at most half the number of free ports that have a
free route partner. Summing that bound over placements, and adding a conservative
bound for future placements, prevents lone stubs on separate switches from being
counted as transits. No matching or collision assumption can undercount routes.

Reversing targets use the same table after an exact rigid transformation moves
the target onto the anchor. A future junction must first be placed, then reach
one of its own spare ports within the remaining traversal budget. Precomputed
queries cover every geometrically distinct placement and spare port, ignoring
what precedes the placement. Distance and heading to the original endpoints
cannot prune a branch while a future junction could supply another target. A
regression pins a valid teardrop even when the selected original target is 100 m
away, which a bound on the original endpoints alone would reject.

Both projections share the same preprocessing budget, and a layer is published
only when both are complete. Slop queries use the physical enclosures below.
Partial layers never reject a candidate: a cap falls back to DFS without changing
completeness or stop reasons. `completion_work` records the actual expansions.

`completion_lookahead=0` provides a reference search. Regressions compare complete
solution signatures on both engines and custom 15-degree pieces, exercise
preprocessing exhaustion, and retain zero-piece and reversing witnesses. Further
coverage is in `tests/test_completion_targets.py`, including rotated/elevated
targets, both switch branches, projected false matches and future junctions.

## Longer tails use heading-conditioned linear envelopes

Beyond the short exact tables, each heading has minimum/maximum intervals for
exact coordinate coefficients, height, and cardinal/diagonal linear projections.
At a fixed heading every move adds a fixed vector. Translating intervals by that
vector and taking their union's bounds therefore contains every predecessor.
Each layer also includes the previous layer, so it bounds **at most** that many
traversals. Independent intervals may describe different walks; this admits extra
possibilities and cannot remove a real one.

The cardinal/diagonal projections use rational weights resembling physical axes.
For example, the lattice uses 26/15 in place of sqrt(3). These are exact integer
linear forms on the lattice coefficients, not rounded world positions. Applying
the same form to every displacement and query makes any such weights sound.
The general field engine similarly uses rational forms on its exact coefficients,
including all four height coefficients. No floating tolerance enters these bounds.

All routes, free-transit allowances and present/future targets use the same
conservative rules as the short tables. Both share the progressive
preprocessing allowance (`min(4096, max_nodes // 8)` expansions at once, 24
more per DFS node, at most 262,144), and neither publishes an unfinished layer. Stable zero-motion envelopes are reused at every greater depth,
so an empty move pool and a huge inventory cannot allocate endless identical
layers. The future-target query cache is limited to 4096 entries.

`completion_bound_depth` and `completion_bound_states` expose the largest complete
depth and total retained heading envelopes. Regressions in
`tests/test_completion_bounds.py` retain independently constructed exact tails,
compare exhaustive results on both engines, exercise custom 15-degree curves and
preprocessing exhaustion, and pin two broad-inventory cases.

## Traversal count and turning capacity are separate bounds

The geometry tables relax stock by pooling all available route types. Counting a
free crossing transit as another traversal is necessary for distance, but must not
grant it a curve's turning capacity. Before querying geometry, completion search
also bounds the total absolute heading change available to the tail, in exact
15-degree steps.

For `k` remaining placement slots, newly placed pieces contribute at most the
smaller of `k * max_turn` and the sum of turning capacities in remaining stock.
Existing free transits contribute their own piece's maximum route turn times
their compatible-port transit allowance. Future free transits contribute at most
the smaller of the allowance for `k` junctions and the sum over remaining stock.
These bounds may select incompatible routes or piece types, but only overestimate
capacity. The circular distance between headings cannot exceed the sum of route
turns, so a larger required heading change rules out that target.

The anchor and every existing reversing target are checked separately. For a
future target, the junction that creates it consumes one placement and one copy
of its turn allowance before the tail begins. Ignoring all earlier placements
only enlarges the remaining resources. The future-target cache key includes this
turn budget as well as traversal count and remaining slop; equal-length branches
can have different amounts of turning stock. Early candidate checks conservatively
leave the candidate in stock until its recursive visit.

Slippage changes position, never heading, so it cannot enlarge the turn allowance.
`tests/test_completion_turn_budget.py` compares complete ordered solutions with
lookahead disabled on both arithmetic engines, including scarce stock, backtracking,
free turning transits on rotated and elevated switches, and a custom junction
traversed twice. Independent witnesses include forced joints and zero new pieces.
The mixed-inventory benchmarks also pin eight audited results below 25,000 nodes
for exact, 1 mm and 5 mm searches.

## Stock-aware reach and base routes

For an inventory without new junctions, the remaining reach of a tail is
bounded by the longest available pieces that fit the current contour, with the
candidate piece subtracted before its child is checked, so one spent bridge
cannot make every later move look able to span a bridge's length. The early
child check applies only to states without open stubs or reversing-loop
targets; an inventory with new junctions keeps the plain rules, because a
junction may later supply free transits. The tables pool every stock traversal
and only the usable routes of base-only junctions: both route ports must be
open on the same placement, and sealed, linked and selected endpoint ports
serve no transit. No base piece is ignored as an obstacle, and free ports only
disappear during growth, so the initial route set stays an overapproximation
throughout backtracking.

## Slippage uses physical distances and one remaining budget

A small physical displacement need not have small exact coefficients: large
rational and radical terms can nearly cancel. Expanding the coefficient bounds
by a number of millimetres would therefore discard valid forced fits. Slippage
instead uses physical x/y projections, with eight directions bounding longer
tails. Each direction is widened by its Euclidean norm times the remaining slop.
Height coefficients and headings retain their exact constraints.

Physical projections are enclosed by integer intervals at `10**9` units per mm.
Integer square roots give rational lower/upper bounds on sqrt(2), sqrt(3) and
sqrt(6). Multiplication by signed coefficients, outward division and interval
addition preserve containment. An additional outward relative margin covers
floating distance evaluation at large translated coordinates. Rounding can only
increase the search space; these intervals never decide whether a solution is
exact. The final joint checks and independent collision audit remain authoritative.

Short layers retain their exact poses. A lazily built index groups their physical
boxes by heading and sorts them by minimum x. Binary searches restrict candidate
boxes; the minimum box-to-box Euclidean distance must fit the remaining budget.
The maximum box width is included in the binary-search window, so overlapping or
unusually wide intervals cannot be skipped. Indexes exist only for complete layers,
with at most `(completion_lookahead + 1) * (completion_work + 1)` box entries.

Every forced transit translates the remaining path without changing its heading
or height. By the triangle inequality the accumulated displacement is at most
the sum of those joint gaps. The bound therefore uses `slop - slack_used`, once
for the entire tail, including the final joint. Rigid retargeting preserves that
budget for existing and future reversing targets. Both geometry and future-target
cache keys include the remaining budget, preventing an answer for one allowance
from being reused for another. The indexes are cleared together with the query
cache when a search that built its own tables finishes or its progress callback
raises.

`tests/test_completion_slippage.py` compares complete ordered solutions against
lookahead-disabled searches on both engines, including 3-4-5 mm offset endpoints,
1+2 mm intermediate/final gaps, forced reversing targets and large cancelling
coefficients. Independent perturbed tails exercise the longer physical bounds.
Additional cases cover 15° geometry, incomplete preprocessing, finite huge slop,
cache limits and audited benchmark results. Browser coverage previews and applies
a forced closure through the real Pyodide worker under the production CSP.

## Reused geometric proofs are independent of search state

The completion cache keys contain the full exact cursor pose, including height
and heading, the remaining traversal bound, and any remaining slop. The anchor
and move pool are fixed for the tables' lifetime. Published reachability layers
never change, so both positive and negative answers from complete layers can be
reused. An answer that needs a layer not yet built is permissive and is never
cached: the progressive budget may build that layer later, and the query is
asked again.

Geometric cache entries contain no stock, free ports, collision decisions or candidate layouts.
Each DFS node computes its current transit allowances and reversing targets once;
its child visits compute their own values after consuming stock and ports. The
parent's values remain valid when backtracking restores its state.

The 4096-entry LRU belongs to the tables. A search that built its own empties
it on normal return or a traversal exception, which avoids retaining its poses
through the recursive DFS closure cycle; tables an editor closing passes from
one search to the next keep their decided answers for the same ends and stock.
Tests compare complete results and all search counters against
an uncached evaluator, retain permissive fallback after eviction, separate
catalogues, and check callback-error cleanup.

## Input and snapshot boundaries preserve exactness

Arc angles, start headings and chord angles are checked as exact multiples of
15 before any integer conversion. For example, 30.9 degrees is rejected rather
than changed into a 30-degree curve, and 30.0000000001 rather than snapped to 30.
Integral float/string inputs are normalized to integers while retaining signed
and multi-turn sweeps. Layout construction copies and freezes the link graph,
placements and accessory collections; copying and pickling retain that boundary.
Editor responses copy nested accessory metadata, so modifying a response cannot
change the catalogue or other sessions.

## Classification never reports a budget-limited verdict

Switch settings are generated lazily. Before simulation, `classify()` computes
the number of starts times the product of switch choices and compares it with
`max_runs` (100,000 by default). Exceeding the limit raises
`ClassificationLimitError` without a classification. A larger explicit budget,
or `None` in the library API, permits exhaustive enumeration. This avoids both
materializing an exponential assignment list and silently treating an unfinished
universal check as a proof. The CLI exposes the same budget as `--max-runs`.

These boundaries are covered by `tests/test_review_boundaries.py`.

## Reversals start another ordered pass

A face stone is silent only when departing from that face. Returning toward it
after a mid-piece reversal encounters it normally. A face direction stone starts
a fresh inward pass on the same piece, without following its external link; the
midpoint and next connector are then encountered in order. Stop stones take
precedence over direction stones at the same position. The ordinary repeated-state
check also detects oscillations entirely inside one piece, including two guarded
faces, without falsely claiming coverage of other track.

`DriveReport.steps` records each pass as `(placement, departure, reached)`.
A face turnaround and its return are separate passes; a mid-piece bounce reaches
its own departure port, so face-reversing runs have correspondingly larger
`steps` and `period` values. These are discrete pass counts, not travel times.
`DriveReport.terminal` records the stopping event (stop stone, buffer, open end
or dead route) with its piece, inward entry and reached face without adding a
pass; endless runs have none. Saved layout JSON and the formal lazy-switch
theorem are untouched.

## Remove the selected stone, not the last stone of that colour

The editor carries `at_port` from each drawn marker through `/api/stone`:
`null` selects the midpoint and an integer selects that connector face. Toggling
matches type and position together. The Remove tool also sends `remove: true`,
so a missing marker is an error rather than a request to add a new stone. Invalid
positions/removal modes leave the session and revision untouched.

Library callers can use `Layout.without_accessory(..., at_port=None)` or an
integer for exact-position removal. Omitting the keyword removes the last stone
of that colour. Removing one marker preserves other positions, counts,
serialization round trips and undo.

These contracts are exercised by `tests/test_review_round3.py`,
`tests/test_stone_encounters.py`, `tests/test_stone_positions.py` and
`tests/web/stone-selection.test.cjs`, including the HTTP and Pyodide dispatcher.

## Deferred collision binning keeps the sampled model

A placement's centreline samples are binned into the collision grid only when a
later candidate's bounding box comes within the interaction limit of its box. The
box test is conservative in the model's own terms: two samples can only overlap
when their planar distance is below `half_width + half_width - TOUCH_MARGIN`
and their height difference is below the clearance, and a candidate whose box is
that far from a placement's box in `x`, in `y`, or in height has no such pair.
Underpass rules only exempt further pairs. Whenever the boxes do come within
reach, every deferred placement in reach is binned before the unchanged point
test runs, so the grid the test sees contains every placement that could matter.
Backtracking removes a placement's cell entries by placement rather than by
stack position, because a late-binned placement may sit below a newer one in a
shared cell. The final overlap audit of every returned layout is unchanged and
still bins eagerly.

## The bounds index only screens

A field of at least 128 clouds keeps a lazy 256 mm grid of sample bounding
boxes for the broad phase. A query expands by its own half-width plus the
greatest stored half-width less the touching margin, boxes spanning more than
64 cells live in a fallback list, oversized or non-finite queries take the
linear path, and grid boundaries round outward, so every cloud the linear scan
would consider is returned; each returned cloud is still tested with its own
width, the box inequalities and the sampled points. Clouds are deduplicated by
identity, and the index belongs to one field.

## Free transits need a reachable entry

A free transit passes through a junction without spending a placement, so each
possible transit adds one traversal to what the completion tables are asked.
Two exact conditions gate that allowance.

A junction still in stock can only be transited by a tail that first places it
and then loops back to one of its spare ports that still has a route partner.
For each junction type the solver stores the return queries: from the exit of
every route, the reversed pose of every such port, retargeted onto the anchor
exactly like reversing targets. `transit_floor` reports the largest complete
layer depth in which no return query appears, so a return loop needs more
traversals than that; in slippage mode the physical near test with the whole gap
budget is used, and heights are checked exactly. The allowance is granted only
when the remaining placements minus the junction itself, plus the free transits
already available to shorten the loop, exceed the floor. A candidate junction is
placed by its own move, so its loop must fit the placements left after it. The
floor only grows as layers are published and becomes final at the first layer
that contains a return query, so it can never overstate the loop.

A junction already placed can only be transited after the walk reaches one of
its spare entries. Each DFS node asks the tables, with the loosest traversal
count and the remaining slop, whether the cursor can reach any such entry; a
placement whose entries are all unreachable lends no traversal and no turn. A
candidate one move on can reach no more than its parent, so the node's answer
covers its candidates as well.

Table preprocessing grows with the search effort. Every answer is either final
(a rejection, or a membership found in a published layer, which no later layer
can undo) or permissive because a depth was not yet affordable; only final
answers are cached, and a permissive one is asked again when the allowance has
grown. Comparing a cached search with an uncached one therefore gives the same
decisions at every node; only the moment some layer was built can differ, which
the regression in `tests/test_completion_reuse.py` allows for.

## Loop mode explores one handedness

A loop built from moves `m1 ... mn` has a mirror image built from their mirror
twins, which the canonical signature already folds onto the same key. While a
loop search has not yet placed a turning move (a move whose heading change or
lateral offset is nonzero), right-handed candidates are skipped; every loop they
would lead to is the mirror of a loop the left-handed branch finds, with the
same achiral prefix. The rule is applied only when every stock traversal has a
mirror twin, because a single-handed piece would make the twin loop
unconstructible and its signature distinct, and never in completion mode, where
the base fixes the handedness. Reversing closures and transits are unaffected:
both are mirror-symmetric. A result-limited search may therefore return the
left-handed representative of a class where a two-handed search would return the
right-handed one; complete searches return the same signature set either way.

## The canonical frame is chosen on reduced integer identities

Choosing the frame requires only a total order on the exact frame identities
that every member of an orbit computes identically. Centred coordinates are
rotation-equivariant, so all 48 frames of a curve and of any congruent curve
form the same set of exact geometries. Each is represented by integer
coefficient vectors over a common denominator and reduced by the gcd of all
entries and that denominator; a rational vector set has exactly one such
reduced form, so equal geometries get equal identities whatever denominators
they arrived with, and the smallest identity names the same frame for every
member of the orbit. Ties can only occur between frames with identical
geometry, which sample to the same points. The chosen frame is materialised
with its exact transform, so the sampled key is exactly the one that frame
produces. Opaque custom segments keep the sampled-orbit fallback.

## Forward probes are exact

Let `L_d` be the complete layer of depth `d`: every projection that reaches the
anchor in at most `d` traversals. A cursor lies in `L_{d+g}` if and only if some
pose reached from it by at most `g` forward moves lies in `L_d`. If a route of
length at most `d + g` exists, either it has at least `g` moves, and its pose
after `g` moves has at most `d` moves left, or it is shorter and ends at the
anchor, which every layer contains, after fewer than `g` moves. Conversely a
pose in `L_d` reached after `i <= g` moves gives a route of at most `i + d`
moves. The probe therefore expands the cursor forward level by level, over the
same pooled moves the layers use, and tests each level against `L_d`; heights
are checked separately against their own exact layer at the queried depth, as
before. Slippage translates the remainder of a route at its forced joints, never
the cursor's own first moves, so the same argument holds with the near test at
depth `d`. A probe that exceeds its expansion cap leaves the query permissive
and undecided, exactly like an unaffordable layer.

## Loop searches share the reverse tables

A fresh loop closes when the walking end returns to the origin face exactly (or
within the slop budget), which is the same condition a completion imposes on its
selected end: the anchor of the reverse tables is the closing pose, the move
pool is every traversal of every stock piece, and free transits, open stubs and
reversing targets are handled by the same context. The traversals a loop has
left are its remaining placements plus the transits its stubs and future
junctions can lend, exactly as for a completion tail, so a cursor absent from
the tables cannot close and its subtree contains no loop. The prune is
conservative: it removes only subtrees without closures, so an exhaustive or
result-limited loop search returns the same solutions in the same order, and a
node-limited one can only return more. The one-handed rule and the signature
deduplication are unaffected. Regressions compare ordered results with and
without the tables on both engines, with slop, with reversing closures, and on
a search that exhausts its node budget without them.

## Group extremes only pre-test the near scan

A near test asks whether some box of the queried heading's group lies within
the slack of the query's box. If the query's box grown by the slack does not
overlap the smallest axis-aligned box containing the whole group, no member
can be within reach, so rejecting it early is a necessary condition applied
before the unchanged sorted scan; nothing is accepted that the scan would not
accept. The cached box of a queried pose is the same integer enclosure the
layer poses use. The integer form of the field engine's interval enclosure
computes the same floor and ceiling as exact Fraction sums.

## Screened frames and cached keys choose and name the same frame

The canonical frame is the one with the smallest exact identity, a tuple that
compares its reduced scale first, then its sorted lines, circles and isolated
points. A frame whose reduced scale is larger than the best one's, or whose
smallest primitive of the first nonempty component is larger, therefore has a
larger identity whatever the rest of it holds, so discarding it before building
the identity changes nothing; ties are only resolved by the full comparison.
Reducing each point once and rotating by quadrant afterwards is exact because
the gcd divides every entry, so negation and division commute. The key cache
maps an identity to the sampled key that identity produced: the materialised
frame is a function of the identity, and sampling is deterministic, so a cached
key is the key a fresh computation returns. Endpoints and sector boundaries
taken from the placement cache are the exact points the line and circle
formulas evaluate to at those parameters. A regression compares the screened
choice against the exhaustive minimum over all 48 frames and the cached keys
against fresh ones.

## Network open ends must stay mutually reachable

Let the current partial network have open ends `O`, and let a closed network
extend it by new pieces `N`, none of which has a sealed port or a connectable
port that no route serves. Start a walk at any `e` in `O`: `e` is mated to a
port of some piece in `N` (or directly to another end of `O`, a walk of length
zero). Traverse a route of that piece and continue through whatever the exit
port is mated to. Stop when the walk arrives at an end of `O`, or when it
enters a piece it has traversed before through a port its earlier traversals
did not use (a spare port of a junction). No walk can pass the same joint twice
before one of these happens: passing a joint twice in the same direction means
a piece was left twice through one port, so it was entered through two
different ports, and the second entry was through a port unused before; passing
it twice in opposite directions means an earlier joint repeated first. So the
walk ends after at most `|N|` traversals, each piece traversed once, at the
reversed pose of another end of `O` or at a spare port of a junction it placed.
The first case is a reachability query of the loop solver's tables after the
rigid motion that moves the target onto the anchor, over at most the remaining
placements; the second is the solver's future-junction query, which depends
only on the junction type and the remaining budget less one. A piece with a
sealed or route-less port can end a walk without mating anything, and two walks
can trail into one new junction whose third port a single such cap then
closes, so while any cap remains in stock no end is provably stranded; with
none left, a node is rejected when some end has no reachable target.
Collisions and stock counts are ignored, which only enlarges the allowed set;
direct joins are the zero-traversal case. Regressions compare the enumerated
layouts, in order, with and without the prune on rings, buffered bars and capped
networks with a switch or a crossing, check that a teardrop closing into its own
switch survives, and that a passing loop whose two branch ends share one buffer
through a second switch is found.

## A reversing lobe driven either way round

A reversing closure ends at a junction the walk placed or passed: the walk
enters it, leaves by one branch, goes round the lobe and closes into the other
branch, the stub. Entering the same way, the walk can leave by the stub instead
and drive the lobe backwards to close into the first branch. When the closure
is exact both walks build the same layout, so the signature is the minimum over
both walks (and their mirror images in loop mode); a forced fit keeps its
misfit at the closing joint, so its two walks are different layouts and keep
separate signatures. A regression checks that no reversing result, in loop or
completion mode, repeats a layout.

The closing joint names a port of the junction closed into, and each candidate
names it as its own walk numbers that junction: a symmetric piece written with
its canonical traversal relabels its ports, and the mirror image places the
junction by its mirror traversal, which for the crossing is the other route, so
a diagonal port lands on a straight one. Both port maps come from the placed
geometry. A regression checks that the mirror twins of a loop closing into a
crossing are one result when a single-handed piece in stock makes the search
build both.

## Lazy signature minima and assembled layouts

The canonical signature is the lexicographic minimum of the normalised
rotations of four sequences. Comparing tuples lexicographically decides on the
first differing element, so after k elements only the rotations whose first k
normalised elements equal the minimum prefix can still win; the lazy algorithm
keeps exactly those and extends them by one element, using each rotation's own
first-appearance numbering, and the survivors after the last element all have
the minimum tuple. A solution's layout is the base's placements and links plus
one placement per placed step, whose frame is the engine's exact frame of that
placement converted back to the field, and one link per recorded joint: the
entry of each placed piece to the previous exit, each transit's entry to the
exit before it, and the final exit to the closing target. That is what the
replay through the checked constructors builds, since those constructors derive
the same frames and the search has already verified every joint they check.

## A root pass may withdraw the types rooted before it

The pass rooted at type `t` enumerates, exhaustively within the piece bound,
every closed network that contains a piece of type `t`: any such network can be
assembled in canonical-end order from any of its pieces. The search only reaches
a later pass when every earlier pass ran to exhaustion, because a result or node
limit stops the whole enumeration. So when the pass for `u` starts, every network
containing an earlier type is already recorded or was rejected, and a network's
acceptance does not depend on its root: congruent realizations have the same
stone variants and drive identically. Withdrawing the earlier types therefore
removes only subtrees whose closed networks were all duplicates, and the
remaining subtrees are visited in the same order, so the found layouts and their
order are unchanged. One theoretical difference remains: the sampled overlap
audit works in floating point, so a network exactly on its threshold could in
principle be rejected in one embedding and pass in another, where an
enumeration keeping every type in every pass would audit it again from another
root. With `use_all_pieces` no later pass
can use the whole inventory, so those passes are skipped.

## Lattice oracle poses and shared audits

The arc oracle only compares poses for exact equality and composes rigid
motions. The lattice engine's flat tuples represent exactly the poses whose
coordinates lie on the 30-degree lattice, and two such poses are equal as
tuples exactly when they are equal as field poses, so composing a candidate's
prefix and suffix on the lattice and comparing there decides the same matches
as the field arithmetic did. Rigid motions associate, so stepping through a
unit piece by piece yields the pose its composed transform yielded. When an
end or a traversal does not fit the lattice the oracle keeps the exact
geometry; a regression compares the two geometries candidate for candidate on
a dozen closings and step for step on every traversal.

The shared auditor builds the collision field over the base placements in
index order and then, for each candidate, keeps the leading placements it
shares with the previous candidate and checks and pushes the rest in index
order. A placement's verdict in the standalone audit depends only on the
placements before it, on its own samples and on the set of indices it is linked
to, so a kept placement, one whose piece and frame are the same objects and
whose link set is unchanged (a later transit or closing can link an earlier
placement to a new neighbour, which ends the kept prefix), has already passed
exactly the point tests the standalone audit would run, and the new placements
see the same field. Popping the rest restores the field's grid and width
bookkeeping exactly, as the collision tests assert. A candidate that does not
begin with the base is audited standalone. A regression audits sixty reversing
loop solutions and their overlapping variants in emission, reverse and random
order against the standalone audit. The cell-box pre-test rejects a
stored cell cloud only when its box and the query cell's box are at least the
pair's limit apart along an axis, in which case every sample pair is at least
that far apart and the strict distance test would reject each of them.

## Joint audits from an index

`joint_issues(since=k)` reports exactly the entries of the full audit whose
joint touches a placement at index k or later, in the audit's order; a
regression checks every k against the filtered full report, with and without
supplied port poses. The bridge expansion keeps every base placement at its
index and every base link, so the joints it can change are precisely those
touching an index at or beyond the base size, which is what the stage audits.
A regression closes the reported gap over a base with a curve set a millimetre
off and checks that the candidate's only joint issues are the base's own.

## Packed lattice keys

A key is injective on planar poses whose coordinates stay below 2^31 lattice
units, 107 km. A problem whose anchor, start or base junction ports lie beyond
2^30 lattice units (53 km) runs on the field engine instead; the search reaches
only metres from them, so its keys stay in range. The key ignores the height,
exactly as the levelled tuple did: the height layers remain separate. A move's
packed delta is the difference of the keys of its endpoint and its origin at
each heading, and adding it to any key of that heading yields the key of the
moved pose, because no coordinate field can borrow or carry within the bound.
A regression builds the reverse layers with tuples from the same moves and
checks every published layer and frontier against the packed tables state for
state, the per-heading deltas against the packed differences of the moves, and
three hundred cursors at every depth up to the probe range for the same answer.
