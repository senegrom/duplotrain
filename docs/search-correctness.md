# Search correctness and input boundaries

## Potential joints are exact, not distance-based

Network placements do not move after attachment. Two placed pieces can become
directly linked later only when an unoccupied, unsealed connector on each already
mates exactly (position, height and opposite heading). During growth, the collision
checker therefore exempts the attached neighbour and those possible future
neighbours. The final audit exempts only actual links.

This uses the same whole-neighbour exemption as the final collision model; it does
not assume a 70 mm joint radius or a particular piece width. Regression tests
compare loop and network enumeration on wide circles, including a catalogue that
requires the general field engine. Collision checks remain sampled and inherit
the catalogue's geometry and underpass assumptions.

## Centreline identity is independent of piece boundaries

`congruence_key()` normalizes the union before sampling: touching and overlapping
collinear 3D segments become one interval, while arcs use the union of fixed
15-degree sectors on each circle. A single 256 mm straight and two 128 mm straights
therefore have the same curve key. The same holds for uneven segment splits,
ramps of equal grade, arc splits and duplicate routes.

The exact normalized geometry supplies the translation origin. Rounded samples
are a set, so repeated points cannot reweight the centroid or result. The public
`spacing` and `decimals` arguments still control the sampled, approximate key;
this is not an exact congruence proof. Unknown `Segment` subclasses retain their
own sampling method. Keys are implementation details rather than a persisted
layout format; regenerate cached keys after updating the implementation.

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
and height projections that can reach the anchor in at most six traversals by
default. Both arithmetic engines use exact values. Separating the projections
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
away; the previous endpoint-only bound incorrectly rejected it.

All slop searches bypass the exact tables. Both projections share the same
preprocessing budget, and a layer is published only when both are complete.
Partial layers never reject a candidate: a cap falls back to DFS without changing
completeness or stop reasons. `completion_work` records the actual expansions.

`completion_lookahead=0` provides a reference search. Regressions compare complete
solution signatures on both engines and custom 15-degree pieces, exercise
preprocessing exhaustion, and retain zero-piece and reversing witnesses. Further
coverage is in `tests/test_completion_targets.py`, including rotated/elevated
targets, both switch branches, projected false matches and future junctions.

## Input and snapshot boundaries preserve exactness

Arc angles are checked as exact multiples of 15 before any integer conversion.
For example, 30.9 degrees is rejected rather than changed into a 30-degree curve.
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

These boundaries are covered by `tests/test_review_boundaries.py` and
`tests/test_completion_lookahead.py`.

## Reversals start another ordered pass

A face stone is silent only when departing from that face. Returning toward it
after a mid-piece reversal encounters it normally. A face direction stone starts
a fresh inward pass on the same piece, without following its external link; the
midpoint and next connector are then encountered in order. Stop stones take
precedence over direction stones at the same position. The ordinary repeated-state
check also detects oscillations entirely inside one piece, including two guarded
faces, without falsely claiming coverage of other track.

`DriveReport.steps` now records each pass as `(placement, departure, reached)`.
A face turnaround and its return are separate passes; a mid-piece bounce reaches
its own departure port. Consequently face-reversing runs can have larger `steps`
and `period` values than before. These are discrete pass counts, not travel times.
No change is made to saved layout JSON or the formal lazy-switch theorem.

## Remove the selected stone, not the last stone of that colour

The editor carries `at_port` from each drawn marker through `/api/stone`:
`null` selects the midpoint and an integer selects that connector face. Toggling
matches type and position together. The Remove tool also sends `remove: true`,
so a missing marker is an error rather than a request to add a new stone. Invalid
positions/removal modes leave the session and revision untouched.

Library callers can use `Layout.without_accessory(..., at_port=None)` or an
integer for exact-position removal. Omitting the keyword retains the older
last-of-colour behaviour. Removing one marker preserves other positions, counts,
serialization round trips and undo.

These contracts are exercised by `tests/test_review_round3.py`,
`tests/test_stone_encounters.py`, `tests/test_stone_positions.py` and
`tests/web/stone-selection.test.cjs`, including the HTTP and Pyodide dispatcher.
