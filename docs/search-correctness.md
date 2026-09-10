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
