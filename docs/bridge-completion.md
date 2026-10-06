# Bridge-aware editor completion

Without reversing loops, two proofs can end a pair search before any stage, the
job naming them as its stage: the joint check, for a bridge end that no piece left
and no end meeting it could join, and then the height check, for ends further
apart in height than the pieces left could climb.

The editor searches in this order: the arc templates (skipped when reversing loops
are allowed), ordinary curves and straights, one complete standard bridge plus
ordinary track, and finally the full remaining inventory. The bridge stage is a
heuristic, not a proof of completeness. Other elevations, custom bridge geometry,
and multiple bridges still use the general solver. Plain and bridge stages prefer
ordinary closures even when reversing loops are allowed; the full-inventory
fallback also searches reversing closures. Collision and underpass thresholds are
the general solver's, and every stage keeps to the bridge's joints and the floor
([search-correctness.md](search-correctness.md#bridge-joints-and-the-floor)).

The bridge macro uses the exact four ramp/span/span/ramp segments and their sampled
height profile. It is enabled only for the standard bridge geometry, sufficient
stock (two ramps and two spans), and two ends on the floor. Reserving three extra
piece slots accounts for its four real components. Before publication, every macro
is expanded into normal catalogue placements and checked for inventory, real-piece
depth, exact joints among the new placements, and collisions against the actual
link graph. Action stones and all existing placements and links are retained, so a
base with a deliberate forced fit keeps its candidates. No macro appears in saved
layouts.

A search starts with plain, bridge and full-inventory budgets of 25,000, 250,000
and 60,000 nodes. If curves and straights are already all the box a walk can place
(a buffer, an off-ramp or a ramp with no arch joins no walk), only the
full-inventory search runs. A job's `searched` count accumulates across stages
instead of restarting, and **Search harder** resumes the same job with larger
budgets ([search-jobs.md](search-jobs.md)).

## Regression case

`tests/fixtures/bridge-gap.json` and `bridge-completed.json` are two JSON layouts.
The former has 59 placements and two open
ends; the latter retains them and adds 16 curves, four straights, two ramps and two
spans. Tests separately verify that witness and discover a completion without its
coordinates, in both finite-stock and infinite-pieces modes. Every returned candidate
must export as ordinary pieces, preserve the base, close exactly, and pass a complete
layout collision audit. Applying and undoing the candidate must retain the base.

The default request (`max_pieces=26`, `max_results=8`, zero slop) finds eight
24-piece extensions from either end in both inventory modes; node counts are in
[performance.md](performance.md#representative-times). These are model-validated
layouts, not measurements of real bridge clearance.
