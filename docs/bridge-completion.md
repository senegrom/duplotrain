# Bridge-aware editor completion

The editor searches in this order: the arc templates (skipped when reversing loops
are allowed), ordinary curves and straights, one complete standard bridge plus
ordinary track, and finally the full remaining inventory. The bridge stage is a
heuristic, not a proof of completeness. Other elevations, custom bridge geometry,
and multiple bridges still use the general solver. Plain and bridge stages prefer
ordinary closures even when reversing loops are allowed; the full-inventory
fallback also searches reversing closures. Collision and underpass thresholds are
the general solver's.

The bridge macro uses the exact four ramp/span/span/ramp segments and their sampled
height profile. It is enabled only for the standard bridge geometry, sufficient
stock (two ramps and two spans), and two ground-level ends. Reserving three extra
piece slots accounts for its four real components. Before publication, every macro
is expanded into normal catalogue placements and checked for inventory, real-piece
depth, exact joints among the new placements, and collisions against the actual
link graph. Action stones and all existing placements and links are retained, so a
base with a deliberate forced fit keeps its candidates. No macro appears in saved
layouts.

`search_effort` is an integer API parameter from 1 to 16, defaulting to 1. It scales
the plain, bridge and full-inventory budgets of 25,000, 250,000 and 60,000 nodes. If
the plain inventory is already the whole box, that search uses the full budget.
Progress counters accumulate across stages instead of restarting. A synchronous
`/api/solve` retry starts over with its larger budget; the editor's **Search
harder** resumes the same job instead ([search-jobs.md](search-jobs.md)).

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
