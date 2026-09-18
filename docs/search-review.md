# Search and application review — 16 September 2026

Compared with production commit `21d922664b9d77d15e4003a7f5d4db8487005576`.

## Search changes

The editor grows from either selected end in turns: the two directions alternate,
each turn with twice the previous budget, starting at 1,024 nodes (a sixteenth
of a small allowance), and the rest of the allowance goes to the turn it no
longer fits. This is a **direction portfolio**, not a meet-in-the-middle or
resumable search, and all turns together obey the existing stage node budget.
The search is deterministic, so a direction is only given a turn when that
turn's budget exceeds its previous one; each direction keeps its reverse
reachability tables between its turns, and the direction that settles a stage is
tried first in the next stage of the same closing problem. On the reported
bridge gap, growing from one end proves the plain stage impossible in about a
hundred nodes while the other end wanders for tens of thousands; the fixed
forward-first split spent 97% of its 23,352 nodes on that end. Easy searches
stop after the first turn. A fully searched piece bound stops retries but is
never presented as an exhausted inventory.
Forced-fit searches (nonzero slop) and reversing-loop targets keep their original
one-direction semantics. No collision or underpass threshold is relaxed.

The arc-template shortcut now builds exact backward suffix pose lookups once,
instead of transforming each possible suffix for every prefix. It also suppresses
duplicate layouts produced by equivalent template splits. The shortcut's template
family and real-piece/inventory limits are unchanged.

Expanded bridge assemblies are now audited **before** counting them toward the
result limit. Previously an invalid macro could take a slot and be discarded only
after the search stopped, hiding later valid candidates. The optional core
`solution_filter` hook and `dropped_filter` counter make this explicit; the ordinary
core solver's behavior is unchanged when the hook is absent.

## Other application fixes and review scope

The Search deeper button remains available when an incomplete search has returned
some suggestions, not just when it returns none. Clicking Solve before the initial
state loads or while another operation is busy is ignored safely. Mating hints no
longer offer a forbidden road-plate-to-road-plate joint. Even a forced core join
cannot connect a port to itself.

Reviewed the editor/API, save/import/export and revision paths, worker recovery,
layout/join validation, collision integration, solver and network search entry
points, and test/deployment configuration. This is not a claim of an exhaustive
security audit or a proof that every remaining app bug has been eliminated. The
network enumerator and train-driving algorithms were not rewritten in this pass.

## Reproducible benchmark

Run `PYTHONPATH=src python benchmarks/editor_completion.py --repeats 3` and compare
with the same runner and fixtures against the previous source via `PYTHONPATH`.
These are median seconds from three sequential runs per case on the same local
CPython 3.13.5 environment, **not** browser or iPhone timings. Node counts exclude
the arc shortcut's pose work. Every returned candidate was checked for unchanged
base placements/links, exact joints, and whole-layout collisions. The finite bridge
box contains precisely the original layout plus 16 curves, four straights, two
ramps and two spans. All cases request eight results, zero slop and at most 26
added pieces; “forward” is the editor's default endpoint order for the report.

| Case | Old nodes | New nodes | Old seconds | New seconds |
|---|---:|---:|---:|---:|
| half_circle | 0 | 0 | 0.0121 | 0.0103 |
| winding_circle | 0 | 0 | 0.5592 | 0.1662 |
| mixed_gap | 138 | 139 | 0.5945 | 0.2022 |
| half_built_bridge | 0 | 0 | 0.0141 | 0.0127 |
| reported_finite_forward | 83,490 | 25,369 | 3.7858 | 1.4988 |
| reported_finite_reverse | 2,732 | 2,765 | 0.3178 | 0.2520 |
| reported_unlimited_forward | 190,000 | 32,441 | 8.4879 | 2.0428 |
| reported_unlimited_reverse | 9,804 | 9,881 | 1.3092 | 0.8245 |

The default reported infinite-inventory case still finds eight valid 24-piece
extensions: 190,000 -> 32,441 nodes (82.9% fewer), 8.4879 -> 2.0428 seconds (4.16x).
Finite-stock default drops from 83,490 to 25,369 nodes and 3.7858 to 1.4988 seconds.
Already-favorable endpoint orders can spend slightly more nodes because splitting
budgets changes the core's adaptive lookahead allowance; this is not a universal
node-count improvement. The mixed gap has one extra node but much less template
setup work. Both favorable endpoint cases also ran faster in this measured sample.

## Regression coverage and limits

New coverage includes shared-budget exhaustion, cumulative progress, exact
field/lattice acceptance filters, rotated and elevated arc closures, duplicate
suppression, bridge audit rejection followed by a later valid result, preserved
inventory/base geometry, invalid mating hints and self-joins, and browser
import -> solve -> preview -> apply -> undo on the reported 59-piece layout.
No answer coordinates are supplied to the search. Existing recovery, atomicity,
worker, security and search-law regressions remain enabled.

Search is still bounded and heuristic in the editor: failure under a node/piece
limit does not establish impossibility. Search deeper increases effort but restarts
rather than resumes a saved frontier, and it may return the same suggestions.
The bridge shortcut still handles one standard complete bridge between ground-level
ends; other bridge arrangements fall back to the general solver. No new physical
clearance measurements or minimum-piece guarantees are claimed.
