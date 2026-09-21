# Editor presentation optimisation and cleanup — 21 September 2026

Baseline: `6e8ac1c779c74ed5cf19b575022e31cd06bdb3dc`. The lattice-pose cache,
shared-tail candidate audit and previous search improvements on that baseline
are preserved; this pass does not attribute their performance gains to itself.

## Runtime changes

Project dirty-state comparison keeps the cached immutable session-content string
separate from a small name/view/search-settings key. It no longer places the
large string inside another JSON serialization. Fresh but equal snapshots still
compare equal, and reverting content or preferences restores the unchanged state.
Hover-only frames do not recompute project status. Explicit non-hover redraws
still update it, as do the existing save/open and preference controls.

Check layout keeps its linear path below 128 pieces. Larger layouts maintain a
shared deferred bounding-box field and use its public `nearby_placements` method
to shortlist prior placement IDs in sorted order. The existing per-piece fields
still run precisely the same near/clashes tests, neighbour exemptions, clearance,
underpass rules and 8 mm sampling. It stops at the same 200 overlapping pairs,
with the same incomplete-report flag. The shortlist is not a collision verdict.
Diagnostics now reuse the equivalent existing `centreline_points` sample cache.

A 2,048-entry LRU stores immutable rounded route-preserving drawing coordinates
per exact placement. Each public response receives fresh nested lists and dicts;
mutating a response cannot contaminate later responses. A separate 32-entry LRU
stores dimensions keyed only by immutable placements. Neither cache retains a
Session or caches revisions, links/open-port state, inventory, ownership or
acceptance decisions. Size-cache entries may retain geometry for up to 32 layouts;
these are bounded entry counts, not a fixed-byte memory ceiling.

Flat sampled chords no longer receive height-order subdivisions. Ascending and
descending edges retain their existing local-height subdivisions and cap. Picking
still uses the same distance, painted-area, elevation and placement tie rules,
but visits only the shortlisted pieces' segment groups. One WeakMap-owned lazy
geometry record holds segments, per-piece groups, batches and bounds with a
shared lifetime. Explicit revision validation remains separate from cache identity.
The unused segment/hit `order` field is gone.

Worker and local HTTP machine responses use compact JSON separators. Parsed
values and default ASCII escaping are unchanged; human-readable download contents,
request/snapshot size limits and security checks are unchanged. Restore no longer
validates its proposed snapshot twice: parsing and the final atomic pre-mutation
commit guard remain, with a regression checking both rejection and single validation.

## Source organisation

The structural refactor is a separate commit from the runtime optimisations.
`editor.js` remains the sole owner of the current API snapshot and core editor
interaction state. Three companion scripts hold derived canvas/picking geometry,
project/backup presentation, and train presentation. They share that owner rather
than duplicating session state. These are normal deferred scripts, not isolated
ES modules: their explicit load order and single DOMContentLoaded initialiser are
part of the tested contract. Both hosts serve the same checked-in sources.

All companion scripts participate in the content stamp and cache-busted asset
URLs; the local host uses an explicit asset allowlist. The Node harness loads the
complete scripts in the same order. No framework or bundler is added. This split
reduces coupling and the main editor file's size, not the total download size.
The extended-search workflow installs the test extra rather than the broader dev
extra; its pytest/render coverage stays intact. Production build, both browser
checks and same-artifact deployment gates are unchanged.

## Integrated measurements

The same `benchmarks/editor_presentation.py` runs against the old and new source
via PYTHONPATH. Three fresh-process rounds alternate old/new then new/old order,
each with one untimed warm-up and three timed calls per component. Figures below
are the median of the three per-round medians (nine warm calls per variant),
native CPython 3.13.5, default garbage collection. No tests or profiler run
concurrently with these timings. They are not browser, iPhone, cold-start or
whole-search measurements. Equality checks and instrumentation are outside timing.

The 539- and 1,499-piece scenes append widely separated closed 12-curve rings to
the supplied 83-piece completed layout. They are synthetic scaling tests, not
additional user layouts. Full report dictionaries and compact state JSON hashes
match across versions and all measured rounds.

| Scene | Check before / after | State + compact JSON before / after |
| --- | ---: | ---: |
| Completed layout, 83 pieces | 4.31 / 4.28 ms | 4.93 / 3.40 ms |
| Synthetic layout, 539 pieces | 57.54 / 21.05 ms | 27.18 / 18.66 ms |
| Synthetic layout, 1,499 pieces | 414.79 / 60.34 ms | 77.44 / 64.82 ms |
| Reported 59-piece gap, eight suggestions | 2.82 / 2.55 ms | 11.02 / 8.68 ms |

For the large scenes, pair-level near calls fall from 144,449 to 8,482 and from
1,121,249 to 9,485. The 83-piece scene retains the original 3,317 calls. The
1,499-piece diagnostic uses about 85% less elapsed time in this benchmark; this
is not a claim about all dense/custom scenes or application-wide speed.

Actual raw API JSON for the eight-suggestion response falls from 147,131 to
128,754 bytes (12.5%). The completed layout falls from 82,933 to 72,192 bytes.
This measures uncompressed response data, not a proportional network-speed gain.
State dictionaries and drawing values are unchanged; only transport whitespace
is removed.

The full-source Node harness confirms drawing segment counts of 2,572 -> 1,390
for 83 pieces, 15,340 -> 7,774 for 539 pieces, and 42,220 -> 21,214 for 1,499
pieces. One hundred dirty-status checks cause zero large-string re-encodings,
instead of 100. These are work/allocation counts, not browser wall-time claims.

## Validation

Local final standard suite: **1,820 Python tests passed, 28 deselected**
(`not slow and not browser`), and **145 JavaScript tests passed**. Compileall and
whitespace checks passed. Ruff and real Chromium/WebKit validation require the
normal CI gates; no local result is claimed for them.

New differential cases compare indexed diagnostics with the original all-pairs
implementation for mixed 170-piece scenes, negative coordinates, custom headings,
wide/underpass pieces and truncation boundaries. Tests cover deferred bounds,
cache capacity and session lifetime, immutable-to-mutable response isolation,
geometry-only size reuse, live inventory/revisions, exact restore rejection,
compact transport and unchanged export schemas.

Frontend tests cover equal fresh snapshots, changed/reverted settings, no
project-status work on hover-only frames, lazy geometry ownership, flat and
climbing segments, and shortlist/unfiltered picking. A browser pixel regression
compares flat chord interiors and local ramp/level paint order with picked pieces,
on both the local editor and actual production-CSP Pyodide flow. It is not a
claim of pixel-identical anti-aliasing at every polygon boundary. Existing
project/undo/recovery/overlap/train/browser scenarios remain in place.

All eight editor-completion benchmark cases retain identical ordered exact-solution
hashes, node counts, result counts, stop reasons and added-piece lists. Their
independent base-preservation, exact-joint and collision audits pass. The default
reported infinite-inventory gap still yields eight exact 24-piece completions in
1,878 nodes. The supplied unfinished and completed bridge files remain fixtures.

No solver algorithm, budget, bridge clearance, saved layout/project/autosave
format or external dependency is changed. Functional desktop tools, legacy API
support, revision guards, recovery and backup locks are not removed as debloat.
