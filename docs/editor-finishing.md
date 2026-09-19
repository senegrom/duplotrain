# PR #18 finishing pass — 19 September 2026

Baseline: `1abec36d4fe886626bc6eca37e289dc4e62f65e4` on
`fix/editor-reliability-projects`. This implements all six follow-up review items.
PR #18 was merged and its original branch deleted during this work. The finishing
changes are published separately on `fix/editor-finishing`, based on `07b2c1d`,
without merging or deploying them. The upstream no-unchanged-hover-repaint
optimization is preserved alongside frame-coalesced hit-testing.

## Selection safety and no-op history

The overlap chooser now owns its target and allowed candidate set. Confirmation
rechecks the originating revision, current dialog identity, selected option and
membership; it cannot delete the global selection from another control. Other
selection/tool actions invalidate the old dialog, and highlighting follows the
chooser's own target. Tests exercise the precise-selection dropdown, replacement
choosers, stale revisions, cancellation and direct changes to global selection.

Clear on a genuinely empty layout returns without changing history, redo,
candidates or revision. Clearing a non-empty layout remains undoable. Import,
restore and candidate-publication revision semantics have not been generalized or
changed in the name of no-op detection.

## Train terminal events and coverage

`DriveReport.terminal` is an optional `DriveTerminal` record: placement, inward
entry, reached port (or midpoint), and reason. Stop stones, buffers, open ends and
dead routes are distinguished. This is an additive report field with a default;
it does not add artificial traversals, alter loop periods or change outcomes.
Playback has a separate final event, including an immediate stop with no completed
traversals. Its highlight reaches the actual stopped piece and playback stops
there. Endless runs have no terminal event; an exhausted run budget makes no
terminal-position or coverage claim.

The editor shows visited/total **drivable** pieces, excluding buffer-only pieces
from the coverage denominator as the existing engine does. Separate toggles
highlight unvisited track and the eventual repeating cycle. Overlays are
piece-level, not continuous locomotive paths. Changing the layout, starting point
or initial switch choices invalidates the old trace and overlays; delayed results
from a previous selection are not adopted.

Initial switch selectors expose the existing drive model's valid facing-port
choices. Submitted indices and ports are strictly validated before simulation;
missing choices use the same defaults as before. The result records the actual
initial settings. These are per-run controls, reset with a new layout revision,
not persistent layout geometry or project preferences. This remains a bounded
single-start model result, not a claim about all starts/settings or physical track.

With the supplied bridge fixtures, start `(0, 0)` and default switches, both the
59-piece unfinished layout and the 83-piece completed layout visit 41 drivable
pieces. Each records 73 traversals, with its 26-step repeating cycle starting at
index 47; the completed layout has 42 unvisited pieces in this particular run.
Regression tests assert those values without claiming other switch settings have
the same coverage.

## Distinguishable, safely managed local backups

New local copies retain separate UUID keys and add an ISO save timestamp. Labels
show name, local save time, piece count and a short copy identifier; copies sort
newest first. Existing timestamp-free copies remain readable and show 'date
unknown'; malformed copies remain visible rather than being deleted automatically.
The current selection survives list refreshes when its key still exists.

Explicit Rename/Delete actions display the selected copy in a confirmation panel.
The operation captures its key and exact bytes, then rechecks them inside an
origin-scoped per-slot Web Lock before changing only that key. A changed or deleted
copy, cancelled dialog, or changed selection is not overwritten. Rename preserves
its original save timestamp; neither action mutates the current design. With no
Web Locks support, destructive management refuses with an explanation; portable
download and non-overwriting new copies remain available. Local copies are not
cloud synchronization, and locks coordinate cooperating tabs rather than arbitrary
external modifications to browser storage.

A separate project indicator tracks content/name, viewport and search settings
against the last successful save/open in this tab. Autosave is explicitly separate.
Failed local saves do not mark the project saved. Large immutable session snapshots
are serialized once for this comparison, not once per hover event. The portable
layout/session schemas and existing autosave coordination are unchanged. A
project download marks the prepared download as the baseline; the browser cannot
certify that a user ultimately retained the downloaded file.

## Hover work and conservative picking

Hover events retain the latest pointer position and request a frame. At most one
hover hit-test runs in that animation frame; click actions still pick immediately.
Pending hover is discarded on leave, dragging, revision/geometry changes or
selection transitions. A weakly cached bounding-box prefilter skips distant
placements before the existing segment-distance and elevation ordering checks.
The bounds have an outward floating-point guard and conservatively admit
non-finite bounds rather than falsely rejecting a possible hit.

The event regression sends 100 pointer movements before one frame and observes
one hit-test using the latest coordinates (previously 100). Filtered and unfiltered
picking are compared on crossings, ramps, translated layouts and different zooms.
The independently added upstream optimization is retained: unchanged hover does
not repaint track, while non-hover redraw requests still do. This is a work-count
result, not a measured browser wall-time speedup.

## Validation

Local standard Python suite: **1,770 passed, 27 deselected** (slow/browser).
Complete-source JavaScript/worker suite: **133 passed**. Compileall and whitespace
checks pass. The new focused Python file supplies 32 parametrized cases, and the
new JavaScript file supplies 27 tests; existing JavaScript fixtures are shared
without removing their scenarios. The upstream unchanged-hover regression is
adapted to count actual paints after coalesced hit-testing.

The eight-case editor completion benchmark retains identical ordered exact-layout
hashes, node counts, result counts, added-piece lists and stop reasons against the
baseline. The benchmark independently audits unchanged original placements/links,
exact joins and collisions. The reported default unlimited gap still yields eight
24-piece completions in 1,878 nodes. No new search timing claim is made.

The shared browser flow exercises backup versions/rename/delete/dirty state,
terminal stopping events, actual bridge coverage, overlay controls and initial
switch settings on both local hosting and the built Pyodide app under its existing
CSP. Separate browser regressions cover empty-Clear redo and overlap/precise-list
selection interference. Local browser binaries and Ruff are unavailable in this
environment; their results must come from PR CI, not be inferred from unit tests.

No solver search algorithm, search budget, collision threshold, dependency,
production workflow, existing layout format or autosave format was changed.
