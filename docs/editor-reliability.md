# Editor reliability, diagnostics and projects

Baseline: `755f7ebef90856e1431e880c4a9fdfe10e8e6020` (19 September 2026).
This branch implements the non-solver review without replacing the newer lattice
oracle, sample caches, shared audits or alternating-endpoint search on main.

## Editing and history

Endpoint picks are tied to the revision at which they were selected. A changed
revision invalidates picks, diagnostic highlights, train traces and ambiguous
selection dialogs. Ordinary armed piece/stone tools may persist intentionally;
old placement indices can never be silently reused as a newly imported piece.
The precise open-end selector uses the selected indices directly, rather than
round-tripping through potentially coincident screen positions.

Undo and redo now include exact layout, track ownership, stone ownership and
sandbox mode. The bounded history shares immutable Layout objects; small ownership
records accompany them. A new edit clears redo, while a no-op or rejected edit
preserves it. Restoring a project is one atomic undoable content change. Actions
have descriptive Undo/Redo titles. Ctrl/Cmd+Z undoes, Shift+Ctrl/Cmd+Z redoes and
Ctrl+Y redoes, without hijacking text-input editing. Viewport and search preferences
are presentation settings, not entries in the engine's undo stack. History is
not serialized into the existing session save format.

Rejected track/stone counts restore the last confirmed number, except when the
user has already typed a newer draft. Normal redraws preserve focused inputs and
unsubmitted text. Action stones have directly editable owned-count inputs.

## Drawing and selection

Painting and picking share elevation-ordered segments. Ramps are subdivided at
up to 8 mm intervals (with a per-segment subdivision cap), so their ordering near
an intersection uses local height rather than a whole-piece average. This is a
sampled 2D view, not a solid-geometry renderer or a new physical collision model.
Equal-height ties follow placement order, consistently in paint and selection.
Picking uses distance to line segments instead of the nearest sample point.

Hover and selection highlight the affected piece. When several tracks overlap,
Remove opens a keyboard-accessible chooser and requires confirmation of the
highlighted piece. Changing revision invalidates that confirmation. Stone removal
keeps its existing more-specific marker hit testing.

A selectable piece list and open-end list provide keyboard-accessible focus,
attach and remove controls, including placing the first armed piece on an empty
layout. Fit preview fits the complete proposed geometry. Repaint requests are
coalesced into animation frames. World-space rail/segment/batch geometry and
compact preview composition are weakly cached; no stale revision is reused.
Flat same-height segments share canvas fill/stroke batches. No browser speedup
percentage is claimed for this change.

## Check layout

`/api/check` is a revision-checked, read-only report. The UI separates:

- connector closure and incompatible joints;
- sampled overlaps using the existing width, height, underpass and direct-neighbour
  rules, with the original 8 mm audit sampling;
- explicit shortages of track and action stones, also visible in sandbox mode;
- pieces marked as provisional in the catalogue.

Findings focus/highlight the relevant pieces. Manual editing/import remains
permissive. The legacy `exactly_closed` property still describes connectors, not
collision-free construction. At most 200 overlapping pairs are returned; reaching
that bound explicitly marks the overlap check incomplete. A clean sampled report
is not a guarantee of real-world clearance. Solver audits remain unchanged.

## Portable projects and local copies

Export layout retains `duplotrain-layout/1`. Save/Open project adds
`duplotrain-project/1`, containing a name, a complete existing
`duplotrain-session/1` snapshot and validated viewport/search preferences. Loading
validates preferences and all session content before any mutation. Slow imports
cannot replace a newer selected file or silently adopt an intervening revision.
The project opener also accepts emergency `duplotrain-session/1` downloads.

Named local saves use separate, append-only UUID slots. Saving the same name again
creates a new copy rather than overwriting another tab's work. A quota/storage
failure is reported; portable download remains available. Existing autosave keys,
locking, migration and stale-tab protections are unchanged. Local slots are not
cloud sync and cannot substitute for a downloaded backup.

## Recovery and cancellation

The worker failure screen offers downloads of the last confirmed layout and full
session without contacting the engine or trusting a possibly newer autosave from
another tab. Restart creates a new worker and restores a copied in-memory confirmed
snapshot. Responses from old worker generations are ignored. Restart resets prior
undo/redo history and search suggestions; the status message says so.

Startup retains its 60-second timeout. Outstanding calls have a two-minute
**inactivity** watchdog reset by engine responses/progress, not a fixed overall
search timeout. A failed restoration keeps emergency download actions available.
The browser Cancel action terminates/restarts its worker from the confirmed
snapshot. It is not pause/resume of a search frontier.

The local HTTP host instead uses a per-request operation ID and cooperative
cancellation. The cancellation endpoint is protected by the same origin, host and
body checks and does not wait for the session lock held by the search. It signals
only the identified active request, and the search raises at its next progress or
publication checkpoint before publishing candidate state. A cancellation arriving
before registration or after completion reports that the request is not active;
the UI permits retry. It never cancels a later unrelated request. Cancellation
latency therefore depends on reaching a checkpoint, not on a hard interrupt.

## Test train

The editor calls the existing drive engine for one selected inward start, using
the engine's default switch tongues. The report includes endless/stopped/buffered/
derailed outcomes, visited pieces, reversals and cycle period. Play, Pause and Step
walk the recorded piece/port trace and highlight its current piece; this is a
piece-level route visualization, not continuous locomotive physics. Editing the
session stops and invalidates playback.

The UI/API limits the selected run to 10,000 steps; a limit produces no verdict.
The library's existing default remains 100,000, with an optional smaller budget and
an explicit DriveLimitError. Incompatible joints are refused before simulation.
The result explicitly concerns this start/default switches only, not every possible
start or switch state. It does not certify physical track. `drive.py` is now included
in the worker for this feature; desktop enumeration/scoring/render modules remain
excluded. No new external dependency was added.

## Validation

Local standard Python suite: **1,735 passed, 26 deselected** (slow/browser).
Complete-source JavaScript/worker suite: **105 passed**. Compileall and whitespace
checks pass. Local browser execution was attempted, but the required Chromium
binary is not installed; real Chromium/WebKit checks remain mandatory in PR CI.
The browser suite includes project/history/diagnostics/train UI, replacement-layout
picks, overlap removal, and the same project/tools plus crash/export/restart flow
against the actual Pyodide worker under the existing CSP.

Compared both checkouts with `benchmarks/editor_completion.py --repeats 1` for
correctness, not timing: all eight cases have identical ordered exact-solution
hashes, nodes, counts, stopping reasons and added-piece lists. All benchmark
candidates passed the existing independent unchanged-base, exact-joint and
whole-layout collision audits. The reported bridge gap still yields eight exact
24-piece extensions: 1,878 nodes in default unlimited direction, 854 in reverse,
1,742 with finite stock in default direction and 718 in reverse.

No production deployment workflow, collision threshold, solver search budget,
exact-layout format or existing autosave schema is changed by this branch.
