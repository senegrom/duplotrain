# The editor

`duplotrain.editor` owns the session (the exact layout, its bounded history,
owned pieces and stones, sandbox mode, candidates and revision) and the API
dispatcher shared by every host. `duplotrain.gui` is only the local HTTP host,
its static asset routes and the desktop launcher; the browser build runs the
same editor module in a Pyodide worker and talks to it through the same
dispatcher. HTML, CSS and JavaScript are packaged source files served by both
hosts. The static build injects the worker bootstrap, stamps the bundle with
the content of every file, and leaves the CLI, the HTTP host, rendering,
exhaustive enumeration and scoring out of the worker archive. Local hosting
security and the revision protocol are described in [security.md](security.md).

## History

Every edit commits the exact layout together with the owned track and stone
counts and the sandbox flag, so undo and redo restore all of them; layouts are
immutable and shared between history entries. The history holds at most 200
entries, each with a label the Undo and Redo buttons show. A new edit clears
redo; a no-op or rejected edit, such as clearing an empty layout, submitting an
unchanged count or a count the session refuses, keeps it. Opening a project is
one undoable change. Ctrl or Cmd+Z undoes, Shift+Ctrl or Cmd+Z and Ctrl+Y redo,
never inside a text input. Viewport and search settings are presentation, not
history, and history is not persisted across engine restarts.

## Picks, dialogs and selection

Endpoint picks, index-based dialogs, diagnostic highlights and train traces
are bound to the revision they were made at; a changed revision discards them,
while an armed piece or stone tool persists. Old placement indices are never
reused for a newly imported piece, and the keyboard selectors act on the
selected indices directly. When several pieces overlap under the pointer, a
click or the Remove tool opens a chooser that owns its allowed targets and its
selected target: confirmation checks the originating revision, the dialog
identity and the selected option, and any other tool invalidates an old dialog.

## Drawing and picking

Pieces are painted and picked as elevation-ordered segments: ramps are
subdivided at 8 mm intervals (at most 256 per segment) so their order near a
crossing follows local height, equal heights follow placement order, and
picking measures the distance to segments rather than to sample points.
World-space rails, segments and paint batches are cached per layout revision,
flat segments of one piece share a fill and stroke, and repaints are coalesced
into animation frames. Hover hit-testing runs at most once per frame at the
latest pointer position, after a cached bounding-box prefilter, and repaints
only when the hovered piece changes; clicks pick immediately. This is a sampled
2D view, not a solid renderer or a collision model.

## Compact previews

The editor requests `preview_format: "duplotrain-preview/1"` on every call,
including the read-only `/api/state` POST; callers that omit it receive the
original full previews. A compact candidate carries `format`, `base_revision`,
`base_count` and `placements` with drawing-only widths and sampled lines. It
reuses the first `base_count` current placements only while their exact
geometry is unchanged; otherwise `base_count` is zero and all geometry is
included. Exact candidate layouts stay in the session; drawing payloads are
never inputs to candidate application.

## Inventory

Owned counts of track and of loose action stones are edited in place. A
rejected submission restores the last confirmed count unless a newer draft has
been typed meanwhile, and redraws preserve focused inputs and unsubmitted text.
Sandbox mode lifts the limits for placing and searching; Check layout still
reports the shortages.

## Check layout

`/api/check` is a revision-checked, read-only report of open connectors and
incompatible joints, sampled overlaps between non-neighbouring pieces under the
solver's width, height and underpass rules, shortages of track and action
stones against the owned counts, and pieces the catalogue marks provisional.
Each finding focuses and highlights its pieces. At most 200 overlapping pairs
are reported, and reaching that bound marks the check incomplete. A clean
report is a model result at 8 mm sampling, not a physical-clearance guarantee,
and manual layouts stay editable whatever it says.

## Autosave

The editor saves the exact layout, the owned track and stone counts and the
sandbox flag in the browser's local storage after every change. A fresh engine
restores that session; a local server that is already running keeps its newer
session. Checkpoints carry unique revisions and Web Locks serialise writes
across tabs: a tab that sees another writer pauses its autosave and asks you to
export before reloading, and redrawing or closing a stale tab never rewrites a
newer checkpoint. Saves from older editor versions migrate read-only into a new
storage key, isolated from tabs still running the old editor. Without safe
locking or storage the editor warns you to export instead, and a storage or
recovery error is shown without overwriting an unreadable checkpoint. Autosave
is device- and browser-local, not a backup: export JSON or save a project for a
portable copy. Undo history is not persisted across engine restarts.

## Projects and local copies

Export JSON keeps the `duplotrain-layout/1` format. A project
(`duplotrain-project/1`) adds a name, the complete `duplotrain-session/1`
snapshot and validated preferences: the viewport and the search settings
(added-piece limit, slop, reversing). Opening validates everything before any
mutation, a slow file cannot replace a newer selection or adopt an intervening
revision, and the opener also accepts an emergency session download.

Local copies are append-only slots under a per-path key with a random
identifier and a save timestamp; saving twice creates two copies, and the list
shows name, time, piece count and identifier, newest first, keeping unreadable
copies visible. Rename and delete act on the selected copy only, recheck its
exact bytes inside a per-slot Web Lock, and are refused where locks are
unavailable. A separate indicator reports whether the content, name, viewport
or search settings changed since the last project save or open in this tab.
Autosave is independent of all of this, and local copies are not a backup
service.

## Recovery and cancellation

When the engine fails, the overlay offers downloads of the last confirmed
layout and session from this tab's own state, and a restart that creates a new
worker and restores a copy of that snapshot; responses from an old worker
generation are ignored, and a restart resets undo history and suggestions and
says so. Startup times out after 60 seconds; outstanding calls time out after
two minutes without a response or progress report. In the browser, Cancel
restarts the worker from the confirmed snapshot. On the local host a search
carries a random `operation_id`; `/api/cancel` sets its event without waiting
for the session lock, the search raises at its next progress or publication
checkpoint with HTTP 409 and `code: "cancelled"`, the layout stays unchanged,
and a cancellation for a request not yet registered or already finished reports
that it was not active.

## Test train

`/api/drive` runs the drive model from one selected inward start with the
chosen initial switch positions (`train_switches` in the state lists the
choices, `switch_states` in the request selects them) for at most 10,000
steps; a run that reaches the limit makes no verdict, coverage or terminal
claim. The report gives the outcome, the traversals, the repeating cycle, the
reversals, the visited and unvisited drivable pieces, and a separate terminal
event (stop stone, buffer, open end or dead route) with the piece and port it
happened at. Play, Pause and Step walk the trace and highlight the current
piece; toggles highlight unvisited track and the repeating cycle. Changing the
start, a switch or the layout invalidates the trace. This is a piece-level
model of one start, not a physical simulation or a claim about every start.

## Checks and deployment

The application workflow lints, runs the node suite once, runs the Python
suite on two interpreters and on a minimal install, builds the Pages bundle
once as an immutable artifact, and runs the Chromium and WebKit browser suites
against that artifact after verifying its digest. The deploy job of the same
run publishes that artifact only after every gate passes on a push to `main`;
it has no checkout and no build step, and nothing is selected across
workflows.
