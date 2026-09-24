# The editor

`duplotrain.editor` owns the session (the exact layout, its bounded history,
owned pieces and stones, sandbox mode, candidates and revision) and the API
dispatcher shared by every host. `duplotrain.gui` is only the local HTTP host,
its static asset routes and the desktop launcher; the browser build runs the
same editor module in a Pyodide worker and talks to it through the same
dispatcher. HTML, CSS and JavaScript are packaged source files served by both
hosts: `editor.js` owns the API snapshot and the interaction state, and five
companion deferred scripts hold derived canvas and picking geometry, project
and backup presentation, train presentation, interactive jobs and offline controls; their load order and the
single DOMContentLoaded initialiser are part of the tested contract, and the
local host serves them from an explicit allowlist. The static build injects
the worker bootstrap, stamps the bundle with the content of every engine and
editor source, and leaves the CLI, the HTTP host, rendering, exhaustive
enumeration and scoring out of the worker archive. Local hosting
security and the revision protocol are described in [security.md](security.md).

## History

Every edit commits the exact layout together with the owned track and stone
counts and the sandbox flag, so undo and redo restore all of them; layouts are
immutable and shared between history entries. The history holds at most 200
entries, each with a label the Undo and Redo buttons show; beyond that the
oldest entry becomes the start, so every remaining step undoes exactly the edit
its label names. A new edit clears redo; a no-op or rejected edit, such as
clearing an empty layout, submitting an unchanged count or a count the session
refuses, keeps it. Opening a project is one undoable change. A session recovered
into an engine (autosave on a fresh engine, a worker or server restart) starts a
new history instead: undoing it could only empty the engine, and autosave would
then replace the recovered checkpoint. Ctrl or Cmd+Z undoes, Shift+Ctrl or Cmd+Z and Ctrl+Y redo,
never inside a text input. Viewport and search settings are presentation, not
history, and history is not persisted across engine restarts.

## Picks, dialogs and selection

Endpoint picks, index-based dialogs, diagnostic highlights and train traces
are bound to the revision they were made at; a changed revision discards them,
while an armed piece or stone tool persists unless an edit was refused as stale,
which disarms it. Old placement indices are never
reused for a newly imported piece, and the keyboard selectors act on the
selected indices directly. When several pieces overlap under the pointer, a
click or the Remove tool opens a chooser that owns its allowed targets and its
selected target: confirmation checks the originating revision, the dialog
identity and the selected option, and any other tool invalidates an old dialog.

## Drawing and picking

Pieces are painted and picked as elevation-ordered segments: climbing edges
are subdivided at 8 mm intervals (at most 256 per segment) so their order near
a crossing follows local height, flat chords stay whole, equal heights follow
placement order, and picking measures the distance to segments rather than to
sample points. One lazily built record per layout holds its world-space
segments, per-piece groups, paint batches and bounds, flat segments of one
piece share a fill and stroke, and repaints are coalesced into animation
frames. Hover hit-testing runs at most once per frame at the latest pointer
position, visits only the pieces whose bounds contain the pointer, and repaints
only when the hovered piece changes; clicks pick immediately. A right click
removes the stone or piece under the pointer, through the same chooser when
pieces overlap. This is a sampled 2D view, not a solid renderer or a collision
model.

Conservative viewport bounds skip off-screen track batches and markers without
changing global paint order or picking. While the view or geometry keeps
changing (a pan, a zoom, new track) every frame paints the track directly. Once
a frame repeats, one reused offscreen surface holds the stable track while hover,
selection, train and constraint overlays change; geometry, view, viewport or
device-pixel-ratio changes invalidate it. The raster is limited to eight million
pixels (about 32 MB of RGBA data); larger canvases or hosts without a secondary
canvas use direct painting.

## Compact previews

The editor requests `preview_format: "duplotrain-preview/1"` on every call except
`/api/export`, including the read-only `/api/state` POST; callers that omit it
receive full previews. A compact candidate carries `format`, `base_revision`,
`base_count` and `placements` with drawing-only widths and sampled lines. It
reuses the first `base_count` current placements only while their exact geometry
is unchanged; otherwise `base_count` is zero and all geometry is included. Exact
candidate layouts stay in the session; drawing payloads are never inputs to
candidate application.

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
Each finding focuses and highlights its pieces. Layouts of 128 pieces or more
shortlist candidate pairs through the collision field's bounds index and run
the same pair tests on that superset. At most 200 overlapping pairs are
reported, and reaching that bound marks the check incomplete. A clean
report is a model result at 8 mm sampling, not a physical-clearance guarantee,
and manual layouts stay editable whatever it says.

## Autosave

The editor saves the exact layout, the owned track and stone counts and the
sandbox flag in the browser's local storage after every change. Storage is keyed
by the app's directory, so its URL with and without `index.html` shares one
autosave and one list of local copies; an autosave an older editor kept under
the `index.html` spelling moves to that key, or becomes the local copy "Autosave
from index.html" when the directory already has one. A fresh engine restores
that session; a local server that is already running keeps its newer session,
and a tab that loses the race to restore a fresh engine shows what the other tab
restored and keeps autosaving. After a server restart the first tab to act
restores the newest confirmed session into the new server: its own, unless
another tab autosaved since this tab last did, in which case that checkpoint.
Checkpoints carry unique revisions and Web Locks serialise writes across tabs: a
tab that sees another writer pauses its autosave and asks you to export before
reloading, and redrawing or closing a stale tab never rewrites a newer
checkpoint. Saves from older editor versions migrate read-only into a new
storage key, isolated from tabs still running the old editor. Without safe
locking or storage the editor warns you to export instead, and a storage or
recovery error is shown without overwriting an unreadable checkpoint. A saved
session this editor cannot read, or its engine refuses, keeps autosave off until
you act on it, since a newer editor may read it: its notice offers a download (a
session file that Open project reads, or the raw text of one that cannot be
read) and a discard, which asks for confirmation, deletes it only if no other
tab has replaced it since, and turns autosave back on for this tab's session. A
restore that fails for another reason, such as a lost connection, keeps the
session without offering to discard it. Autosave is device- and browser-local,
not a backup: export JSON or save a project for a portable copy.

## Projects and local copies

Export JSON keeps the `duplotrain-layout/1` format. A project
(`duplotrain-project/1`) adds a name, the complete `duplotrain-session/1`
snapshot and validated preferences: the viewport and the search settings
(added-piece limit, slop, reversing, and optional ranking, piece exclusions and
room/keep-out constraints). Opening validates everything before any
mutation, a slow file cannot replace a newer selection or adopt an intervening
revision, and the opener also accepts an emergency session download.

Local copies are append-only slots under the app's key with a random
identifier and a save timestamp; saving twice creates two copies, and the list
shows name, time, piece count and identifier, newest first, keeping unreadable
copies visible. Rename and delete act on the selected copy only, recheck its
exact bytes inside a per-slot Web Lock, and are refused where locks are
unavailable. A separate indicator reports whether the content, name, viewport
or search settings changed since the last project save or open in this tab; it
compares a cached session string with a small settings key and is refreshed on
explicit redraws, not on hover frames.
Autosave is independent of all of this, and local copies are not a backup
service.

## Recovery and cancellation

When the engine fails, including a fatal error the Python runtime reports
while answering a request, the overlay offers downloads of the last confirmed
layout and session from this tab's own state, and a restart that creates a new
worker and restores a copy of that snapshot; responses from an old worker
generation are ignored, and a restart resets undo history and suggestions and
says so. Startup times out after 60 seconds; outstanding calls time out after
two minutes without a response or progress report. The editor's searches and
route analyses are interactive jobs that pause without restarting the worker
([search-jobs.md](search-jobs.md)); the synchronous `/api/solve` route serves API
clients. On the local host such a search may carry a random
`operation_id`; `/api/cancel` sets its event without waiting for the session
lock, the search raises at its next progress or publication checkpoint with
HTTP 409 and `code: "cancelled"`, the layout stays unchanged, and a cancellation
for a request not yet registered, past its last checkpoint or already finished
reports that it was not active.

## Interactive completion

Find more, Search harder, pause and resume, ranking, room and keep-out
rectangles and Close all gaps are described in [search-jobs.md](search-jobs.md),
with their limits and what a ranking or a bounded search does not prove.

## Test train

`/api/drive` runs the drive model from one selected inward start with the
chosen initial switch positions (`train_switches` in the state lists the
choices, `switch_states` in the request selects them) for at most 10,000
steps; a run that needs more makes no verdict, coverage or terminal claim. The report gives the outcome, the traversals, the repeating cycle, the
reversals, the visited and unvisited drivable pieces, and a separate terminal
event (stop stone, buffer, open end or dead route) with the piece and port it
happened at. Play, Pause and Step walk the trace and highlight the current
piece; toggles highlight unvisited track and the repeating cycle. Changing the
start, a switch or the layout invalidates the trace. This is a piece-level
model of one start, not a physical simulation or a claim about every start.

Route analysis can additionally search all initial switch assignments for the
selected start or all starts, optimise lifetime or cycle coverage, and load a
witness into these trace controls. It reports universal properties only after
all requested runs complete within the bounds; see [search-jobs.md](search-jobs.md).

## Offline installation and updates

The browser-engine app offers **Make available offline** on HTTPS or localhost.
It is opt-in; simply opening the app does not install a service worker. The build
emits a manifest of the exact editor, engine, runtime, icon and manifest assets,
including byte lengths and SHA-256 digests. An offline version is named by a
digest of what that manifest serves, so a build whose served content differs
installs as a new version even where its build stamp is unchanged (the Pages CSP
tag, the web manifest and the icons are not part of the stamp). The engine
archive counts by its entries rather than its compressed bytes, and text assets
ship with LF newlines, so one commit names one offline version on every build
host. An offline version is marked
ready only after all resources verify and the completion marker is written. A
download fails once no bytes arrive for a minute, not when a slow but steady
link needs longer for a large runtime file. Cached
responses preserve the build's CSP and MIME headers. Project/autosave data is
not stored in these application-code caches.

The status shows the loaded build and whether the complete corresponding version
is available. Update checks install a verified waiting version without forcing
activation or reloading an unsaved design. Applying it requires confirmation,
rechecks readiness and waits for activation before reloading. Download a project
first: an explicit reload still resets in-memory undo and search progress.

A failed installation, failed digest or storage quota error does not replace an
older verified version or delete unrelated application caches. Versioned asset
URLs keep old live tabs on coherent resources: activating a version keeps the
version that was active before it, which tabs opened before the update still
run, and deletes the other older versions, such as a waiting update that was
superseded; a version that is still installing is left alone.
Browser eviction or missing entries can remove offline availability, so readiness
is checked and installation can be repaired online. This is not a permanent
storage guarantee or a substitute for portable project backups. The desktop local
HTTP host remains a separate offline-capable Python program and does not install
this browser service worker.

## Checks and deployment

The application workflow lints, runs the node suite once, runs the Python
suite on two interpreters, smoke-tests the CLI on a minimal install, builds the
Pages bundle once as an immutable artifact, and runs the Chromium and WebKit
browser suites against that artifact after verifying its digest. The deploy job
of the same run publishes that artifact only after every gate passes on a push
to `main` or a manual run there; it has no checkout and no build step, and
nothing is selected across workflows. Because the Pages action selects the
artifact by name, the deploy job first downloads it by the build job's artifact
ID and checks the same digest: a same-name upload from any other job would carry
a new ID, and the deploy would fail rather than publish it.

The offline browser test boots the built app in a fresh profile under the
production CSP, installs the offline version, stops the resource server, reloads
the real engine from the cache and recovers the confirmed session; any page error
fails it. Chromium serves it over HTTP loopback. WebKit needs HTTPS under that
policy, so its variant runs only on the disposable GitHub-hosted runner, which
installs a short-lived test CA by explicit opt-in (`DUPLOTRAIN_TEST_SYSTEM_CA=1`)
and removes it afterwards; elsewhere it is skipped. `tests/browser/tls.py` and
`tests/browser/test_path_web.py` give the details.
