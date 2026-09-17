# Editor cleanup — 17 September 2026

Baseline: `d80346a9d73178dd1e5eaea8c626534c54644fbd`.

## Changes

The shared `duplotrain.editor` module owns Session and API dispatch; `gui` owns
only local HTTP hosting, static asset routes and desktop launch. Existing imports
of `gui.Session`, `gui.dispatch_session`, `gui.make_server`, `gui.run` and the shared
API exception types remain valid. HTTP framing, origin/host, deadline and revision
protections are preserved. The worker imports `editor` and excludes `gui.py`; its
isolated import test refuses any dependency on `http.server` or `webbrowser`.

HTML, CSS and JavaScript are separate packaged source files. Local HTTP and static
hosting use the same `editor.js` and `editor.css`; no bundler or framework was added.
The static builder injects worker boot before the deferred editor script, and the
editor initializes once on DOMContentLoaded. HTML/CSS/JS content participates in
the cache stamp. The former extracted `app.js` is removed from in-place builds.
Node tests load the complete JavaScript through one VM harness instead of slicing
HTML at function names or comments. Real browser tests cover actual startup.

Three unused internal definitions were removed: `solver._outward`,
`_LatticeEngine.heur_dist` and `_congruence.curve_points`. The field engine's active
`heur_dist`, exact arithmetic, interval guards and all final collision audits remain.
Repeated HTTP server lifetime, request, adapter-loading and unchanged-state test
helpers now live in `tests/editor_support.py`; individual scenarios are retained.

## Versioned compact previews

Legacy callers still receive the original full preview by default. The updated
editor opts in with `preview_format: "duplotrain-preview/1"` in API request bodies,
including read-only POST `/api/state`. Python callers can use
`Session.state(preview_format="duplotrain-preview/1")`. GET state and calls omitting
the option preserve the old contract. Unsupported formats reject before any edit.

Compact candidate previews contain `format`, `base_revision`, `base_count`, and
`placements` with drawing-only `width` and sampled `lines`. A candidate reuses the
first `base_count` current placements only when their exact geometry is unchanged.
Otherwise `base_count` is zero and all candidate drawing geometry is included.
The frontend checks the version and revision before composing the shared base and
additions. This keeps full-base ghost tint and touch/hover selection unchanged.

Full exact candidate layouts stay in Session. Candidate indices, revisions, summary
metrics, apply, undo, autosave and the exported layout format are unchanged. Drawing
payloads are fresh, disposable data, never inputs to exact candidate application.

## CI: build once, test and deploy the same artifact

Lint and the Node-only suite run once. Python 3.12 and 3.13 tests, Chromium and
WebKit integration tests, and the deliberately minimal CLI install/export test
remain separate gates. Browser jobs use `.[browser]` rather than rendering/lint
extras. Development extras remain available; `.[test]` is the Python test subset.

One read-only job builds the Pages-ready bundle at the run's exact checkout and
uploads its immutable artifact. Both browsers download that artifact by its ID,
verify its SHA-256 and extract it with the data-only tar filter. Deployment uses
that same run's Pages artifact after all gates succeed, only on `main` and never
for pull requests. The privileged job has no source checkout or build command.
There is no cross-workflow artifact selection, and runtime archive digest checks
remain mandatory even on cache hits. CI duration savings have not been benchmarked.

## Measurements and validation

`PYTHONPATH=src python benchmarks/editor_payload.py --repeats 7` measures state
creation and compact JSON serialization after solving the reported 59-piece gap.
In the local CPython 3.13.5 run, both contracts describe the same eight 24-piece
extensions from the unchanged 23,491-node search:

| Response contract | Bytes | Median state + JSON time |
|---|---:|---:|
| Legacy full previews | 505,794 | 38.132 ms |
| Opt-in compact previews | 128,136 | 9.425 ms |

These are uncompressed JSON sizes and native serialization times, not network,
browser or whole-search timings. The smaller response is 74.7% below the legacy
response. Worker ZIP size was approximately 92.1 kB versus 95.4 kB at baseline; Pyodide still
dominates deployment size and was not changed.

Regression coverage reconstructs legacy ghost geometry from compact payloads,
checks fallback geometry and stale previews, keeps all candidate metrics, tests
mutation isolation and unknown-format atomicity, and exercises state/apply/export/
undo over direct, HTTP and isolated adapter paths. The reported bridge case still
passes exact-joint and full-layout collision audits. Existing browser cases now
also assert the compact contract, including the actual Pyodide worker under CSP.

Local validation: 1,572 Python tests passed in the non-slow/non-browser suite and
73 JavaScript tests passed. Real Chromium and WebKit checks are enforced by CI.
