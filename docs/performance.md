# Editor performance and worker packaging

Exact arithmetic remains in Q(sqrt(2), sqrt(3)). Rational products skip zero
cross-terms, subtraction works directly on coefficients, and existing Fraction
coefficients are reused. Alg now enforces its documented immutability so shared
exact values cannot corrupt geometry caches; copying and pickling still work.

The shared caches are bounded: 128 piece-traversal entries, 128 local centreline
sample entries, and 4,096 exact port transforms. Keys contain geometry, not just
catalogue ids. The port cache holds no Layout or Session. Public list containers
are fresh copies; cached samples are immutable tuples. No validation result,
revision check, collision decision or complete mutable session response is cached.

Ring/bridge completion composes repeated ramp/span units and reuses exact prefixes
within one search. Its enumeration order, inventory limits and collision checks
are unchanged. Candidate cards reuse the size already computed in their preview.

The frontend retains catalogue controls and candidate cards while their displayed
metadata is unchanged, updating counts, availability and selected-tool styling in
place. Redraws preserve focus and unsubmitted inventory values. Catalogue changes
rebuild the relevant controls; new candidate revisions clear stale selection. Card
comparison does not serialize preview geometry, and event handlers use current data.

The worker ZIP omits static/editor.html (already served separately), cli.py and
render.py. Those files remain in the desktop Python package. The worker archive
stays content-stamped, deterministic and self-hosted. Pyodide itself is unchanged.

Regression coverage lives in tests/test_performance_contracts.py,
tests/test_worker_bundle.py, tests/web/render-reuse.test.cjs and the browser suite.
Tests compare exact arithmetic, cache isolation/bounds, worker API round-trips and
DOM identity rather than making machine-dependent wall-clock assertions.

## Second-pass cold-start and search overhead

Port transforms split repeated local rotation from per-placement translation. Connector
geometry has only 24 possible headings, so exact radical multiplication is reused across
placements while every returned Pose remains exact. Floating centreline evaluation keeps
its original operation order; only the 24 sin/cos pairs are cached, so sampled float
values and borderline collision comparisons are bit-for-bit unchanged.

Alg hashes are memoized lazily. This avoids paying tuple/Fraction hashing for the many
short-lived exact values that are never dictionary keys, while repeated exact-position
lookups reuse a stable hash. Built-in catalogue parsing and solver symmetry/span metadata
are likewise bounded and cached; public catalogue mappings remain fresh caller-owned
objects and all cached piece objects are immutable.

Collision rollback now exploits its strict LIFO contract: the previous maximum piece
width is restored in O(1), and each grid cell removes the just-added contiguous suffix
instead of reverse-scanning once per sample point. The collision predicate, cell layout,
clearance rules, and sample coordinates are unchanged.

The Pyodide worker now uses a minimal package marker and excludes the desktop-only drive,
explore, network-enumeration and scoring helpers in addition to the CLI, renderer and
separately served editor HTML. Those modules remain in normal Python installs. The worker
still contains every transitive dependency of gui.Session/solve and its isolated API
round-trip test exercises state, edit, solve, apply, import, export and restore.


## Third-pass collision and editor-state reuse

Collision grid buckets group one placement's samples per occupied cell instead of
repeating placement metadata for every point. LIFO rollback removes one grouped cell
entry at a time, and each candidate query resolves a grid-cell neighbourhood once even
when many 8 mm samples share that same 96 mm cell. Collision thresholds, height and
underpass rules, neighbour exemptions, and sample coordinates are unchanged.

Layout footprint expansion is translation-invariant, so the sampled local footprint is
cached by immutable path geometry, width, overhang and one of the 24 headings; each
placement then contributes only a translated envelope. Editor state serialization also
computes each exact connector pose once and shares it between layout JSON, joint audits
and matable-pair detection. Returned JSON remains freshly owned by the caller.
