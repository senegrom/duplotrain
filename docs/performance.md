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
