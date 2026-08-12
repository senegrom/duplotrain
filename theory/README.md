# Theory: the lazy-point switch problem

The mathematical side of the project: how many distinct switch settings
can a single train visit on a layout of N lazy Y-switches?  The
conjectured law is f(N) = min(2^N, N + 4).  Machine-checked status:
**N + 4 ≤ f(N) ≤ N + 5 for every N ≥ 3**, fully symbolic in N on both
sides; the last additive unit is reduced to four explicit residual
geometries (see `lean/README.md`).

Contents:

* **`lean/`** — the machine-checked results (Lean 4, no Mathlib):
  the `N+5` upper bound (`StateLawNAddFive.lean`, via the unconditional
  known-incoming-edge `N+4` core), the symbolic `N+4` lower-bound
  family (`StateLawLowerBound.lean`), the sharpened residual frontier
  for the exact `N+4` law, the exhaustive small-N anchors, and the
  permanent axiom audit.  `lean/README.md` is the guide.
* **`lazy-point-theory.md`** — the paper trail of the earlier
  register-machine (echo) program; historical, superseded by the track
  proofs.
* **`switch_ceiling_proof.py`** — the perfection exhaustion engine
  (no perfect layout has ≥ 3 switches), used by
  `tests/test_switch_ceiling.py`.
* **`tools/bstates.py`** — the python state-count prober that
  discovered the extremal `N+4` family and cross-checks
  `lean/FamilyLowerBound.lean`.

Build the Lean proofs: `cd lean && lake build` (elan; toolchain pinned).
