# Theory: the lazy-point switch problem

The mathematical side of the project: how many distinct switch settings
can a single train visit on a layout of N lazy Y-switches? The sharp law is
now machine-checked:

**f(N) = min(2^N, N + 4) for every N ≥ 1.**

The symbolic Lean proof gives the `N + 4` upper bound for every `N`; the
matching construction gives `N + 4` states for every `N ≥ 3`, while the
finite-state ceiling supplies `2^N` and the exhaustive small cases give
`f(1) = 2` and `f(2) = 4`.

Contents:

* **`lean/`** — the machine-checked results (Lean 4, no Mathlib):
  `StateLawNAddFourSharp.lean` proves the sharp raw `N+4` theorem over
  tracks and switches; `StateLawLowerBound.lean` gives the matching family;
  the exhaustive small-N anchors and the permanent axiom audit remain
  separate from the symbolic proof. `lean/README.md` is the guide.
* **`lazy-point-theory.md`** — the paper trail of the earlier
  register-machine (echo) programme; historical and independent of the
  completed physical-track proof.
* **`switch_ceiling_proof.py`** — the perfection exhaustion engine
  (no perfect layout has ≥ 3 switches), used by
  `tests/test_switch_ceiling.py`.
* **`tools/bstates.py`** — the Python state-count prober that discovered the
  extremal `N+4` family behind `lean/StateLawLowerBound.lean`.

Build the Lean proofs: `cd lean && lake build` (elan; toolchain pinned).
