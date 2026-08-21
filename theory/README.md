# Theory: the lazy-point switch problem

The mathematical side of the project: how many distinct switch settings
can a single train visit on a layout of N lazy Y-switches?  The answer is
machine-checked as a single Lean theorem:

**f(N) = min(2^N, N + 4).**

Contents:

* **`lean/`** — the machine-checked proof (Lean 4, no Mathlib, no
  `native_decide`).  `StateLaw.lean` states the one headline theorem
  `GeneralN.state_law`; every other file supports it.  `lean/README.md`
  is the guide.  Build from `lean/` with `lake build` (elan; toolchain
  pinned); the build ends by auditing the theorem's axioms.
* **`paper/state-law.pdf`** — the human-readable proof: a 12-page paper
  extracted from the Lean development (complete for the model, the `2^N`
  ceiling, and every attainment construction; a structured account of the
  sharp `N+4` upper bound).  Source in `paper/state-law.tex`; build with
  `tectonic state-law.tex`.
* **`switch_ceiling_proof.py`** — the perfection exhaustion engine
  (no perfect layout has ≥ 3 switches), used by
  `tests/test_switch_ceiling.py`.
