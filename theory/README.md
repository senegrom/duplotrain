# Theory: the lazy-point switch problem

The mathematical side of the project: how many distinct switch settings
can a single train visit on a layout of N lazy Y-switches?  The conjectured
law is f(N) = min(2^N, N + 4).  The general linear bound
f(N) ≤ 34N + 3 is now machine-checked; the sharp coefficient-one bound is
**open**.

Contents:

* **`lean/`** — the machine-checked results (Lean 4, no Mathlib).
  `lean/StateLaw.lean` states the sharper open target in the raw language of
  tracks and switches; `lean/TrackQuantitative.lean` proves the unconditional
  `34N+3` theorem; `lean/README.md` has the full theorem tables
  (exhaustive small-N proofs, the general-N cascade/retrace/reflector
  theorems, the echo machine, the pigeonhole ceiling f(N) ≤ 2^N, the
  heat monovariant, and the conditional counting scaffold).
* **`lazy-point-theory.md`** — the paper trail: T1–T10, the forest
  compilation, the echo machine, the nesting argument, the honest
  status of lemmas B and C.
* **`echo_machine.py`** — the register-machine simulator and the
  exhaustive sweeps backing B and C empirically.
* **`switch_ceiling_proof.py`** — the perfection exhaustion engine
  (no perfect layout has ≥ 3 switches), used by
  `tests/test_switch_ceiling.py`.

Build the Lean proofs: `cd lean && lake build` (elan; toolchain pinned).
