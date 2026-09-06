# Theory: the lazy-point switch problem

How many distinct switch settings can a single train visit on a wiring
of `N` lazy Y-switches? The exact answer is machine-checked in Lean:

**f(N) = min(2^N, N + 4).**

**`lean/`** contains the proof, with no Mathlib or `native_decide`.
`StateLaw.lean` states `GeneralN.state_law`; `lean/README.md` explains the
model, proof structure, and verification commands. From `lean/`, run
`lake build StateLawAxiomAudit` to check the headline theorem and its exact
axiom list, or `lake build` to check all retained libraries. The toolchain
is pinned.

Two proof simplifications were made on 6 September 2026. First, cap an
unwired starting port and apply the known-incoming-edge bound without
shifting time zero. Second, use one canonical protected-pair history and
split only on whether the old action coordinate is used by the second
construction. A general reserved-coordinate count and a switch-simple
endpoint-agreement lemma replace repeated counting and contradiction
arguments. The headline dependency closure is now 53 modules / 24,104
source lines, down from 65 / 27,846 before the two passes. The theorem,
model, and attainment constructions are unchanged; historical modules
remain buildable. See `lean/README.md` for the arguments and measurement
conventions.

**`paper/state-law.pdf`**, with source in `paper/state-law.tex`, presents
the model, the `2^N` ceiling, attainment constructions, and a structured
account of the earlier sharp upper-bound proof. It predates these proof
simplifications; use `lean/README.md` for the current argument. Build the paper
with `tectonic state-law.tex`.

**`switch_ceiling_proof.py`** is the perfection exhaustion engine used by
`tests/test_switch_ceiling.py`.
