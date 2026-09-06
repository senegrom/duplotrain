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

The arbitrary-start upper-bound argument was simplified on 6 September
2026: cap an unwired starting port with a self-link, preserve every live
configuration under wiring extension, and apply the known-incoming-edge
bound without shifting time zero. This removes nine modules from the
headline theorem's dependency path; their earlier proofs remain available
and buildable for comparison. The theorem statement and attainment
constructions are unchanged.

**`paper/state-law.pdf`**, with source in `paper/state-law.tex`, presents
the model, the `2^N` ceiling, attainment constructions, and a structured
account of the earlier sharp upper-bound proof. It predates the capping
simplification; use `lean/README.md` for that reduction. Build the paper
with `tectonic state-law.tex`.

**`switch_ceiling_proof.py`** is the perfection exhaustion engine used by
`tests/test_switch_ceiling.py`.
