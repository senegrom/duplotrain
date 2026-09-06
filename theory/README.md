# Theory: the lazy-point switch problem

How many distinct switch settings can a single train visit on a wiring
of `N` lazy Y-switches? The exact answer is machine-checked in Lean:

**f(N) = min(2^N, N + 4).**

**`lean/`** contains the proof, with no Mathlib or `native_decide`.
`StateLaw.lean` states `GeneralN.state_law`; `lean/README.md` explains the
model, proof structure, and verification commands. From `lean/`, run
`lake build StateLawAxiomAudit` to check the headline theorem and its exact
axiom list, or `lake build` to check every library. The toolchain is pinned.

## Proof simplifications

The upper bound first completes every free port on the existing switches
with a self-link. This preserves every original live configuration and
makes the finite exploration probes automatically live, without shifting
time zero or imposing totality on the original wiring.

Inside the dynamical argument, one shared construction history supports
the two budgets `(N+2)+2` and `(N+3)+1`. Disturbed traversals are analysed on
the selected outward route, leaving only stem capture versus branch repair.
All-time phase covers use boundary invariants under positive-length
excursions instead of enumerated contact periods. Capture is a suffix of
ordinary traversal. Shortened reflectors reuse their original construction
witnesses rather than rebuilding them in the later tongue state.

The retained development has 53 Lean files and 16,077 source lines,
including its 19-line axiom audit; the headline import closure has 52
modules and 16,058 lines. Source lines include comments and blank lines.
The theorem statement, model, finite-state ceiling, attainment constructions,
and exact axiom audit are unchanged. Git history retains superseded proofs.

**`paper/state-law.pdf`**, with source in `paper/state-law.tex`, presents
the model, the `2^N` ceiling, attainment constructions, and a structured
account of the simplified sharp upper bound. It includes total completion,
the shared-history budgets, and the trace-reuse arguments. Build with
`tectonic state-law.tex`, or run `pdflatex state-law.tex` twice.

**`switch_ceiling_proof.py`** is the perfection exhaustion engine used by
`tests/test_switch_ceiling.py`.

Spatial loops use a one-bit invariant instead of contact/avoidance period
cases. The general two-phase reflector contract now also handles arbitrary
grooved lobes and stay-reflector splices. Their four-corner (or collapsed
two-corner) orbit is preserved by positive excursions, which provide both
liveness and pointwise phase bounds without calculating periods. One shared
first-contact theorem handles both arbitrary routes with repeated switches
and the switch-simple manufactured routes. The paper and Lean guide describe
these reductions; the elementary `2^N` ceiling remains a one-line observation
in the paper's assembly rather than a standalone section.

A grooved approach followed by any positive return inside a two-vector cover
now closes one common repair invariant, even when the approach meets the
action switch. Backward contacts and same-exit cycles synchronize after their
first arrival with an already-grooved spatial loop, avoiding transient-lap and
period calculations. The endpoint-coordinate law also supplies one-change
phase bounds and productive-writer survival directly.
