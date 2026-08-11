# Unified upper-bound proof work

Branch: `agent/upper-bound-unified`

This branch is the visible integration point for the active upper-bound
programmes.  It is an octopus merge of:

* `agent/upper-bound-current` at `dacb3110846c26043e85fd6c2f4e545bfd299168`;
* `agent/coefficient-one-current` at `5fb946657966dc5d7f9d83cd2858c187b26651e2`;
* `codex/first-repeated-edge-proof` at `d615f15a2249933dc27d528ac6b4c87b508a4f7e`.

The merge commit is `43a8ca081bfdb3fc20b4baa9ac2bd222ed6f0d0c`.
The independent Codex module was retained under the nonconflicting name
`theory/lean/CodexStateLawTwoSharp.lean`.

## Strongest unconditional bound

The strongest previously kernel-checked endpoint included in this tree is:

```text
known incoming edge:  2*N + 6
arbitrary start:       2*N + 7
```

Its public source endpoint is:

```text
theory/lean/StateLawTwoSharper.lean
```

The independently developed Codex proof of the weaker arbitrary-start bound
`2*N + 8` is also preserved as `CodexStateLawTwoSharp.lean`.  It contributes
additional two-history and two-reflector lemmas even though its final numeric
endpoint is one larger.

## Coefficient-one milestones

### Conditional `N + 7`

`theory/lean/CoefficientOneSeven.lean` proves the exact payoff of the current
six-event reduction:

```text
sharp six-event residue impossible
  => known incoming edge: N + 6
  => arbitrary start:      N + 7
```

The implication is kernel-checked; the raw geometric residue remains open.

### Target `N + 6`

The sharp target is:

```text
known incoming edge:  N + 5
arbitrary start:       N + 6
```

It follows from the raw assertion that at most four globally novel
repeated-writer events occur after entry through a known physical edge.

## Integrated coefficient-one progress

### Pointwise simple-cycle tail

The following green modules from `agent/coefficient-one-current` are present:

```text
theory/lean/TraceRetainingFirstRevisit.lean
theory/lean/TraceRetainingBABASecondRepeat.lean
theory/lean/PointwiseSimpleCycleTail.lean
```

They retain the transient and stable switch-simple laps and prove that every
positive raw time after the reached same-exit repeat has the single settled
restricted tongue vector.  This removes the tongue-state uncertainty from the
BABA simple-cycle leaf; only its placement relative to the selected closes
remains.

### Selected self-link cycle closure

`theory/lean/TripleSelfLinkSimpleCycleTail.lean` closes both outcomes of the
selected periodic self-link branch: the opposite-reflector outcome and the
stable simple-cycle outcome each give an explicit two-vector tail which
rotates back to the selected close.

### Two-history contact reduction

The integrated files

```text
theory/lean/TwoHistoryUnionCharge.lean
theory/lean/ContactHistorySharpBound.lean
```

show that changing first old-support contacts, and unchanged contacts not
following the old selected route forward, have a two-vector novelty cover over
an exact history of length at most `N + 3`.  The sole local contact residue is:

```lean
FacingForwardContactTwoNoveltyLaw
```

Proving that law gives the local `N + 5` count immediately.

### Independent two-reflector assembly

`theory/lean/CodexStateLawTwoSharp.lean` retains the other agent's complete
source for an unconditional two-reflector assembly.  In particular it closes
preserved-support and first-damaged-support branches without residual
recursion, providing reusable history-overlap lemmas for the coefficient-one
programme.

## Current proof frontier

For the six-event route to `N + 7`, the remaining tasks are:

1. transport the pointwise-constant BABA cycle leaf to the literal selected
   post-close list and charge the at-most-three earlier closes;
2. close the other overlap-minimal BABA leaves by a forbidden four-vector cover
   or a strictly smaller residue;
3. close the serial/serial branch by well-founded suffix descent while
   preserving the consecutive-event window.

For the sharper `N + 6` route, the most concentrated local target is the
unchanged forward first-support contact.  A successful proof should reuse the
existing facing-forward constant-tail geometry rather than introduce a new
period-length count.

## Verification

The branch-local workflow is:

```text
.github/workflows/upper-bound-unified-check.yml
```

It checks the unconditional endpoint, both coefficient-one reductions, the
trace-retaining cycle modules, the contact-history modules, and the renamed
independent Codex endpoint in one repository tree.
