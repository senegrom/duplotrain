import StateLaw

/-!
# Axiom audit for the state law

`#print axioms` on the single theorem.  The expected output is at most
the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) — in particular **no** `sorryAx` and no
`Lean.ofReduceBool` (kernel `decide` only, never `native_decide`).
-/

namespace GeneralN

#print axioms state_law

end GeneralN
