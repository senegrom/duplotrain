import StateLawNAddFourSharp
import StateLawLowerBound
import StateLawSmallN

/-!
# Axiom audit for the sharp state law

`#print axioms` on the headline theorems: the sharp `N + 4` upper bound,
its known-incoming-edge core, the historical `StateLaw` target it
subsumes, the matching `N + 4` lower bound, and the `2^N` leg — the
finite-state ceiling with its `N = 1, 2` witnesses.  The expected output
is at most the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) — in particular **no** `sorryAx` and no `Lean.ofReduceBool`
(kernel `decide` only, never `native_decide`).
-/

namespace GeneralN

#print axioms state_law_N_add_four

#print axioms knownIncomingEdgeNAddFour

#print axioms stateLaw

#print axioms state_law_lower_bound

#print axioms state_law_two_pow

#print axioms state_law_lower_bound_one

#print axioms state_law_lower_bound_two

end GeneralN
