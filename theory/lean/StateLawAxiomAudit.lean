import StateLawNAddFourSharp
import StateLawLowerBound

/-!
# Axiom audit for the sharp state law

`#print axioms` on the headline theorems: the sharp `N + 4` upper bound,
its known-incoming-edge core, the historical `StateLaw` target it
subsumes, and the matching `N + 4` lower bound.  The expected output is
at most the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) — in particular **no** `sorryAx`.
-/

namespace GeneralN

#print axioms state_law_N_add_four

#print axioms knownIncomingEdgeNAddFour

#print axioms stateLaw

#print axioms state_law_lower_bound

end GeneralN
