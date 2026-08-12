import StateLawNAddFive
import StateLawLowerBound

/-!
# Axiom audit for the state law

`#print axioms` on the headline theorems — the `N + 5` upper bound, its
known-incoming-edge `N + 4` core, the historical `StateLaw` target, and
the `N + 4` lower bound.  The expected output is at most the three
standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) — in
particular **no** `sorryAx`.
-/

namespace GeneralN

#print axioms state_law_N_add_five

#print axioms knownIncomingEdgeNAddFour

#print axioms stateLaw_via_N_add_five

#print axioms state_law_lower_bound

end GeneralN
