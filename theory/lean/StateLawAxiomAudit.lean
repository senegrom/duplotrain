import KnownEdgeNAddFiveAlt
import StateLawLowerBound

/-!
# Axiom audit for the coefficient-one state law

`#print axioms` on the canonical theorems — the `N + 6` upper bound and
the `N + 4` lower bound.  The expected output is at most the three
standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) — in
particular **no** `sorryAx`.
-/

namespace GeneralN

#print axioms stateLaw

#print axioms stateLaw_N_add_six_alt

#print axioms known_edge_all_run_distinct_le_N_add_five

#print axioms state_law_lower_bound

end GeneralN
