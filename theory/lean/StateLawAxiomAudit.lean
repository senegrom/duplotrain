import KnownEdgeNAddFiveAlt

/-!
# Axiom audit for the coefficient-one state law

`#print axioms` on the canonical theorem.  The expected output is at most
the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) — in particular **no** `sorryAx`.
-/

namespace GeneralN

#print axioms stateLaw

#print axioms stateLaw_N_add_six_alt

#print axioms known_edge_all_run_distinct_le_N_add_five

end GeneralN
