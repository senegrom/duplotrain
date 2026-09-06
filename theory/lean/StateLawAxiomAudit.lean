import StateLaw

/-!
# Axiom audit for the state law

Check the exact transitive axiom list, not merely the absence of `sorryAx`.
The guard fails compilation if an unexpected axiom appears. A separate
print retains the diagnostic consumed by the CI log check.
-/

namespace GeneralN

/-- info: 'GeneralN.state_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms state_law

#print axioms state_law

end GeneralN
