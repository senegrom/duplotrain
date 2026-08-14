import PartialSecondRunSharp

/-!
# Structural dichotomy for an unfinished second journey

This file separates the dynamic statement "the second probe does not
manufacture an opposite reflector" from the coefficient-one accounting
problem.  The dynamic conclusion is exact: the `N+1` probe either dies, or
reaches a stable switch-simple cycle.  The latter has one settled restricted
tongue vector at every absolute time after its transient lap.

The statements are over raw `Wiring`, `PhysicalTrace`, and `stepN`; there is
no finite-`N` evaluation and no hidden completion selector.
-/

namespace GeneralN

/-- The literal reflector payload returned by the second `N+1` probe. -/
structure PartialSecondReflectorCompletion
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (N : Nat) : Type where
  reflector : ManufacturedReflector w e g
  state : Tongues
  length_le :
    reflector.exploration.length + reflector.runway.length + 1 <=
      2 * N + 1
  paths : PathGrooves reflector.toSupported.paths state
  base : reflector.baseState = A.activatedState
  activated : state = reflector.activatedState
  reaches :
    stepN w
      (reflector.exploration.length + reflector.runway.length + 1)
      (e, A.activatedState) = some (g, state)
  preserves : forall j,
    j ∉ reflector.exploration.map passageSwitch ->
      state j = A.activatedState j

end GeneralN
