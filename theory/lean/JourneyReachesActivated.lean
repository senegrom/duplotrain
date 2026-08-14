import TrackNovelReplay
import FirstReflectorNovelty

/-!
# The manufacturing journey reaches the activated state

The one raw `stepN` fact every downstream counting file needs from the
old Gray-corner module, extracted so the sharp proof does not depend on
the Mellit corridor.
-/

namespace GeneralN

/-- The complete canonical manufacturing journey really ends at the
reflector's activated state.  This packages only raw `stepN` facts and is
useful for identifying the first-turnaround contact vector with the initial
corner of the following reflector pair. -/
theorem ManufacturedReflector.manufacturing_journey_reaches_activated
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState) :
    stepN w (A.exploration.length + A.runway.length + 1)
      (g, A.baseState) = some (e, A.activatedState) := by
  have hback :
      stepN w (A.runway.length + 1) A.preReturn =
        some (e, A.activatedState) := by
    have htrace := physicalTrace_contact_retraces_prefix
      A.runway_trace (A.runway_grooved hpaths)
      A.entryEdge A.return_arrive_mouth
    simpa [reversePassages_length] using htrace.sound
  have hlen :
      A.exploration.length + A.runway.length + 1 =
        A.exploration.length + (A.runway.length + 1) := by
    omega
  rw [hlen, stepN_add, A.exploration_trace.sound]
  exact hback

end GeneralN
