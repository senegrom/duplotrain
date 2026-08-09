import TrackStaySpliceSharp
import TrackThetaTighter
import TrackQuantitativeRouteSharp
import TrackQuantitativeRepairSeventeen

/-!
# Exact `15*N+2` protected-repair cap

The remaining repair outcomes now have these exact costs:

* early/facing repair: `12*N`;
* changed-forward splice: `13*N` (stay: `9*N`, flip: `13*N`);
* complete repair: one switch-simple route (`N`) followed by the repaired
  reflector pair (`14*N+2`).

Thus the uniform local cap is `15*N+2`.
-/

namespace GeneralN

/-- Every changed-forward merge closes within `13*N`. -/
theorem ManufacturedReflector.ChangedForwardMerge.within_thirteen_sharp
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.ChangedForwardMerge B) :
    EventuallyPeriodicWithin w (g, B.activatedState) (13 * N) := by
  cases B with
  | stay R => exact (hmerge.stay_within_nine hN).weaken (by omega)
  | flip R => exact hmerge.flip_within_thirteen hN

/-- Complete repair followed by the tighter reflector-pair lasso costs at
most `15*N+2`. -/
theorem ManufacturedReflector.completed_route_with_pair_support_within_fifteen_succ_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (base state finalState : Tongues)
    (hbasePaths : PathGrooves A.toSupported.paths base)
    (hrepair : PhysicalTrace w (g, state)
      (A.orientedRoute state)
      (A.orientedFinish state, finalState))
    (hAfinal : PathGrooves A.toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState) :
    EventuallyPeriodicWithin w (g, state) (15 * N + 2) := by
  obtain ⟨reference, _hreferencePaths, hroute, hfinish,
      hreferenceGrooved, _hguard⟩ :=
    A.current_route_reference base state hbasePaths
  have hfinalGrooved :
      PassagesGrooved finalState (A.orientedRoute state) :=
    hrepair.grooved_of_switchSimple (A.orientedRoute_simple state)
  have hfinalReferenceGrooved :
      PassagesGrooved finalState (A.orientedRoute reference) := by
    rw [hroute]
    exact hfinalGrooved
  have hreferenceGrooved' :
      PassagesGrooved reference (A.orientedRoute reference) := by
    rw [hroute]
    exact hreferenceGrooved
  have horiented := A.oriented_data_eq_of_route_grooved
    reference finalState hreferenceGrooved' hfinalReferenceGrooved
  have hrouteFinal := A.orientedRoute_trace finalState hAfinal
  have hrouteFinal' : PhysicalTrace w (g, finalState)
      (A.orientedRoute state)
      (A.orientedFinish state, finalState) := by
    rw [horiented.1, horiented.2, hroute, hfinish] at hrouteFinal
    exact hrouteFinal
  have hpair := manufactured_pair_within_fourteen_succ_two
    hN A B finalState hAfinal hBfinal
  have hend := hpair.forward hrouteFinal'.sound
  have hrouteLe : (A.orientedRoute state).length ≤ N :=
    hrepair.switchSimple_length_le_switches hN
      (A.orientedRoute_simple state)
  exact (hend.prepend hrepair.sound).weaken (by omega)

/-- Damaged support is repaired or absorbed within `15*N+2`. -/
theorem manufactured_pair_protected_repair_within_fifteen_succ_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    EventuallyPeriodicWithin w (g, B.activatedState) (15 * N + 2) := by
  rcases manufactured_pair_protected_repair_quantitative_outcomes
      hN A B hA hB with hperiodic | hrest
  · exact hperiodic.weaken (by omega)
  · rcases hrest with hfacing | hrest
    · exact (hfacing.within_twelve hN).weaken (by omega)
    · rcases hrest with hchanged | hcomplete
      · exact (hchanged.within_thirteen_sharp hN).weaken (by omega)
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        exact A.completed_route_with_pair_support_within_fifteen_succ_two
          hN B B.baseState B.activatedState finalState hA hrepair
          hAfinal hBfinal

end GeneralN
