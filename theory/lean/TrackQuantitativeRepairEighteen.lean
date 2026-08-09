import TrackThetaSharper
import TrackQuantitativeRouteSharp

/-!
# Eighteen-N protected repair

The complete-repair branch now costs one switch-simple repair route (`N`)
plus the sharpened complete reflector-pair lasso (`16*N`), hence `17*N`.
The state-changing forward-merge branch remains bounded by `18*N`, so it is
now the sole bottleneck and the uniform protected-repair cap is `18*N`.
-/

namespace GeneralN

/-- Complete repair followed by the sharpened pair lasso costs at most
`17*N`. -/
theorem ManufacturedReflector.completed_route_with_pair_support_within_seventeen
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
    EventuallyPeriodicWithin w (g, state) (17 * N) := by
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
  have hpair := manufactured_pair_within_sixteen_mul_switches
    hN A B finalState hAfinal hBfinal
  have hend := hpair.forward hrouteFinal'.sound
  have hrouteLe : (A.orientedRoute state).length ≤ N :=
    hrepair.switchSimple_length_le_switches hN
      (A.orientedRoute_simple state)
  exact (hend.prepend hrepair.sound).weaken (by omega)

/-- Damaged support is repaired or absorbed within `18*N`. -/
theorem manufactured_pair_protected_repair_within_eighteen
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    EventuallyPeriodicWithin w (g, B.activatedState) (18 * N) := by
  rcases manufactured_pair_protected_repair_quantitative_outcomes
      hN A B hA hB with hperiodic | hrest
  · exact hperiodic.weaken (by omega)
  · rcases hrest with hfacing | hrest
    · exact (hfacing.within_twelve hN).weaken (by omega)
    · rcases hrest with hchanged | hcomplete
      · exact hchanged.within_eighteen hN
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        exact (A.completed_route_with_pair_support_within_seventeen
          hN B B.baseState B.activatedState finalState hA hrepair
          hAfinal hBfinal).weaken (by omega)

end GeneralN
