import TrackQuantitativeTight

/-!
# A switch-simple physical route has length at most N

The complete-repair branch previously bounded the selected oriented route by
the reflector's total two-route travel, `2*N`.  The selected route itself is
switch-simple, and every one of its passages belongs to a switch below `N`.
Thus its length is at most `N`.  Replacing the coarse route estimate tightens
the complete-repair lasso from `22*N` to `21*N`.
-/

namespace GeneralN

/-- Every switch appearing in a physical trace is below the wiring's switch
ceiling. -/
theorem PhysicalTrace.passage_switches_lt
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N) :
    ∀ {start finish : Nat × Tongues} {passages : List Passage},
      PhysicalTrace w start passages finish →
      ∀ s ∈ passages.map passageSwitch, s < N := by
  intro start finish passages htrace
  induction htrace with
  | nil =>
      intro s hs
      cases hs
  | @cons p x q u v rest finish harrive hlink tail ih =>
      intro s hs
      simp only [List.map_cons, List.mem_cons] at hs
      rcases hs with rfl | hs
      · have hx : x < 3 * N := (hN x q hlink).1
        have hswitch := arrive_exit_switch u p
        rw [harrive] at hswitch
        dsimp [passageSwitch]
        omega
      · exact ih s hs

/-- A switch-simple trace in an `N`-switch wiring contains at most `N`
passages. -/
theorem PhysicalTrace.switchSimple_length_le_switches
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    passages.length ≤ N := by
  unfold SwitchSimple at hsimple
  have hlt := htrace.passage_switches_lt hN
  simpa only [List.length_map] using
    nodup_nat_lt_length hsimple hlt

/-- Quantitative complete repair with the selected-route bound `N` rather
than the total-reflector-travel bound `2*N`. -/
theorem ManufacturedReflector.completed_route_with_pair_support_within_twenty_one
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
    EventuallyPeriodicWithin w (g, state) (21 * N) := by
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
  have hpair := manufactured_pair_within_twenty_mul_switches
    hN A B finalState hAfinal hBfinal
  have hend := hpair.forward hrouteFinal'.sound
  have hrouteLe : (A.orientedRoute state).length ≤ N :=
    hrepair.switchSimple_length_le_switches hN
      (A.orientedRoute_simple state)
  exact (hend.prepend hrepair.sound).weaken (by omega)

end GeneralN
