import BoundaryCanonicalGeometry
import TrackThetaAllTime

/-!
# Coordinate charge in the canonical productive-boundary residual

This file isolates the remaining canonical branch.  At the unchanged
canonical occurrence, the initial boundary switch is the omitted action
switch of the first flip reflector.  Full coordinate charge therefore puts
that switch among the second reflector's productive first writers and the
present-writer boundary theorem closes the branch.

Saturation alone, however, leaves one exact arithmetic corner: if the action
is absent from the second first writers, the generic two-novelty protected
repair and the reserved-action charge bound meet at
`reusable + secondWriters + 1 = N`.  The final theorem records this tight
residual without claiming the unavailable full-charge equality.
-/

namespace GeneralN

/-- A grooved flip reflector with equal source and target ports has only its
two action phases at every future raw time.  It is the same reflector paired
with itself in the general all-time flip-pair theorem. -/
theorem ManufacturedFlipReflector.same_endpoint_all_time_two_phase
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e)
    (hge : g = e)
    (state : Tongues)
    (hpaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths state)
    (d : Nat) :
    ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
      (phase = state ∨ phase = flipAt state R.actionSwitch) := by
  subst e
  obtain ⟨port, phase, hrun, hphase⟩ :=
    manufactured_flip_pair_all_time_four_phase
      R R state hpaths hpaths d
  refine ⟨port, phase, hrun, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hphase
  rcases hphase with hstate | hfirst | hsecond | hboth
  · exact Or.inl hstate
  · exact Or.inr hfirst
  · exact Or.inr hsecond
  · exact Or.inl (by simpa [flipAt_flipAt] using hboth)

/-- **Canonical saturation is impossible.**  The unchanged canonical
occurrence removes one first-journey vector and inserts `original`.  Its
runway is empty, so after that journey the same-port flip reflector traps the
entire future in its two action phases.  The activated phase is already in
the reduced first history; adjoining only the opposite phase gives a global
history of length at most `N+3`, contradicting saturated `N+4` avoidance.

This is the amortized tail charge: no separate second-reflector or repair
budget is needed once the canonical source self-reflector is exposed. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_canonical_unchanged
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hstay : O.next = O.middle)
    (hcanonical : O.before.length = R.runway.length) :
    False := by
  let A : ManufacturedReflector w S.source.g S.source.e :=
    ManufacturedReflector.flip R
  let firstTravel := A.exploration.length + A.runway.length + 1
  let opposite := VectorCount.restrict N
    (flipAt A.activatedState R.actionSwitch)
  let history := O.reducedBoundaryHistory N S.source.original ++ [opposite]
  have hge : S.source.g = S.source.e :=
    (S.canonical_source_self_link R O hcanonical).1
  have hApathsS : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [← S.activated]
    exact S.grooves
  have hApaths : PathGrooves A.toSupported.paths A.activatedState := by
    simpa [A, hAeq] using hApathsS
  have hAbase : A.baseState = S.source.base := by
    simpa [A, hAeq] using S.reflector_base
  have hreach : stepN w firstTravel (S.source.g, S.source.base) =
      some (S.source.e, A.activatedState) := by
    simpa [firstTravel, A, hAeq, S.activated] using S.reached
  have hreachSelf : stepN w firstTravel (S.source.g, S.source.base) =
      some (S.source.g, A.activatedState) := by
    simpa [hge] using hreach
  have hlengthReduced :=
    O.reducedBoundaryHistory_length hN S.source.original
  have hlength : history.length ≤ N + 4 := by
    dsimp [history]
    simp only [List.length_append, List.length_singleton]
    omega
  have horiginal : VectorCount.restrict N S.source.original ∈ history := by
    apply List.mem_append_left
    exact List.mem_cons_self
  have hactivated : VectorCount.restrict N A.activatedState ∈
      O.reducedBoundaryHistory N S.source.original := by
    apply O.sharp_mem_reduced_of_stay S.source.original hstay
    unfold ManufacturedReflector.sharpConstructionHistory
    apply List.mem_append_right
    exact List.mem_singleton.mpr rfl
  have hglobal : ∀ d,
      (stepN w d (S.source.g, S.source.base)).isSome →
      restrictedTonguesAt w N (S.source.g, S.source.base) d ∈ history := by
    intro d hdLive
    by_cases hprefix : d ≤ firstTravel
    · apply List.mem_append_left
      have hm := A.manufacturing_journey_mem_sharpHistory
        (N := N) hApaths (j := d)
          (by simpa [firstTravel] using hprefix)
      have hmR : restrictedTonguesAt w N
          (S.source.g, A.baseState) d ∈
          (ManufacturedReflector.flip R).sharpConstructionHistory N := by
        simpa [A] using hm
      have hmSource : restrictedTonguesAt w N
          (S.source.g, S.source.base) d ∈
          (ManufacturedReflector.flip R).sharpConstructionHistory N := by
        rw [← hAbase]
        exact hmR
      exact O.sharp_mem_reduced_of_stay
        S.source.original hstay _ hmSource
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hpathsR : PathGrooves
          (ManufacturedReflector.flip R).toSupported.paths
            (ManufacturedReflector.flip R).activatedState := by
        simpa [A] using hApaths
      obtain ⟨port, phase, hrun, hphase⟩ :=
        R.same_endpoint_all_time_two_phase hge
          (ManufacturedReflector.flip R).activatedState hpathsR q
      have hrunGlobal :
          stepN w d (S.source.g, S.source.base) = some (port, phase) := by
        rw [hdEq, stepN_add, hreachSelf]
        simpa [A] using hrun
      have hvector :
          restrictedTonguesAt w N (S.source.g, S.source.base) d =
            VectorCount.restrict N phase := by
        simp [restrictedTonguesAt, tonguesAt, hrunGlobal]
      rw [hvector]
      rcases hphase with hphase | hphase
      · apply List.mem_append_left
        simpa [A, hphase] using hactivated
      · apply List.mem_append_right
        simp [opposite, A, hphase]
  exact S.source.false_of_global_history history hlength horiginal hglobal

end GeneralN
