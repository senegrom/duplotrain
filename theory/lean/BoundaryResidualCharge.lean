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

/-- Exact size of the ordinary coefficient-one history core for a first
flip reflector. -/
theorem ManufacturedFlipReflector.preservedTwoHistoryCore_length_eq_charge_add_three
    {w : Wiring} {N g e : Nat}
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState) :
    ((ManufacturedReflector.flip R).preservedTwoHistoryCore B N).length =
      (ManufacturedReflector.flip R).reusableSwitches.length +
        (rawFirstWriterTimes w N (e, B.baseState)
          B.exploration.length).length + 3 := by
  have hboundary :
      VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState ∈
        B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hexploration :
      (ManufacturedReflector.flip R).exploration.length =
        (ManufacturedReflector.flip R).reusableSwitches.length + 1 := by
    simp [ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches]
    omega
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    (ManufacturedReflector.flip R).sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

/-- In the canonical branch, full coordinate charge makes the initial
boundary switch a productive first writer of the second construction. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_initial_mem_second_writers_of_full_charge
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length)
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (hfull :
      (ManufacturedReflector.flip R).reusableSwitches.length +
        (rawFirstWriterTimes w N (S.source.e, B.baseState)
          B.exploration.length).length = N) :
    S.source.k0 ∈ B.constructionFirstWriterSwitches N := by
  have hk0 : S.source.k0 = R.actionSwitch :=
    O.switch_eq_action_of_before_length_eq_runway hcanonical
  have haction := R.action_mem_second_writers_of_full_charge
    hN B hbaseGrooves hpreGrooves hfull
  simpa [hk0] using haction

/-- Full charge closes the canonical saturated protected-pair branch by the
present-writer productive-boundary theorem. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_canonical_full_charge_protected_pair
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length)
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (lead : List Passage)
    (hlead : PhysicalTrace w (S.source.g, B.baseState) lead
      (S.source.e, B.baseState))
    (hleadSimple : SwitchSimple lead)
    (hfull :
      (ManufacturedReflector.flip R).reusableSwitches.length +
        (rawFirstWriterTimes w N (S.source.e, B.baseState)
          B.exploration.length).length = N) :
    False := by
  have hApathsS : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [← S.activated]
    exact S.grooves
  have hApaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState := by
    simpa [hAeq] using hApathsS
  have hAbase : (ManufacturedReflector.flip R).baseState =
      S.source.base := by
    simpa [hAeq] using S.reflector_base
  have hAatBase : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have hpresent :=
    S.canonical_initial_mem_second_writers_of_full_charge
      hN R O hcanonical B hAatBase hpre hfull
  have hbound := productive_initial_boundary_N_add_four_of_present_writer
    hN S.source.entry S.source.stem S.source.switch_lt
      S.source.original S.source.base S.source.base_flip
      (ManufacturedReflector.flip R) hAbase B hbase
      hApaths hBpaths hpre hpresent lead hlead hleadSimple
      S.source.times S.source.live S.source.distinct
  rw [S.source.saturated] at hbound
  omega

/-- Exact surviving canonical obstruction.  Once the present-action-writer
branch is closed, saturation forces the action to be absent from the second
first writers and forces the one-reserved coordinate charge to be tight.

In particular, the hypotheses currently imply `charge = N - 1`, not the
full-charge equality required by
`action_mem_second_writers_of_full_charge`. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_saturated_protected_pair_tight_spare
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length)
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (lead : List Passage)
    (hlead : PhysicalTrace w (S.source.g, B.baseState) lead
      (S.source.e, B.baseState))
    (hleadSimple : SwitchSimple lead) :
    R.actionSwitch ∉ B.constructionFirstWriterSwitches N ∧
      (ManufacturedReflector.flip R).reusableSwitches.length +
          (rawFirstWriterTimes w N (S.source.e, B.baseState)
            B.exploration.length).length + 1 = N := by
  have hk0 : S.source.k0 = R.actionSwitch :=
    O.switch_eq_action_of_before_length_eq_runway hcanonical
  have hApathsS : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [← S.activated]
    exact S.grooves
  have hApaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState := by
    simpa [hAeq] using hApathsS
  have hAbase : (ManufacturedReflector.flip R).baseState =
      S.source.base := by
    simpa [hAeq] using S.reflector_base
  have hAatBase : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have hhistory : ∀ x,
      x ∈ (ManufacturedReflector.flip R).sharpConstructionHistory N ∨
        x ∈ B.sharpConstructionHistory N →
      x ∈ (ManufacturedReflector.flip R).preservedTwoHistoryCore B N := by
    intro x hx
    exact (ManufacturedReflector.flip R).mem_preservedTwoHistoryCore B hx
  have htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes,
        (stepN w k (S.source.g, B.activatedState)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N
          (S.source.g, B.activatedState))).Nodup →
      NoveltyCoverOn w N (S.source.g, B.activatedState)
        tailTimes
        ((ManufacturedReflector.flip R).preservedTwoHistoryCore B N) 2 := by
    intro tailTimes htailLive htailNodup
    exact ManufacturedReflector.protected_repair_two_novelty_over_history
        hN (ManufacturedReflector.flip R) B hAatBase hBpaths hpre
          ((ManufacturedReflector.flip R).preservedTwoHistoryCore B N)
          hhistory tailTimes htailLive htailNodup
  have hlive : ∀ k ∈ S.source.times,
      (stepN w k
        (S.source.g, (ManufacturedReflector.flip R).baseState)).isSome := by
    intro k hk
    simpa [hAbase] using S.source.live k hk
  have hnd : (S.source.times.map
      (restrictedTonguesAt w N
        (S.source.g, (ManufacturedReflector.flip R).baseState))).Nodup := by
    have htailNodup := (List.nodup_cons.mp S.source.distinct).2
    simpa [hAbase] using htailNodup
  have hcount :=
    ManufacturedReflector.two_journeys_then_shared_history_novelty_count
        (ManufacturedReflector.flip R) B hbase hApaths hBpaths
          ((ManufacturedReflector.flip R).preservedTwoHistoryCore B N)
          hhistory 2 htail S.source.times hlive hnd
  have hcoreLength :=
    R.preservedTwoHistoryCore_length_eq_charge_add_three
      (N := N) B hbase
  by_cases haction :
      R.actionSwitch ∈ B.constructionFirstWriterSwitches N
  · have hpresent :
        S.source.k0 ∈ B.constructionFirstWriterSwitches N := by
      simpa [hk0] using haction
    have hbound := productive_initial_boundary_N_add_four_of_present_writer
      hN S.source.entry S.source.stem S.source.switch_lt
        S.source.original S.source.base S.source.base_flip
        (ManufacturedReflector.flip R) hAbase B hbase
        hApaths hBpaths hpre hpresent lead hlead hleadSimple
        S.source.times S.source.live S.source.distinct
    rw [S.source.saturated] at hbound
    omega
  · refine ⟨haction, ?_⟩
    have hreserved :=
      ManufacturedReflector.reusable_add_second_first_writers_add_reserved_le
        hN (ManufacturedReflector.flip R) B hAatBase hpre
          (R.action_lt hN) R.action_not_mem_reusable haction
    have hsaturated := S.source.saturated
    omega

end GeneralN
