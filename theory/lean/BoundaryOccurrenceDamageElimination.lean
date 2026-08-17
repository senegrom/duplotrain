import BoundaryApproachActionElimination
import BoundaryCanonicalGeometry

/-!
# Elimination of the occurrence-support-damage residuals

A noncanonical unchanged occurrence supplies a second repeated vector in the
first manufacturing journey.  Replacing the ordinary sharp history core by
the existing double-reduced boundary history therefore inserts the arbitrary
pre-passage vector at no extra cost.  The changed-contact lead has exactly the
same length as the ordinary compressed lead, while retaining that boundary
vector.  The existing zero/two/one-novelty contact classification then counts
time zero inside the `N+4` budget.
-/

namespace GeneralN

/-- Pairing a grooved flip reflector with itself at equal endpoints collapses
the general four-phase law to its two action phases. -/
theorem ManufacturedFlipReflector.same_endpoint_two_phase
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e)
    (hge : g = e)
    (state : Tongues)
    (hpaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths state)
    (d : Nat) :
    exists port phase,
      stepN w d (g, state) = some (port, phase) /\
        (phase = state \/ phase = flipAt state R.actionSwitch) := by
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

/-- **The canonical unchanged saturation is impossible.**

Canonicality forces an empty runway and a self-linked source.  The complete
future after the first manufacture then has only the activated phase and its
action mate.  Both manufacturing phases, `original`, and that one mate fit in
a global history of size at most `N + 3`, contradicting saturation and global
avoidance of `original`. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_canonical_saturation
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
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
  let history :=
    O.reducedBoundaryHistory N S.source.original ++ [opposite]

  have hgeometry := S.canonical_source_self_link R O hcanonical
  have hge : S.source.g = S.source.e := hgeometry.1
  have hApathsS : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [← S.activated]
    exact S.grooves
  have hApaths : PathGrooves A.toSupported.paths A.activatedState := by
    simpa [A, hAeq] using hApathsS
  have hAbase : A.baseState = S.source.base := by
    simpa [A, hAeq] using S.reflector_base
  have hreach : stepN w firstTravel
      (S.source.g, S.source.base) =
        some (S.source.e, A.activatedState) := by
    simpa [firstTravel, A, hAeq, S.activated] using S.reached
  have hreachSelf : stepN w firstTravel
      (S.source.g, S.source.base) =
        some (S.source.g, A.activatedState) := by
    simpa [hge] using hreach

  have hlengthReduced :=
    O.reducedBoundaryHistory_length hN S.source.original
  have hlength : history.length <= N + 3 := by
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
    exact List.mem_cons_self

  have hglobal : forall d,
      (stepN w d (S.source.g, S.source.base)).isSome ->
      restrictedTonguesAt w N (S.source.g, S.source.base) d ∈
        history := by
    intro d _hdLive
    by_cases hprefix : d <= firstTravel
    · apply List.mem_append_left
      apply O.sharp_mem_reduced_of_stay S.source.original hstay
      have hm := A.manufacturing_journey_mem_sharpHistory
        (N := N) hApaths (j := d)
          (by simpa [firstTravel] using hprefix)
      have hmR :
          restrictedTonguesAt w N (S.source.g, S.source.base) d ∈
            (ManufacturedReflector.flip R).sharpConstructionHistory N := by
        simpa only [A, hAbase] using hm
      exact hmR
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hpathsR : PathGrooves
          (ManufacturedReflector.flip R).toSupported.paths
            (ManufacturedReflector.flip R).activatedState := by
        simpa [A] using hApaths
      obtain ⟨port, phase, hrun, hphase⟩ :=
        R.same_endpoint_two_phase hge
          (ManufacturedReflector.flip R).activatedState hpathsR q
      have hrunGlobal :
          stepN w d (S.source.g, S.source.base) =
            some (port, phase) := by
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

  exact S.source.false_of_global_history
    history (by omega) horiginal hglobal

/-- Replace the first reflector's ordinary one-duplicate core in a changed
contact lead by the two-duplicate boundary history. -/
noncomputable def InitialEntryWriterOccurrence.doubleReducedContactLead
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (original : Tongues) : List (List Bool) :=
  O.doubleReducedBoundaryHistory N original ++
    ((rawFirstWriterHistory w N
      (e, (ManufacturedReflector.flip R).activatedState)
      C.approach.length).erase
        (VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState) ++
      [VectorCount.restrict N C.nextState])

/-- The replacement lead contains the arbitrary boundary vector. -/
theorem InitialEntryWriterOccurrence.original_mem_doubleReducedContactLead
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (original : Tongues) :
    VectorCount.restrict N original ∈
      O.doubleReducedContactLead (N := N) C original := by
  unfold InitialEntryWriterOccurrence.doubleReducedContactLead
  apply List.mem_append_left
  exact List.mem_cons_self

/-- A noncanonical occurrence replacement has exactly the same size as the
ordinary compressed changed-contact lead. -/
theorem InitialEntryWriterOccurrence.doubleReducedContactLead_length_eq
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (original : Tongues)
    (hdifferent : O.before.length ≠ R.runway.length) :
    (O.doubleReducedContactLead (N := N) C original).length =
      (C.compressedLead N).length := by
  unfold InitialEntryWriterOccurrence.doubleReducedContactLead
  unfold PartialSecondRunSharp.ChangedContact.compressedLead
  simp only [List.length_append]
  rw [O.doubleReducedBoundaryHistory_length original hdifferent,
    (ManufacturedReflector.flip R).sharpHistoryCore_length]

/-- Every ordinary compressed-lead vector is retained by the occurrence
replacement. -/
theorem InitialEntryWriterOccurrence.mem_doubleReducedContactLead_of_mem_compressedLead
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (original : Tongues)
    (hstay : O.next = O.middle)
    {x : List Bool}
    (hx : x ∈ C.compressedLead N) :
    x ∈ O.doubleReducedContactLead (N := N) C original := by
  unfold PartialSecondRunSharp.ChangedContact.compressedLead at hx
  unfold InitialEntryWriterOccurrence.doubleReducedContactLead
  rcases List.mem_append.mp hx with hxFirst | hxTail
  · apply List.mem_append_left
    apply O.sharp_mem_doubleReducedBoundaryHistory original
      hstay
    exact List.mem_of_mem_erase hxFirst
  · exact List.mem_append_right _ hxTail

/-- A local novelty cover over the ordinary compressed lead lifts across the
first manufacturing journey to the boundary-replacement lead. -/
theorem InitialEntryWriterOccurrence.doubleReducedContactLead_global_cover
    {w : Wiring} {N g e k0 budget : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (original : Tongues)
    (hstay : O.next = O.middle)
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hlocal : NoveltyCoverOn w N
      (e, (ManufacturedReflector.flip R).activatedState)
      (times.map (fun k => k -
        ((ManufacturedReflector.flip R).exploration.length +
          (ManufacturedReflector.flip R).runway.length + 1)))
      (C.compressedLead N) budget) :
    NoveltyCoverOn w N
      (g, (ManufacturedReflector.flip R).baseState) times
      (O.doubleReducedContactLead (N := N) C original) budget := by
  let A : ManufacturedReflector w g e := ManufacturedReflector.flip R
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localTimes := times.map (fun k => k - firstTravel)
  have hreach : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel, A] using
      A.manufacturing_journey_reaches_activated hA
  have hlocal' : NoveltyCoverOn w N (e, A.activatedState)
      localTimes (C.compressedLead N) budget := by
    simpa [localTimes, firstTravel, A] using hlocal
  obtain ⟨fresh, hfresh, hlocalMem⟩ := hlocal'
  refine ⟨fresh, hfresh, ?_⟩
  intro k hk
  by_cases hfirst : k ≤ firstTravel
  · apply List.mem_append_left
    unfold InitialEntryWriterOccurrence.doubleReducedContactLead
    apply List.mem_append_left
    apply O.sharp_mem_doubleReducedBoundaryHistory original
      hstay
    exact A.manufacturing_journey_mem_sharpHistory hA (by
      simpa [firstTravel] using hfirst)
  · let d := k - firstTravel
    have hdMem : d ∈ localTimes := by
      dsimp [d, localTimes]
      exact List.mem_map.mpr ⟨k, hk, rfl⟩
    have hm := hlocalMem d hdMem
    have hshift := restrictedTonguesAt_sub_of_reach
      (N := N) hreach (by omega) (hlive k hk)
    rw [hshift]
    rcases List.mem_append.mp hm with hmHistory | hmFresh
    · apply List.mem_append_left
      exact O.mem_doubleReducedContactLead_of_mem_compressedLead
        (N := N) C original hstay hmHistory
    · exact List.mem_append_right _ hmFresh

/-- Count the arbitrary boundary vector together with a changed-contact run
using the occurrence replacement lead. -/
theorem InitialEntryWriterOccurrence.doubleReducedContactLead_count
    {w : Wiring} {N g e k0 budget : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (original : Tongues)
    (hstay : O.next = O.middle)
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).baseState))).Nodup)
    (hlocal : NoveltyCoverOn w N
      (e, (ManufacturedReflector.flip R).activatedState)
      (times.map (fun k => k -
        ((ManufacturedReflector.flip R).exploration.length +
          (ManufacturedReflector.flip R).runway.length + 1)))
      (C.compressedLead N) budget) :
    times.length + 1 ≤
      (O.doubleReducedContactLead (N := N) C original).length + budget := by
  have hcover := O.doubleReducedContactLead_global_cover
    (N := N) C original hstay hA times hlive hlocal
  exact noveltyCoverOn_distinct_count_with_extra hcover
    (O.original_mem_doubleReducedContactLead (N := N) C original) hnd


/-- A saturated productive boundary cannot contain a changed contact after a
noncanonical unchanged occurrence of its first flip reflector. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_noncanonical_occurrence_flip_changed_contact
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hstay : O.next = O.middle)
    (hdifferent : O.before.length ≠ R.runway.length)
    (D : PartialSecondRunSharp.ChangedContact w
      (ManufacturedReflector.flip R)) : False := by
  let C := D
  have hApathsS : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [← S.activated]
    exact S.grooves
  have hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState := by
    simpa [hAeq] using hApathsS
  have hAbase : (ManufacturedReflector.flip R).baseState =
      S.source.base := by
    simpa [hAeq] using S.reflector_base
  have hlive : forall k, k ∈ S.source.times ->
      (stepN w k
        (S.source.g,
          (ManufacturedReflector.flip R).baseState)).isSome := by
    intro k hk
    simpa [hAbase] using S.source.live k hk
  have hnd : (VectorCount.restrict N S.source.original ::
      S.source.times.map (restrictedTonguesAt w N
        (S.source.g,
          (ManufacturedReflector.flip R).baseState))).Nodup := by
    simpa [hAbase] using S.source.distinct
  let localTimes := S.source.times.map (fun k => k -
    ((ManufacturedReflector.flip R).exploration.length +
      (ManufacturedReflector.flip R).runway.length + 1))
  have hsaturated := S.source.saturated
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · have hlocal := C.backward_all_time_zero_novelty
      (N := N) hbackward localTimes
    have hcount := O.doubleReducedContactLead_count
      (N := N) C S.source.original hstay hA
        S.source.times hlive hnd (by
          simpa [localTimes] using hlocal)
    have hlengthEq := O.doubleReducedContactLead_length_eq
      (N := N) C S.source.original hdifferent
    have hlength := C.compressedLead_length_le hN hA
    omega
  · by_cases haction :
        R.actionSwitch ∈ C.approachFirstWriterSwitches N
    · rcases C.forward_flip_one_novelty_or_runway_residual
          hforward hrepair hrestored haction localTimes with
        hone | hresidual
      · have hcount := O.doubleReducedContactLead_count
          (N := N) C S.source.original hstay hA
            S.source.times hlive hnd (by
              simpa [localTimes] using hone)
        have hlengthEq := O.doubleReducedContactLead_length_eq
          (N := N) C S.source.original hdifferent
        have hlength := C.compressedLead_length_le hN hA
        omega
      · exact (Classical.choice hresidual).impossible hN hA
    · have hlocal := C.changed_two_novelty (N := N) localTimes
      have hcount := O.doubleReducedContactLead_count
        (N := N) C S.source.original hstay hA
          S.source.times hlive hnd (by
            simpa [localTimes] using hlocal)
      have hlengthEq := O.doubleReducedContactLead_length_eq
        (N := N) C S.source.original hdifferent
      have hlength :=
        C.compressedLead_length_le_N_add_two_of_action_absent
          hN hA haction
      omega


/-- Every changed contact after an unchanged initial-switch occurrence is
incompatible with a saturated productive boundary.  Stay reflectors already
have the `N+3` saving; for flip reflectors, the canonical occurrence is the
existing saturation obstruction and every noncanonical occurrence is covered
by the double-reduced lead above. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_occurrence_changed_contact
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0 S.A)
    (hstay : O.next = O.middle)
    (D : PartialSecondRunSharp.ChangedContact w S.A) : False := by
  generalize hAeq : S.A = A at O hstay D
  cases A with
  | stay R =>
      have hApathsS : PathGrooves S.A.toSupported.paths
          S.A.activatedState := by
        rw [← S.activated]
        exact S.grooves
      have hA : PathGrooves
          (ManufacturedReflector.stay R).toSupported.paths
          (ManufacturedReflector.stay R).activatedState := by
        simpa [hAeq] using hApathsS
      have hAbase : (ManufacturedReflector.stay R).baseState =
          S.source.base := by
        simpa [hAeq] using S.reflector_base
      have hlive : forall k, k ∈ S.source.times ->
          (stepN w k
            (S.source.g,
              (ManufacturedReflector.stay R).baseState)).isSome := by
        intro k hk
        simpa [hAbase] using S.source.live k hk
      have hnd : (S.source.times.map
          (restrictedTonguesAt w N
            (S.source.g,
              (ManufacturedReflector.stay R).baseState))).Nodup := by
        have htail := (List.nodup_cons.mp S.source.distinct).2
        simpa [hAbase] using htail
      have hbound := D.stay_saving_all_run_distinct_le_N_add_three
        hN hA S.source.times hlive hnd
      have hsaturated := S.source.saturated
      omega
  | flip R =>
      by_cases hcanonical : O.before.length = R.runway.length
      · exact S.false_of_canonical_saturation
          hN R hAeq O hstay hcanonical
      · exact S.false_of_noncanonical_occurrence_flip_changed_contact
          hN R hAeq O hstay hcanonical D


end GeneralN
