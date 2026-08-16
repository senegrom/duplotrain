import BoundaryChangedContactSaving

/-!
# Eliminating the action-only approach-written residual

When the changed-contact approach first-writes the old flip action, the local
forward tail has only one fresh corner (the runway alternative is impossible).
Consequently the exploration-absent boundary coordinate alone supplies the
missing ambient reserve: the compressed lead is at most `N+2`, and the whole
changed-contact run is at most `N+3`.  Thus the only approach-written residual
left by the productive-boundary saving is a first write of the boundary switch
itself.
-/

namespace GeneralN

/-- If the reserved boundary switch is absent both from the old reusable
support and from productive first writers in the strict approach, it supplies
one ambient coordinate independently of whether the old action is itself an
approach writer. -/
theorem PartialSecondRunSharp.ChangedContact.reusable_add_approach_writers_add_reserved_le
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hk0 : k0 < N)
    (hreservedExploration : Not (k0 ∈
      (ManufacturedReflector.flip R).exploration.map passageSwitch))
    (hreservedApproach : Not (k0 ∈
      C.approachFirstWriterSwitches N)) :
    (ManufacturedReflector.flip R).reusableSwitches.length +
        (rawFirstWriterTimes w N
          (e, (ManufacturedReflector.flip R).activatedState)
          C.approach.length).length + 1 <= N := by
  classical
  let times := rawFirstWriterTimes w N
    (e, (ManufacturedReflector.flip R).activatedState)
    C.approach.length
  let writers := times.map
    (rawWriterAt w
      (e, (ManufacturedReflector.flip R).activatedState))
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact nodup_filter_nat _ List.nodup_range
  have hwritersNodup : writers.Nodup := by
    dsimp [writers]
    apply nodup_map_nat_of_injective_on_two_history
    · intro i hi j hj hEq
      have hiData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hi)
      have hjData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hj)
      exact rawFirstWriterAt_injective hiData.2 hjData.2 hEq
    · exact htimesNodup
  have hdisjoint :
      forall oldSwitch,
        oldSwitch ∈ (ManufacturedReflector.flip R).reusableSwitches ->
      forall freshSwitch, freshSwitch ∈ writers ->
        oldSwitch ≠ freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
    have hkData := mem_rawFirstWriterTimes_iff.mp (by
      simpa [times] using hk)
    have houtside :=
      C.approach_trace.productive_writer_not_old_reusable
        hN (ManufacturedReflector.flip R) C.approach_simple
        hA C.old_grooves hkData.1 hkData.2.1
    apply houtside
    rw [← hEq]
    exact hOld
  let occupied :=
    (ManufacturedReflector.flip R).reusableSwitches ++ writers
  have hoccupiedNodup : occupied.Nodup := by
    dsimp [occupied]
    exact List.nodup_append.mpr
      ⟨(ManufacturedReflector.flip R).reusableSwitches_nodup,
        hwritersNodup, hdisjoint⟩
  have hreservedNotOccupied : Not (k0 ∈ occupied) := by
    intro hm
    rcases List.mem_append.mp hm with hold | hfresh
    · exact R.reserved_not_mem_reusable hreservedExploration hold
    · apply hreservedApproach
      simpa [PartialSecondRunSharp.ChangedContact.approachFirstWriterSwitches,
        writers, times] using hfresh
  have hallNodup : (k0 :: occupied).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hreservedNotOccupied, hoccupiedNodup⟩
  have hallLt : forall switch,
      switch ∈ k0 :: occupied -> switch < N := by
    intro switch hswitch
    rcases List.mem_cons.mp hswitch with rfl | hoccupied
    · exact hk0
    rcases List.mem_append.mp hoccupied with hold | hfresh
    · exact (ManufacturedReflector.flip R).reusableSwitch_lt hN hold
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hfresh
      have hkData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hk)
      exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hallNodup hallLt
  have hlength :
      (k0 :: occupied).length =
        (ManufacturedReflector.flip R).reusableSwitches.length +
          times.length + 1 := by
    simp [occupied, writers]
  rw [hlength] at hbound
  simpa [times] using hbound

/-- Reserving the boundary coordinate alone bounds the changed-contact
compressed lead by `N+2`, even when the old action is approach-written. -/
theorem PartialSecondRunSharp.ChangedContact.compressedLead_length_le_N_add_two_of_reserved_absent
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hk0 : k0 < N)
    (hreservedExploration : Not (k0 ∈
      (ManufacturedReflector.flip R).exploration.map passageSwitch))
    (hreservedApproach : Not (k0 ∈
      C.approachFirstWriterSwitches N)) :
    (C.compressedLead N).length <= N + 2 := by
  have hboundary :
      VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState ∈
        rawFirstWriterHistory w N
          (e, (ManufacturedReflector.flip R).activatedState)
          C.approach.length := by
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN]
  have hcharge :=
    C.reusable_add_approach_writers_add_reserved_le
      hN hA hk0 hreservedExploration hreservedApproach
  unfold PartialSecondRunSharp.ChangedContact.compressedLead
  rw [List.length_append, List.length_append,
    List.length_erase_of_mem hboundary,
    (ManufacturedReflector.flip R).sharpHistoryCore_length]
  simp [rawFirstWriterHistory, ManufacturedReflector.exploration,
    ManufacturedReflector.reusableSwitches] at hcharge ⊢
  omega

/-- A one-novelty changed-contact tail plus the boundary-reserved `N+2`
compressed lead gives the required `N+3` global bound. -/
theorem PartialSecondRunSharp.ChangedContact.changed_all_run_distinct_le_N_add_three_of_one_novelty_and_reserved_absent
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hk0 : k0 < N)
    (hreservedExploration : Not (k0 ∈
      (ManufacturedReflector.flip R).exploration.map passageSwitch))
    (hreservedApproach : Not (k0 ∈
      C.approachFirstWriterSwitches N))
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).baseState))).Nodup)
    (hlocal : NoveltyCoverOn w N
      (e, (ManufacturedReflector.flip R).activatedState)
      (times.map (fun k => k -
        ((ManufacturedReflector.flip R).exploration.length +
          (ManufacturedReflector.flip R).runway.length + 1)))
      (C.compressedLead N) 1) :
    times.length <= N + 3 := by
  let firstTravel :=
    (ManufacturedReflector.flip R).exploration.length +
      (ManufacturedReflector.flip R).runway.length + 1
  let localTimes := times.map (fun k => k - firstTravel)
  have hreach : stepN w firstTravel
      (g, (ManufacturedReflector.flip R).baseState) =
        some (e, (ManufacturedReflector.flip R).activatedState) := by
    simpa [firstTravel] using
      (ManufacturedReflector.flip R).manufacturing_journey_reaches_activated
        hA
  have hlocal' : NoveltyCoverOn w N
      (e, (ManufacturedReflector.flip R).activatedState)
      localTimes (C.compressedLead N) 1 := by
    simpa [localTimes, firstTravel] using hlocal
  obtain ⟨fresh, hfresh, hmem⟩ := hlocal'
  have hcover : NoveltyCoverOn w N
      (g, (ManufacturedReflector.flip R).baseState)
      times (C.compressedLead N) 1 := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hfirst : k <= firstTravel
    · unfold PartialSecondRunSharp.ChangedContact.compressedLead
      apply List.mem_append_left
      apply List.mem_append_left
      apply (ManufacturedReflector.flip R).mem_sharpHistoryCore_of_mem
      exact (ManufacturedReflector.flip R).manufacturing_journey_mem_sharpHistory
        hA (by simpa [firstTravel] using hfirst)
    · let d := k - firstTravel
      have hdMem : d ∈ localTimes := by
        dsimp [d, localTimes]
        exact List.mem_map.mpr ⟨k, hk, rfl⟩
      have hm := hmem d hdMem
      have hshift := restrictedTonguesAt_sub_of_reach
        (N := N) hreach (by omega) (hlive k hk)
      rw [hshift]
      exact hm
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hlength :=
    C.compressedLead_length_le_N_add_two_of_reserved_absent
      hN hA hk0 hreservedExploration hreservedApproach
  omega

/-- With an exploration-absent boundary coordinate that is not approach
first-written, every changed contact already fits `N+3`.  If the old action is
first-written, the one-novelty tail and impossibility of the runway residual
replace the action-coordinate reserve. -/
theorem PartialSecondRunSharp.ChangedContact.changed_all_run_distinct_le_N_add_three_of_reserved_absent
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hk0 : k0 < N)
    (hreservedExploration : Not (k0 ∈
      (ManufacturedReflector.flip R).exploration.map passageSwitch))
    (hreservedApproach : Not (k0 ∈
      C.approachFirstWriterSwitches N))
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).baseState))).Nodup) :
    times.length <= N + 3 := by
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · exact C.backward_all_run_distinct_le_N_add_three
      hN hA hbackward times hlive hnd
  · by_cases haction :
        R.actionSwitch ∈ C.approachFirstWriterSwitches N
    · let localTimes := times.map (fun k => k -
          ((ManufacturedReflector.flip R).exploration.length +
            (ManufacturedReflector.flip R).runway.length + 1))
      rcases C.forward_flip_one_novelty_or_runway_residual
          hforward hrepair hrestored haction localTimes with
        hone | hresidual
      · apply C.changed_all_run_distinct_le_N_add_three_of_one_novelty_and_reserved_absent
          hN hA hk0 hreservedExploration hreservedApproach
          times hlive hnd
        simpa [localTimes] using hone
      · exact (Classical.choice hresidual).impossible hN hA |>.elim
    · exact C.changed_all_run_distinct_le_N_add_three_of_action_and_reserved_absent
        hN hA haction hk0 hreservedExploration hreservedApproach
        times hlive hnd

theorem PartialSecondRunSharp.ChangedContact.stem_switch_not_mem_approachFirstWriterSwitches
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hstem : e = 3 * k0) :
    Not (k0 ∈ C.approachFirstWriterSwitches N) := by
  intro hm
  unfold PartialSecondRunSharp.ChangedContact.approachFirstWriterSwitches at hm
  obtain ⟨k, hk, hwriter⟩ := List.mem_map.mp hm
  have hkData := mem_rawFirstWriterTimes_iff.mp hk
  have hklt : k < C.approach.length := hkData.1
  have hprod : RawProductiveAt w N
      (e, (ManufacturedReflector.flip R).activatedState) k :=
    hkData.2.1
  by_cases hkzero : k = 0
  · subst k
    apply hprod.2
    rcases Option.isSome_iff_exists.mp hprod.1 with ⟨next, hnext⟩
    have hnextOne : stepN w 1
        (e, (ManufacturedReflector.flip R).activatedState) = some next := by
      simpa using hnext
    have hemod : e % 3 = 0 := by omega
    have hediv : e / 3 = k0 := by omega
    have harrive : arrive (ManufacturedReflector.flip R).activatedState e =
        (selectedBranch (ManufacturedReflector.flip R).activatedState k0,
          (ManufacturedReflector.flip R).activatedState) := by
      simp [arrive, hemod, hediv, selectedBranch]
    have hnextState : next.2 =
        (ManufacturedReflector.flip R).activatedState := by
      simp only [stepN, step, harrive] at hnextOne
      cases hlink : w.link
          (selectedBranch (ManufacturedReflector.flip R).activatedState k0) with
      | none => simp [hlink] at hnextOne
      | some q =>
          simp [hlink] at hnextOne
          exact (Prod.mk.inj hnextOne.symm).2
    unfold restrictedTonguesAt tonguesAt
    rw [hnextOne]
    simp [hnextState, stepN]
  · have hkpos : 0 < k := by omega
    have hzeroInside : 0 < C.approach.length := by omega
    have hzeroWriter :=
      C.approach_trace.rawWriterAt_eq_passageSwitch_getElem
        (k := 0) hzeroInside
    have hkWriter :=
      C.approach_trace.rawWriterAt_eq_passageSwitch_getElem
        (k := k) hklt
    have hpair := List.pairwise_iff_getElem.mp C.approach_simple
    have hzeroMap : 0 < (C.approach.map passageSwitch).length := by
      simpa using hzeroInside
    have hkMap : k < (C.approach.map passageSwitch).length := by
      simpa using hklt
    have hne := hpair 0 k hzeroMap hkMap hkpos
    apply hne
    simp only [List.getElem_map]
    rw [← hzeroWriter, ← hkWriter]
    calc
      rawWriterAt w
          (e, (ManufacturedReflector.flip R).activatedState) 0 =
          e / 3 := by simp [rawWriterAt, rawEntryAt, stepN]
      _ = k0 := by omega
      _ = rawWriterAt w
          (e, (ManufacturedReflector.flip R).activatedState) k :=
        hwriter.symm


/-- In the productive-boundary geometry, the shifted run starts at the stem of
the reserved switch.  Switch simplicity therefore makes the boundary reserve
automatic, and every changed-contact branch is at most `N+3`. -/
theorem PartialSecondRunSharp.ChangedContact.changed_all_run_distinct_le_N_add_three_of_stem_reserved
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hk0 : k0 < N)
    (hstem : e = 3 * k0)
    (hreservedExploration : Not (k0 ∈
      (ManufacturedReflector.flip R).exploration.map passageSwitch))
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).baseState))).Nodup) :
    times.length <= N + 3 := by
  apply C.changed_all_run_distinct_le_N_add_three_of_reserved_absent
    hN hA hk0 hreservedExploration
    (C.stem_switch_not_mem_approachFirstWriterSwitches hstem)
    times hlive hnd

end GeneralN
