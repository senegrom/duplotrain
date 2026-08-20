import BoundaryChangedContactSaving

/-!
# Changed-contact bound with a reserved boundary stem

When the changed-contact approach first-writes the old flip action, the local
forward tail has only one fresh corner (the runway alternative is impossible).
Consequently the exploration-absent boundary coordinate alone supplies the
missing ambient reserve: the compressed lead is at most `N+2`, and the whole
changed-contact run is at most `N+3`.  At the productive boundary the shifted
run starts at the boundary stem, so switch simplicity also rules out a first
write of the boundary switch.  Every such changed contact therefore fits
`N+3`.
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
  have h := C.reusable_add_approach_writers_add_extras_le hN hA
    [k0] (by simp)
    (by intro s hs
        rw [List.mem_singleton] at hs
        subst s
        exact hk0)
    (by intro s hs
        rw [List.mem_singleton] at hs
        subst s
        exact R.reserved_not_mem_reusable hreservedExploration)
    (by intro s hs
        rw [List.mem_singleton] at hs
        subst s
        exact hreservedApproach)
  simpa using h

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
    (stem_switch_not_mem_firstWriterSwitches_of_simple_trace
      (N := N) hstem C.approach_trace C.approach_simple)
    times hlive hnd

end GeneralN
