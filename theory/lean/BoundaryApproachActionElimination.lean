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
  have hbound :=
    C.changed_all_run_add_extras_le_N_add_three_add_budget
      hN hA [k0] (by simp)
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
      times hlive hnd hlocal
  simp only [List.length_singleton] at hbound
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
