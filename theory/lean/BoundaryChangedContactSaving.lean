import KnownEdgeNAddFourChangedClosed

/-!
# Reserving the boundary coordinate in a changed contact

The productive-boundary residuals feed a changed contact whose closure is
exactly `N+4` in the forward-flip case: `N+2` compressed lead plus two
local novelties when the flip action is not approach-written, `N+3` plus
one otherwise.  To also save the arbitrary boundary vector we need one
more unit.  This file provides it whenever the boundary switch `k0` is
absent from the first reflector's exploration *and* from the strict
approach's productive first writers: `k0` then occupies a fresh ambient
coordinate alongside the reusable support, the approach writers, and the
reserved action switch, lowering the compressed lead to `N+1` and the
forward-flip changed-contact run to `N+3`.

The two remaining tight sub-geometries — the flip action or the boundary
switch productively first-written during the strict approach — are the
refined residuals the sharp law still has to eliminate.
-/

namespace GeneralN

/-- A switch absent from a flip reflector's exploration is absent from its
reusable support. -/
theorem ManufacturedFlipReflector.reserved_not_mem_reusable
    {w : Wiring} {g e k0 : Nat}
    (R : ManufacturedFlipReflector w g e)
    (habsent : Not (k0 ∈
      (ManufacturedReflector.flip R).exploration.map passageSwitch)) :
    Not (k0 ∈ (ManufacturedReflector.flip R).reusableSwitches) := by
  intro hmem
  apply habsent
  change k0 ∈ ((R.runway ++ R.candy).map passageSwitch) at hmem
  obtain ⟨passage, hp, hswitch⟩ := List.mem_map.mp hmem
  apply List.mem_map.mpr
  refine ⟨passage, ?_, hswitch⟩
  change passage ∈ R.runway ++ (R.mouth, R.firstArm) :: R.candy
  rcases List.mem_append.mp hp with hrunway | hcandy
  · exact List.mem_append_left _ hrunway
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hcandy)

/-- A switch absent from a flip reflector's exploration differs from its
facing-action switch. -/
theorem ManufacturedFlipReflector.reserved_ne_action
    {w : Wiring} {g e k0 : Nat}
    (R : ManufacturedFlipReflector w g e)
    (habsent : Not (k0 ∈
      (ManufacturedReflector.flip R).exploration.map passageSwitch)) :
    k0 ≠ R.actionSwitch := by
  intro hEq
  apply habsent
  apply List.mem_map.mpr
  refine ⟨(R.mouth, R.firstArm), ?_, ?_⟩
  · change (R.mouth, R.firstArm) ∈
      R.runway ++ (R.mouth, R.firstArm) :: R.candy
    exact List.mem_append_right _ List.mem_cons_self
  · simpa [passageSwitch, ManufacturedFlipReflector.actionSwitch]
      using hEq.symm

/-- If neither the omitted action switch nor the reserved boundary switch
is approach-first-written, and the boundary switch is exploration-absent,
then reusable support, approach writers, action, and boundary occupy
pairwise distinct ambient coordinates. -/
theorem PartialSecondRunSharp.ChangedContact.reusable_add_approach_writers_add_action_add_reserved_le
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (habsent : Not (R.actionSwitch ∈
      C.approachFirstWriterSwitches N))
    (hk0 : k0 < N)
    (hreservedExploration : Not (k0 ∈
      (ManufacturedReflector.flip R).exploration.map passageSwitch))
    (hreservedApproach : Not (k0 ∈
      C.approachFirstWriterSwitches N)) :
    (ManufacturedReflector.flip R).reusableSwitches.length +
        (rawFirstWriterTimes w N
          (e, (ManufacturedReflector.flip R).activatedState)
          C.approach.length).length + 2 <= N := by
  have h := C.reusable_add_approach_writers_add_extras_le hN hA
    [k0, R.actionSwitch]
    (by simp [R.reserved_ne_action hreservedExploration])
    (by intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hk0
        rw [List.mem_singleton] at hs
        subst s
        exact R.action_lt hN)
    (by intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact R.reserved_not_mem_reusable hreservedExploration
        rw [List.mem_singleton] at hs
        subst s
        exact R.action_not_mem_reusable)
    (by intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hreservedApproach
        rw [List.mem_singleton] at hs
        subst s
        exact habsent)
  simpa using h

/-- Reserving both the action and boundary coordinates lowers the
changed-contact compressed lead from `N+2` to `N+1`. -/
theorem PartialSecondRunSharp.ChangedContact.compressedLead_length_le_N_add_one_of_action_and_reserved_absent
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (habsent : Not (R.actionSwitch ∈
      C.approachFirstWriterSwitches N))
    (hk0 : k0 < N)
    (hreservedExploration : Not (k0 ∈
      (ManufacturedReflector.flip R).exploration.map passageSwitch))
    (hreservedApproach : Not (k0 ∈
      C.approachFirstWriterSwitches N)) :
    (C.compressedLead N).length <= N + 1 := by
  have hboundary :
      VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState ∈
        rawFirstWriterHistory w N
          (e, (ManufacturedReflector.flip R).activatedState)
          C.approach.length := by
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN]
  have hcharge :=
    C.reusable_add_approach_writers_add_action_add_reserved_le
      hN hA habsent hk0 hreservedExploration hreservedApproach
  unfold PartialSecondRunSharp.ChangedContact.compressedLead
  rw [List.length_append, List.length_append,
    List.length_erase_of_mem hboundary,
    (ManufacturedReflector.flip R).sharpHistoryCore_length]
  simp [rawFirstWriterHistory, ManufacturedReflector.exploration,
    ManufacturedReflector.reusableSwitches] at hcharge ⊢
  omega

/-- **The saving changed-contact bound.**  If the strict approach
first-writes neither the omitted action switch nor the exploration-absent
boundary switch, the whole original run of a forward-flip changed contact
carries at most `N+3` distinct restricted tongue vectors — one unit inside
the unconditional `N+4`, exactly the room the productive boundary needs. -/
theorem PartialSecondRunSharp.ChangedContact.changed_all_run_distinct_le_N_add_three_of_action_and_reserved_absent
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (habsent : Not (R.actionSwitch ∈
      C.approachFirstWriterSwitches N))
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
  obtain ⟨fresh, hfresh, hlocal⟩ :=
    C.changed_two_novelty (N := N) localTimes
  have hcover : NoveltyCoverOn w N
      (g, (ManufacturedReflector.flip R).baseState)
      times (C.compressedLead N) 2 := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hfirst : k <= firstTravel
    · unfold PartialSecondRunSharp.ChangedContact.compressedLead
      apply List.mem_append_left
      apply List.mem_append_left
      apply (ManufacturedReflector.flip R).mem_sharpHistoryCore_of_mem
      exact (ManufacturedReflector.flip R).manufacturing_journey_mem_sharpHistory
        hA (by
          simpa [firstTravel] using hfirst)
    · let d := k - firstTravel
      have hdMem : d ∈ localTimes := by
        dsimp [d, localTimes]
        exact List.mem_map.mpr ⟨k, hk, rfl⟩
      have hm := hlocal d hdMem
      have hshift := restrictedTonguesAt_sub_of_reach
        (N := N) hreach (by omega) (hlive k hk)
      rw [hshift]
      exact hm
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hlength :=
    C.compressedLead_length_le_N_add_one_of_action_and_reserved_absent
      hN hA habsent hk0 hreservedExploration hreservedApproach
  omega

/-! ## The keystone dichotomy

A sharp changed contact over a *stay* reflector always fits `N+3`.  Over a
*flip* reflector with an exploration-absent boundary switch, it fits `N+3`
unless the strict approach productively first-writes the action switch or
the boundary switch — the two refined residual geometries. -/

/-- A changed contact over a stay reflector is bounded by `N+3`: backward
contacts by the compressed-lead theorem, forward contacts by the
zero-novelty stay tail. -/
theorem PartialSecondRunSharp.ChangedContact.stay_saving_all_run_distinct_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedStayReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w
      (ManufacturedReflector.stay R))
    (hA : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths
      (ManufacturedReflector.stay R).activatedState)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k
        (g, (ManufacturedReflector.stay R).baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N
        (g, (ManufacturedReflector.stay R).baseState))).Nodup) :
    times.length <= N + 3 := by
  let S := C
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · have hbackwardS : S.x = S.oriented.1 := by
      exact hbackward
    exact S.backward_all_run_distinct_le_N_add_three
      hN hA hbackwardS times hlive hnd
  · let localTimes := times.map (fun k => k -
      ((ManufacturedReflector.stay R).exploration.length +
        (ManufacturedReflector.stay R).runway.length + 1))
    have hlocal := C.forward_stay_all_time_zero_novelty
      (N := N) hforward hrepair hrestored localTimes
    have hbound := changedContact_local_novelty_count
      hN C hA times hlive hnd hlocal
    omega

/-- **The flip keystone dichotomy.**  A changed contact over a flip
reflector whose boundary switch is exploration-absent either fits `N+3`
or productively first-writes the action switch or the boundary switch
during its strict approach. -/
theorem PartialSecondRunSharp.ChangedContact.flip_saving_le_N_add_three_or_approach_written
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hk0 : k0 < N)
    (hreservedExploration : Not (k0 ∈
      (ManufacturedReflector.flip R).exploration.map passageSwitch))
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).baseState))).Nodup) :
    times.length <= N + 3 \/
      R.actionSwitch ∈
        C.approachFirstWriterSwitches N \/
      k0 ∈
        C.approachFirstWriterSwitches N := by
  classical
  let S := C
  by_cases haction : R.actionSwitch ∈
      S.approachFirstWriterSwitches N
  · exact Or.inr (Or.inl haction)
  by_cases hreserved : k0 ∈ S.approachFirstWriterSwitches N
  · exact Or.inr (Or.inr hreserved)
  exact Or.inl
    (S.changed_all_run_distinct_le_N_add_three_of_action_and_reserved_absent
      hN hA haction hk0 hreservedExploration hreserved
        times hlive hnd)

end GeneralN
