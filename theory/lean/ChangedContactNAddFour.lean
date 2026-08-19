import ReuseForcesReplayClosure
import BoundaryDoubleDuplicate

/-!
# The changed-contact `N+4` frontier

The existing changed-support theorem pays `N+3` for the compressed lead and
two further Gray corners.  For a flip reflector, however, the facing action
switch is deliberately absent from the reusable support.  Unless the strict
pre-contact approach productively first-writes that switch, it is a reserved
ambient coordinate.  Charging that coordinate as well lowers the lead to
`N+2`, hence closes the whole changed-contact branch at `N+4`.

Everything here is symbolic in `N`; no finite enumeration is used.
-/


/-!
## Productive writes cannot happen inside a pointwise retrace

A settled retrace window (every depth shows the settled tongue state)
admits no productive write: the vectors before and after any interior
step coincide.  Extracted from the serial-continuation module so the
sharp changed-contact and protected-pair closures do not depend on the
six-event programme.
-/

namespace GeneralN

/-- A productive write cannot occur strictly inside a window whose every
depth carries the settled state. -/
theorem productive_not_inside_pointwise_retrace
    {w : Wiring} {N repeatTime span openTime q : Nat}
    {start : Nat × Tongues} {old settled : Tongues}
    (hrepeat : stepN w repeatTime start = some (q, old))
    (hpointwise : ∀ d, d ≤ span →
      ∃ port, stepN w d (q, old) =
        some (port, if d = 0 then old else settled))
    (hproductive : RawProductiveAt w N start openTime)
    (hafter : repeatTime < openTime) :
    repeatTime + span ≤ openTime := by
  apply Classical.byContradiction
  intro hnot
  let d := openTime - repeatTime
  have hdPositive : 0 < d := by
    dsimp [d]
    omega
  have hdLt : d < span := by
    dsimp [d]
    omega
  have hdSucc : d + 1 ≤ span := by omega
  have htime : repeatTime + d = openTime := by
    dsimp [d]
    omega
  have htimeSucc : repeatTime + (d + 1) = openTime + 1 := by omega
  obtain ⟨beforePort, hbeforeLocal⟩ := hpointwise d (by omega)
  obtain ⟨afterPort, hafterLocal⟩ := hpointwise (d + 1) hdSucc
  have hbeforeGlobal :
      stepN w openTime start = some (beforePort, settled) := by
    rw [← htime, stepN_add, hrepeat]
    simpa [Nat.ne_of_gt hdPositive] using hbeforeLocal
  have hafterGlobal :
      stepN w (openTime + 1) start = some (afterPort, settled) := by
    rw [← htimeSucc, stepN_add, hrepeat]
    simp only [Option.bind_some]
    simpa using hafterLocal
  apply hproductive.2
  simp [restrictedTonguesAt, tonguesAt,
    hbeforeGlobal, hafterGlobal]


/-- A switch-simple physical trace cannot return to its literal starting
port and then continue.  The raw writer at time zero and at the return time
would both be the switch of that port, contradicting the indexed `Nodup`
property of the passage word.  The tongue states need not agree. -/
theorem PhysicalTrace.no_strict_return_to_start_port
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    {k : Nat} {returned : Tongues}
    (hpositive : 0 < k)
    (hinside : k < passages.length)
    (hreturn : stepN w k start = some (start.1, returned)) : False := by
  have hzero :=
    htrace.rawWriterAt_eq_passageSwitch_getElem
      (k := 0) (by omega)
  have hreturned :=
    htrace.rawWriterAt_eq_passageSwitch_getElem
      (k := k) hinside
  have hwriters :
      rawWriterAt w start 0 = rawWriterAt w start k := by
    simp [rawWriterAt, rawEntryAt, stepN, hreturn]
  have hpair := List.pairwise_iff_getElem.mp hsimple
  have hne := hpair 0 k (by simpa using (show 0 < passages.length by omega))
    (by simpa using hinside) hpositive
  apply hne
  simpa [hzero, hreturned] using hwriters

/-- Productive first-writer coordinates in the strict approach to the first
support-changing contact. -/
def PartialSecondRunSharp.ChangedContact.approachFirstWriterSwitches
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A) (N : Nat) : List Nat :=
  (rawFirstWriterTimes w N (e, A.activatedState)
      C.approach.length).map
    (rawWriterAt w (e, A.activatedState))

/-- Reusable support, approach first-writers, and any duplicate-free list
of extra switches avoiding both occupy pairwise distinct ambient
coordinates. -/
theorem PartialSecondRunSharp.ChangedContact.reusable_add_approach_writers_add_extras_le
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (extras : List Nat)
    (hextrasNodup : extras.Nodup)
    (hextrasLt : forall s, s ∈ extras -> s < N)
    (hextrasReusable : forall s, s ∈ extras ->
      Not (s ∈ (ManufacturedReflector.flip R).reusableSwitches))
    (hextrasApproach : forall s, s ∈ extras ->
      Not (s ∈ C.approachFirstWriterSwitches N)) :
    (ManufacturedReflector.flip R).reusableSwitches.length +
        (rawFirstWriterTimes w N
          (e, (ManufacturedReflector.flip R).activatedState)
          C.approach.length).length + extras.length <= N := by
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
      C.approach_trace.productive_writer_not_old_reusable (ManufacturedReflector.flip R) C.approach_simple
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
  have hextrasNotOccupied : forall s, s ∈ extras -> Not (s ∈ occupied) := by
    intro s hs hm
    rcases List.mem_append.mp hm with hold | hfresh
    · exact hextrasReusable s hs hold
    · apply hextrasApproach s hs
      simpa [PartialSecondRunSharp.ChangedContact.approachFirstWriterSwitches,
        writers, times] using hfresh
  have hallNodup : (extras ++ occupied).Nodup :=
    List.nodup_append.mpr
      ⟨hextrasNodup, hoccupiedNodup,
        fun s hs t ht hEq => hextrasNotOccupied s hs (hEq ▸ ht)⟩
  have hallLt : forall switch,
      switch ∈ extras ++ occupied -> switch < N := by
    intro switch hswitch
    rcases List.mem_append.mp hswitch with hextra | hoccupied
    · exact hextrasLt switch hextra
    rcases List.mem_append.mp hoccupied with hold | hfresh
    · exact (ManufacturedReflector.flip R).reusableSwitch_lt hN hold
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hfresh
      have hkData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hk)
      exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hallNodup hallLt
  have hlength :
      (extras ++ occupied).length =
        (ManufacturedReflector.flip R).reusableSwitches.length +
          times.length + extras.length := by
    simp [occupied, writers]
    omega
  rw [hlength] at hbound
  simpa [times] using hbound

/-- If the strict approach does not first-write the omitted action switch,
then reusable support, approach writers, and that reserved switch occupy
pairwise distinct ambient coordinates. -/
theorem PartialSecondRunSharp.ChangedContact.reusable_add_approach_writers_add_action_le
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (habsent : Not (R.actionSwitch ∈
      C.approachFirstWriterSwitches N)) :
    (ManufacturedReflector.flip R).reusableSwitches.length +
        (rawFirstWriterTimes w N
          (e, (ManufacturedReflector.flip R).activatedState)
          C.approach.length).length + 1 <= N := by
  have h := C.reusable_add_approach_writers_add_extras_le hN hA
    [R.actionSwitch] (by simp)
    (by intro s hs
        rw [List.mem_singleton] at hs
        subst s
        exact R.action_lt hN)
    (by intro s hs
        rw [List.mem_singleton] at hs
        subst s
        exact R.action_not_mem_reusable)
    (by intro s hs
        rw [List.mem_singleton] at hs
        subst s
        exact habsent)
  simpa using h

/-- Reserving the flip action coordinate lowers the changed-contact history
from `N+3` to `N+2`. -/
theorem PartialSecondRunSharp.ChangedContact.compressedLead_length_le_N_add_two_of_action_absent
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (habsent : Not (R.actionSwitch ∈
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
    C.reusable_add_approach_writers_add_action_le hN hA habsent
  unfold PartialSecondRunSharp.ChangedContact.compressedLead
  rw [List.length_append, List.length_append,
    List.length_erase_of_mem hboundary,
    (ManufacturedReflector.flip R).sharpHistoryCore_length]
  simp [rawFirstWriterHistory, ManufacturedReflector.exploration,
    ManufacturedReflector.reusableSwitches] at hcharge ⊢
  omega

/-- **Unconditional `N+4` subcase.**  If the strict approach does not
productively first-write the old reflector's omitted action coordinate, the
existing two-corner Gray-tail theorem closes the entire original run at
`N+4`. -/
theorem PartialSecondRunSharp.ChangedContact.changed_all_run_distinct_le_N_add_four_of_action_absent
    {w : Wiring} {N g e : Nat}
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
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).baseState))).Nodup) :
    times.length <= N + 4 := by
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
    C.compressedLead_length_le_N_add_two_of_action_absent
      hN hA habsent
  omega

/-- A one-novelty local tail after the changed contact is exactly enough for
the existing `N+3` compressed lead to give a global `N+4` bound. -/
theorem PartialSecondRunSharp.ChangedContact.changed_all_run_distinct_le_N_add_four_of_one_novelty
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup)
    (hlocal : NoveltyCoverOn w N (e, A.activatedState)
      (times.map (fun k => k -
        (A.exploration.length + A.runway.length + 1)))
      (C.compressedLead N) 1) :
    times.length <= N + 4 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localTimes := times.map (fun k => k - firstTravel)
  have hreach : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hlocal' : NoveltyCoverOn w N (e, A.activatedState)
      localTimes (C.compressedLead N) 1 := by
    simpa [localTimes, firstTravel] using hlocal
  obtain ⟨fresh, hfresh, hmem⟩ := hlocal'
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times (C.compressedLead N) 1 := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hfirst : k <= firstTravel
    · unfold PartialSecondRunSharp.ChangedContact.compressedLead
      apply List.mem_append_left
      apply List.mem_append_left
      apply A.mem_sharpHistoryCore_of_mem
      exact A.manufacturing_journey_mem_sharpHistory hA (by
        simpa [firstTravel] using hfirst)
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
  have hlength := C.compressedLead_length_le hN hA
  omega

structure PartialSecondRunSharp.ChangedContact.RunwayNAddFourResidual
    {w : Wiring} {N g e : Nat}
    (R : ManufacturedFlipReflector w g e)
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R)) : Type where
  action_first_written :
    R.actionSwitch ∈ C.approachFirstWriterSwitches N
  old_corner_missing :
    Not (VectorCount.restrict N
      (flipAt C.contactState R.actionSwitch) ∈ C.compressedLead N)

/-- A forward changed contact into a flip reflector has a one-novelty tail,
unless it produces the exact runway Gray-square residual above. -/
theorem PartialSecondRunSharp.ChangedContact.forward_flip_one_novelty_or_runway_residual
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair : arrive C.nextState C.oriented.1 =
      (C.oriented.2, repaired))
    (hrestored : arrive repaired C.oriented.2 =
      (C.oriented.1, repaired))
    (haction : R.actionSwitch ∈ C.approachFirstWriterSwitches N)
    (times : List Nat) :
    NoveltyCoverOn w N
      (e, (ManufacturedReflector.flip R).activatedState)
      times (C.compressedLead N) 1 ∨
    Nonempty (C.RunwayNAddFourResidual (N := N) R) := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, hApproachGrooved,
      hApproachForeign, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeignNew, hLobe, hreach⟩ :=
    partial_first_forward_contact_active_lead
      (A := ManufacturedReflector.flip R) C.split C.full_simple
      C.approach_trace C.old_grooves C.arrive_eq C.changed
      C.oriented_mem C.oriented_groove C.oriented_switch
      hforward hrepair hrestored
  let K := C.approach.length + 1
  let state := C.contactState
  let alternate := flipAt state (mouth / 3)
  have hreach' : stepN w K
      (e, (ManufacturedReflector.flip R).activatedState) =
        some (outside, alternate) := by
    simpa [K, state, alternate] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.compressedLead N := by
    simpa [hnextAlternate] using C.next_mem_compressedLead (N := N)
  have hstateHistorical :
      VectorCount.restrict N state ∈ C.compressedLead N := by
    simpa [state] using C.contact_mem_compressedLead (N := N)
  have hleadHistorical : forall j, j ∈ times -> j < K ->
      restrictedTonguesAt w N
        (e, (ManufacturedReflector.flip R).activatedState) j ∈
          C.compressedLead N := by
    intro j _hj hjK
    exact C.mem_compressedLead_of_approach (N := N) (by
      dsimp [K] at hjK
      omega)
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ :=
      List.append_of_mem hrunway
    obtain ⟨D, hDAction, hEntryOldNe, hDpaths,
        hNewAvoidsDRaw⟩ :=
      R.suffix_after_runway_passage state hRpaths
        hrunwaySplit hmouthLink
    have hentrySwitch : entry / 3 = mouth / 3 := by
      have hheadGroove : arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hswitch := arrive_exit_switch state entry
      rw [hheadGroove] at hswitch
      exact hswitch.symm
    have hActionsNe : mouth / 3 ≠ D.actionSwitch := by
      rw [← hentrySwitch]
      exact hEntryOldNe
    have hNewAvoidsD :
        (LocalAction.flip (mouth / 3)).Avoids D.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsDRaw
    by_cases holdHistorical :
        VectorCount.restrict N
          (flipAt state R.actionSwitch) ∈ C.compressedLead N
    · have holdHistoricalD :
          VectorCount.restrict N
            (flipAt state D.actionSwitch) ∈ C.compressedLead N := by
        simpa [hDAction] using holdHistorical
      by_cases hcontact : exists passage, passage ∈ candy /\
          passageSwitch passage = D.actionSwitch
      · left
        exact manufactured_flip_arbitrary_lobe_absolute_one_novelty
          D state hDpaths hNewAvoidsD hentryBranch hentrySwitch
          hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
          hmouthLink hcontact hreach' times (C.compressedLead N)
          hentryHistorical hstateHistorical holdHistoricalD
          hleadHistorical
      · have hCandyForeignOld : forall passage, passage ∈ candy ->
            passageSwitch passage ≠ D.actionSwitch := by
          intro passage hp hEq
          exact hcontact ⟨passage, hp, hEq⟩
        left
        exact manufactured_suffix_explicit_lobe_absolute_one_novelty
          D state hDpaths hNewAvoidsD hActionsNe hentryBranch
          hentrySwitch hfullGrooved hfullTrace hcrossed
          hCandyForeignNew hCandyForeignOld hLobe hmouthLink hreach'
          times (C.compressedLead N) hentryHistorical hstateHistorical
          holdHistoricalD hleadHistorical
    · right
      have hmissingR : Not (VectorCount.restrict N
          (flipAt C.contactState R.actionSwitch) ∈
            C.compressedLead N) := by
        simpa [state] using holdHistorical
      exact ⟨{
        action_first_written := haction
        old_corner_missing := hmissingR
      }⟩
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        hentryOld hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    have hone := manufactured_flip_candy_splice_absolute_one_novelty
      R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
      hold horientation hentryGrooved hApproachReplay
      hApproachGrooved hApproachForeign hcrossed hmouthLink harms
      hreach' N (C.compressedLead N) hentryHistorical times
      hleadHistorical
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact Or.inl ⟨fresh, hfresh, hmem⟩

/-- **Sharp changed-contact frontier.**  For arbitrary `N`, every changed
support contact is bounded by `N+4` unless it yields the explicit runway
Gray-square residual.  No completed second reflector is assumed. -/
theorem PartialSecondRunSharp.ChangedContact.changed_N_add_four_or_runway_residual
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).baseState))).Nodup) :
    times.length <= N + 4 ∨
      Nonempty (C.RunwayNAddFourResidual (N := N) R) := by
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · left
    have hsmall := C.backward_all_run_distinct_le_N_add_three
      hN hA hbackward times hlive hnd
    omega
  · by_cases haction :
        R.actionSwitch ∈ C.approachFirstWriterSwitches N
    · let localTimes := times.map (fun k => k -
          ((ManufacturedReflector.flip R).exploration.length +
            (ManufacturedReflector.flip R).runway.length + 1))
      rcases C.forward_flip_one_novelty_or_runway_residual
          hforward hrepair hrestored haction localTimes with
        hone | hresidual
      · left
        apply C.changed_all_run_distinct_le_N_add_four_of_one_novelty
          hN hA times hlive hnd
        simpa [localTimes] using hone
      · exact Or.inr hresidual
    · left
      exact C.changed_all_run_distinct_le_N_add_four_of_action_absent
        hN hA haction times hlive hnd

/-- The residual action write cannot be the final productive write of the
strict approach.  Otherwise the post-action vector would persist to the
contact, and flipping the action bit back would recover the historical
pre-action vector, contradicting `old_corner_missing`. -/
theorem PartialSecondRunSharp.ChangedContact.RunwayNAddFourResidual.exists_later_productive
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    {C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R)}
    (F : C.RunwayNAddFourResidual (N := N) R) :
    exists actionTime laterTime,
      actionTime ∈ rawFirstWriterTimes w N
        (e, (ManufacturedReflector.flip R).activatedState)
        C.approach.length /\
      rawWriterAt w
        (e, (ManufacturedReflector.flip R).activatedState)
        actionTime = R.actionSwitch /\
      actionTime < laterTime /\
      laterTime < C.approach.length /\
      RawProductiveAt w N
        (e, (ManufacturedReflector.flip R).activatedState)
        laterTime := by
  let start : Nat × Tongues :=
    (e, (ManufacturedReflector.flip R).activatedState)
  have haction := F.action_first_written
  change R.actionSwitch ∈
    (rawFirstWriterTimes w N start C.approach.length).map
      (rawWriterAt w start) at haction
  obtain ⟨actionTime, hactionTime, hwriter⟩ :=
    List.mem_map.mp haction
  have hactionData := mem_rawFirstWriterTimes_iff.mp hactionTime
  by_cases hlater : exists laterTime,
      actionTime < laterTime /\
      laterTime < C.approach.length /\
      RawProductiveAt w N start laterTime
  · obtain ⟨laterTime, hleft, hright, hprod⟩ := hlater
    exact ⟨actionTime, laterTime, hactionTime, hwriter,
      hleft, hright, hprod⟩
  · exfalso
    apply F.old_corner_missing
    let span := C.approach.length - (actionTime + 1)
    have hsum : actionTime + 1 + span = C.approach.length := by
      dsimp [span]
      omega
    have hfinish : stepN w (actionTime + 1 + span) start =
        some (C.p, C.contactState) := by
      rw [hsum]
      simpa [start] using C.approach_trace.sound
    have hquiet : forall j,
        actionTime + 1 <= j ->
        j < actionTime + 1 + span ->
        Not (RawProductiveAt w N start j) := by
      intro j hjLeft hjRight hprod
      apply hlater
      refine ⟨j, by omega, ?_, hprod⟩
      rw [hsum] at hjRight
      exact hjRight
    have hstable := restrictedTonguesAt_eq_of_quiet_interval
      hfinish hquiet
    rw [hsum] at hstable
    have hcontactRestriction :
        VectorCount.restrict N C.contactState =
          VectorCount.restrict N
            (tonguesAt w start (actionTime + 1)) := by
      simpa [restrictedTonguesAt, tonguesAt, C.approach_trace.sound,
        start] using hstable
    have hprod := hactionData.2.1
    have hflipRaw := rawProductiveAt_restricted_flip hprod
    have hflip :
        VectorCount.restrict N
            (tonguesAt w start (actionTime + 1)) =
          VectorCount.restrict N
            (flipAt (tonguesAt w start actionTime)
              R.actionSwitch) := by
      simpa [restrictedTonguesAt, hwriter] using hflipRaw
    have hundoContact := restrict_flipAt_congr
      (C := R.actionSwitch) hcontactRestriction
    have hundoWrite := restrict_flipAt_congr
      (C := R.actionSwitch) hflip
    have holdCorner :
        VectorCount.restrict N
            (flipAt C.contactState R.actionSwitch) =
          restrictedTonguesAt w N start actionTime := by
      calc
        VectorCount.restrict N
            (flipAt C.contactState R.actionSwitch) =
            VectorCount.restrict N
              (flipAt (tonguesAt w start (actionTime + 1))
                R.actionSwitch) := hundoContact
        _ = VectorCount.restrict N
              (flipAt
                (flipAt (tonguesAt w start actionTime)
                  R.actionSwitch)
                R.actionSwitch) := hundoWrite
        _ = restrictedTonguesAt w N start actionTime := by
          rw [flipAt_flipAt]
          rfl
    rw [holdCorner]
    exact C.mem_compressedLead_of_approach
      (N := N) (Nat.le_of_lt hactionData.1)

/-- The runway residual is physically impossible when the old reflector's
support is grooved at the beginning of the continuation.

The first write of the old action switch leaves through `R.mouth`.  Endpoint
groove preservation implies that the old runway is still grooved immediately
after that write, so the train must retrace it pointwise and return to the
literal continuation start port `e`.  Switch simplicity forces the first
changed contact to occur no later than that return: otherwise writer `e / 3`
would occur at both time zero and the return time.  But
`exists_later_productive` places a productive event strictly between the
action write and the contact, while a pointwise runway retrace has constant
tongues throughout that whole interval. -/
theorem PartialSecondRunSharp.ChangedContact.RunwayNAddFourResidual.impossible
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    {C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R)}
    (F : C.RunwayNAddFourResidual (N := N) R)
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState) : False := by
  let start : Nat × Tongues :=
    (e, (ManufacturedReflector.flip R).activatedState)
  obtain ⟨actionTime, laterTime, hactionTime, hwriter,
      hactionLater, hlaterContact, hlaterProd⟩ :=
    F.exists_later_productive
  have hactionData := mem_rawFirstWriterTimes_iff.mp hactionTime
  have hactionProd : RawProductiveAt w N start actionTime := by
    simpa [start] using hactionData.2.1
  obtain ⟨cur, next, writerSwitch, hwriterDef, hcur, hnext,
      hstep, hexit, _hflip⟩ :=
    rawProductiveAt_is_endpoint_pivot hactionProd
  have hwriterSwitch : writerSwitch = R.actionSwitch := by
    exact hwriterDef.trans (by simpa [start] using hwriter)
  subst writerSwitch
  have hmouth : 3 * R.actionSwitch = R.mouth := by
    unfold ManufacturedFlipReflector.actionSwitch
    have hstem := R.mouth_is_stem
    omega
  have hparts := step_some_parts hstep
  have hactionArrive :
      arrive cur.2 cur.1 = (R.mouth, next.2) := by
    calc
      arrive cur.2 cur.1 = (exitPort cur, next.2) := by
        apply Prod.ext
        · rfl
        · exact hparts.2.symm
      _ = (R.mouth, next.2) := by
        rw [hexit, hwriterSwitch, hmouth]
  let contactSpan := C.approach.length - (actionTime + 1)
  have hcontactSum :
      actionTime + 1 + contactSpan = C.approach.length := by
    dsimp [contactSpan]
    omega
  have hcontactReach :
      stepN w (actionTime + 1 + contactSpan) start =
        some (C.p, C.contactState) := by
    rw [hcontactSum]
    simpa [start] using C.approach_trace.sound
  have hpostRunwayGrooved : PassagesGrooved next.2 R.runway := by
    intro passage hpassage
    have hcontactGroove :
        arrive C.contactState passage.2 =
          (passage.1, C.contactState) :=
      C.old_grooves R.runway (by
        change R.runway ∈ [R.runway, R.candy]
        exact List.mem_cons_self) passage hpassage
    have hexitSwitch :
        passage.2 / 3 = passageSwitch passage := by
      have hs := arrive_exit_switch C.contactState passage.2
      rw [hcontactGroove] at hs
      simpa [passageSwitch] using hs.symm
    have hmemReusable : passageSwitch passage ∈
        (ManufacturedReflector.flip R).reusableSwitches := by
      change passageSwitch passage ∈
        (R.runway ++ R.candy).map passageSwitch
      apply List.mem_map.mpr
      exact ⟨passage, List.mem_append_left _ hpassage, rfl⟩
    have hswitchLt : passageSwitch passage < N :=
      (ManufacturedReflector.flip R).reusableSwitch_lt
        hN hmemReusable
    have hbit :
        next.2 (passageSwitch passage) =
          C.contactState (passageSwitch passage) := by
      apply Classical.byContradiction
      intro hne
      have hcontactNe :
          C.contactState (passageSwitch passage) ≠
            next.2 (passageSwitch passage) := by
        intro heq
        exact hne heq.symm
      have hchange :
          (tonguesAt w start
              (actionTime + 1 + contactSpan))
                (passageSwitch passage) ≠
            (tonguesAt w start (actionTime + 1))
                (passageSwitch passage) := by
        simpa [tonguesAt, hcontactReach, hnext] using hcontactNe
      obtain ⟨t, htLeft, htRight, htProd, htWriter⟩ :=
        changed_coordinate_has_writer_between
          hswitchLt hcontactReach hchange
      have htBound : t < C.approach.length := by
        rw [hcontactSum] at htRight
        exact htRight
      have hnotReusable :=
        PhysicalTrace.productive_writer_not_old_reusable (ManufacturedReflector.flip R) C.approach_trace
          C.approach_simple hA C.old_grooves htBound htProd
      apply hnotReusable
      rw [htWriter]
      exact hmemReusable
    apply groove_transfer hcontactGroove
    rw [hexitSwitch]
    exact hbit
  have hpointwise :=
    (physicalTrace_contact_retraces_prefix_pointwise
      R.runwayTrace hpostRunwayGrooved R.entryEdge hactionArrive).2
  have hbackTrace := physicalTrace_contact_retraces_prefix
    R.runwayTrace hpostRunwayGrooved R.entryEdge hactionArrive
  let runwaySpan := R.runway.length + 1
  have hbackSound :
      stepN w runwaySpan (cur.1, cur.2) = some (e, next.2) := by
    simpa [runwaySpan, reversePassages_length, Nat.add_comm] using
      hbackTrace.sound
  let returnTime := actionTime + runwaySpan
  have hreturn :
      stepN w returnTime start = some (e, next.2) := by
    dsimp [returnTime]
    rw [stepN_add, hcur]
    exact hbackSound
  have hcontactByReturn : C.approach.length ≤ returnTime := by
    apply Nat.le_of_not_gt
    intro hinside
    exact C.approach_trace.no_strict_return_to_start_port
      C.approach_simple (k := returnTime) (returned := next.2)
        (by dsimp [returnTime, runwaySpan]; omega)
        hinside (by simpa [start] using hreturn)
  have hlaterOutside := productive_not_inside_pointwise_retrace
    (N := N) (repeatTime := actionTime) (span := runwaySpan)
    (openTime := laterTime) (start := start)
    (old := cur.2) (settled := next.2) (q := cur.1)
    hcur (by simpa [runwaySpan] using hpointwise)
    (by simpa [start] using hlaterProd) hactionLater
  dsimp [returnTime] at hcontactByReturn
  omega

/-- **Unconditional changed-contact `N+4` theorem.**  The only residual of
the coefficient-one accounting is excluded by the physical old-runway
retrace above. -/
theorem PartialSecondRunSharp.ChangedContact.changed_all_run_distinct_le_N_add_four
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).baseState))).Nodup) :
    times.length <= N + 4 := by
  rcases C.changed_N_add_four_or_runway_residual
      hN hA times hlive hnd with hbound | hresidual
  · exact hbound
  · obtain ⟨F⟩ := hresidual
    exact (F.impossible hN hA).elim

end GeneralN
