import TwoHistoryUnionCharge

/-!
# One-reflector continuation at coefficient one

This file treats two genuine branches after exactly one manufactured
reflector has been completed.

* A support-preserving switch-simple continuation that falls off on its next
  raw step exposes at most `N+2` restricted tongue vectors.
* A support-preserving switch-simple lead followed by a one-vector cycle tail
  exposes at most `N+3` vectors.

Both statements use one joint coordinate charge: old reusable support
switches and productive first writers of the continuation fit together in
the same set of `N` switch coordinates.
-/

namespace GeneralN

/-- A productive passage in a switch-simple continuation cannot write an old
reusable coordinate when the old support is grooved at both endpoints. -/
theorem PhysicalTrace.productive_writer_not_old_reusable
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PathGrooves A.toSupported.paths start.2)
    (hend : PathGrooves A.toSupported.paths finish.2)
    {k : Nat} (hk : k < passages.length)
    (hprod : RawProductiveAt w N start k) :
    rawWriterAt w start k ∉ A.reusableSwitches := by
  intro hreusable
  have hsurvives :=
    htrace.simple_raw_productive_writer_survives
      hsimple hk hprod
  obtain ⟨path, hpath, old, hold, hswitch⟩ :=
    A.mem_reusableSwitches hreusable
  have hbaseOld := hbase path hpath old hold
  have hendOld := hend path hpath old hold
  have hagree := grooved_states_agree_on_passage hbaseOld hendOld
  have hexit : old.2 / 3 = passageSwitch old := by
    have hs := arrive_exit_switch start.2 old.2
    rw [hbaseOld] at hs
    exact hs.symm
  apply hsurvives
  calc
    finish.2 (rawWriterAt w start k) =
        finish.2 (old.2 / 3) := by rw [hexit, hswitch]
    _ = start.2 (old.2 / 3) := hagree.symm
    _ = start.2 (rawWriterAt w start k) := by rw [hexit, hswitch]

/-- The old reusable coordinates and the first productive writers of a
support-preserving simple continuation share one ambient switch budget. -/
theorem ManufacturedReflector.reusable_add_continuation_first_writers_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PathGrooves A.toSupported.paths start.2)
    (hend : PathGrooves A.toSupported.paths finish.2) :
    A.reusableSwitches.length +
      (rawFirstWriterTimes w N start passages.length).length ≤ N := by
  let times := rawFirstWriterTimes w N start passages.length
  let writers := times.map (rawWriterAt w start)
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
      ∀ oldSwitch ∈ A.reusableSwitches,
        ∀ freshSwitch ∈ writers, oldSwitch ≠ freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
    have hkData := mem_rawFirstWriterTimes_iff.mp (by
      simpa [times] using hk)
    have houtside :=
      htrace.productive_writer_not_old_reusable A hsimple hbase hend hkData.1 hkData.2.1
    apply houtside
    rw [← hEq]
    exact hOld
  let switches := A.reusableSwitches ++ writers
  have hnd : switches.Nodup := by
    dsimp [switches]
    exact List.nodup_append.mpr
      ⟨A.reusableSwitches_nodup, hwritersNodup, hdisjoint⟩
  have hlt : ∀ C ∈ switches, C < N := by
    intro C hC
    rcases List.mem_append.mp hC with hOld | hFresh
    · exact A.reusableSwitch_lt hN hOld
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
      have hkData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hk)
      exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hnd hlt
  have hlength :
      A.reusableSwitches.length + times.length ≤ N := by
    simpa [switches, writers] using hbound
  simpa [times] using hlength

/-- Compressed history for one completed reflector and a subsequent
support-preserving switch-simple continuation. -/
def ManufacturedReflector.continuationHistory
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (N : Nat) (start : Nat × Tongues) (length : Nat) :
    List (List Bool) :=
  A.sharpHistoryCore N ++
    (rawFirstWriterHistory w N start length).erase
      (VectorCount.restrict N A.activatedState)

/-- The combined first-reflector/continuation history has size at most
`N+2`. -/
theorem ManufacturedReflector.continuationHistory_length_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (hstart : start.2 = A.activatedState)
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PathGrooves A.toSupported.paths start.2)
    (hend : PathGrooves A.toSupported.paths finish.2) :
    (A.continuationHistory N start passages.length).length ≤ N + 2 := by
  have hboundary : VectorCount.restrict N A.activatedState ∈
      rawFirstWriterHistory w N start passages.length := by
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hstart]
  have hcharge :=
    A.reusable_add_continuation_first_writers_le
      hN htrace hsimple hbase hend
  have houter := A.exploration_length_le_reusable_add_one
  unfold ManufacturedReflector.continuationHistory
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length]
  simp [rawFirstWriterHistory]
  omega

/-- Every state of the simple continuation belongs to its compressed
coefficient-one history. -/
theorem ManufacturedReflector.mem_continuationHistory
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    {d : Nat} (hd : d ≤ passages.length) :
    restrictedTonguesAt w N start d ∈
      A.continuationHistory N start passages.length := by
  have hm := htrace.restrictedTonguesAt_mem_rawFirstWriterHistory
    (N := N) hsimple d hd
  by_cases hboundary : restrictedTonguesAt w N start d =
      VectorCount.restrict N A.activatedState
  · apply List.mem_append_left
    rw [hboundary]
    exact A.activated_mem_sharpHistoryCore
  · apply List.mem_append_right
    exact (List.mem_erase_of_ne hboundary).mpr hm

/-- Pointwise absolute coverage through the first manufactured journey and
the following simple continuation. -/
theorem ManufacturedReflector.journey_then_continuation_mem
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, A.activatedState) passages finish)
    (hsimple : SwitchSimple passages)
    {k : Nat}
    (hk : k ≤ A.exploration.length + A.runway.length + 1 +
      passages.length) :
    restrictedTonguesAt w N (g, A.baseState) k ∈
      A.continuationHistory N
        (e, A.activatedState) passages.length := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localStart : Nat × Tongues := (e, A.activatedState)
  have hreachA : stepN w firstTravel (g, A.baseState) =
      some localStart := by
    simpa [firstTravel, localStart] using
      A.manufacturing_journey_reaches_activated hA
  by_cases hfirst : k ≤ firstTravel
  · apply List.mem_append_left
    apply A.mem_sharpHistoryCore_of_mem
    exact A.manufacturing_journey_mem_sharpHistory hA (by
      simpa [firstTravel] using hfirst)
  · let d := k - firstTravel
    have hkEq : k = firstTravel + d := by
      dsimp [d]
      omega
    have hd : d ≤ passages.length := by
      dsimp [d, firstTravel] at hk ⊢
      omega
    have hlocalLive := stepN_prefix_some hd htrace.sound
    have hshift := tonguesAt_add_of_reaches hreachA hlocalLive
    have hvector : restrictedTonguesAt w N
        (g, A.baseState) k =
        restrictedTonguesAt w N localStart d := by
      unfold restrictedTonguesAt
      rw [hkEq]
      exact congrArg (VectorCount.restrict N) hshift
    rw [hvector]
    exact A.mem_continuationHistory
      (N := N) (finish := finish) (passages := passages)
      htrace hsimple hd

/-- A completed reflector followed by a support-preserving simple
continuation which falls off on its next step has at most `N+2` distinct
restricted tongue vectors on the entire raw run. -/
theorem preserved_simple_fall_distinct_le_N_add_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, A.activatedState) passages finish)
    (hsimple : SwitchSimple passages)
    (hend : PathGrooves A.toSupported.paths finish.2)
    (hfall : step w finish = none)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 2 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localStart : Nat × Tongues := (e, A.activatedState)
  let lastLive := firstTravel + passages.length
  let history :=
    A.continuationHistory N localStart passages.length
  have hreachA : stepN w firstTravel (g, A.baseState) =
      some localStart := by
    simpa [firstTravel, localStart] using
      A.manufacturing_journey_reaches_activated hA
  have hlocalDead :
      stepN w (passages.length + 1) localStart = none := by
    rw [stepN_add, htrace.sound]
    simpa [stepN] using hfall
  have hglobalDead :
      stepN w (lastLive + 1) (g, A.baseState) = none := by
    have htime :
        lastLive + 1 = firstTravel + (passages.length + 1) := by
      dsimp [lastLive]
      omega
    rw [htime, stepN_add, hreachA]
    exact hlocalDead
  have htimes : ∀ k ∈ times, k ≤ lastLive := by
    intro k hk
    by_cases hle : k ≤ lastLive
    · exact hle
    · have hdeadAtK :
          stepN w k (g, A.baseState) = none :=
        stepN_none_of_none_at_le hglobalDead (by omega)
      have hkLive := hlive k hk
      rw [hdeadAtK] at hkLive
      simp at hkLive
  have hcover :
      NoveltyCoverOn w N (g, A.baseState) times history 0 := by
    refine ⟨[], by simp, ?_⟩
    intro k hk
    simp only [List.append_nil]
    dsimp [history]
    apply A.journey_then_continuation_mem hA htrace hsimple
    simpa [lastLive, firstTravel] using htimes k hk
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hlength :
      history.length ≤ N + 2 := by
    dsimp [history, localStart]
    exact A.continuationHistory_length_le
      hN rfl htrace hsimple hA hend
  omega

theorem simple_lead_one_vector_tail_distinct_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {atRepeat : Nat × Tongues} {lead : List Passage}
    (hlead : PhysicalTrace w
      (e, A.activatedState) lead atRepeat)
    (hleadSimple : SwitchSimple lead)
    (hend : PathGrooves A.toSupported.paths atRepeat.2)
    {settled : Tongues}
    (htail : ∀ d, 0 < d → ∃ port,
      stepN w d atRepeat = some (port, settled))
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 3 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let shift := firstTravel + lead.length
  let localStart : Nat × Tongues := (e, A.activatedState)
  let history := A.continuationHistory N localStart lead.length
  let settledVector := VectorCount.restrict N settled
  have hreachA : stepN w firstTravel (g, A.baseState) =
      some localStart := by
    simpa [firstTravel, localStart] using
      A.manufacturing_journey_reaches_activated hA
  have hreach : stepN w shift (g, A.baseState) =
      some atRepeat := by
    dsimp [shift]
    rw [stepN_add, hreachA]
    exact hlead.sound
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times (history ++ [settledVector]) 0 := by
    refine ⟨[], by simp, ?_⟩
    intro k _hk
    simp only [List.append_nil]
    by_cases hbefore : k ≤ shift
    · apply List.mem_append_left
      dsimp [history]
      apply A.journey_then_continuation_mem hA hlead hleadSimple
      simpa [shift, firstTravel] using hbefore
    · let d := k - shift
      have hd : 0 < d := by
        dsimp [d]
        omega
      have hkEq : k = shift + d := by
        dsimp [d]
        omega
      obtain ⟨port, hlocal⟩ := htail d hd
      have hglobal : stepN w k (g, A.baseState) =
          some (port, settled) := by
        rw [hkEq, stepN_add, hreach]
        exact hlocal
      have hvector : restrictedTonguesAt w N
          (g, A.baseState) k = settledVector := by
        simp [restrictedTonguesAt, tonguesAt, hglobal, settledVector]
      rw [hvector]
      apply List.mem_append_right
      simp
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistory :
      history.length ≤ N + 2 := by
    dsimp [history, localStart]
    exact A.continuationHistory_length_le
      hN rfl hlead hleadSimple hA hend
  dsimp [settledVector] at hcount
  simp only [List.length_append, List.length_singleton] at hcount
  omega

end GeneralN
