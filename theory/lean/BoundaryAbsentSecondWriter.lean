import StateLawCoefficientOneTop

/-!
# The productive initial coordinate is absent from the second writer history

This file isolates one coefficient-one accounting step.  The first
reflector `A` has a list of reusable support coordinates; the second
reflector `B` has a list of coordinates at which its switch-simple
construction performs a productive first write.  If the productive initial
coordinate `k0` belongs to neither list, then it is a genuinely reserved
coordinate.  Adjoining it to the existing disjoint-coordinate certificate
saves one state in the combined construction history.

The final theorem packages the form needed by the arbitrary-start boundary
argument: once the first-reflector analysis says that the original vector is
already represented or `k0` is absent from the reusable support, absence
from the second writer list gives exactly the desired absorbed-or-one-saved
dichotomy.
-/

namespace GeneralN

/-- Switch coordinates of the productive first writers in a manufactured
reflector's switch-simple construction. -/
def ManufacturedReflector.constructionFirstWriterSwitches
    {w : Wiring} {g e : Nat}
    (B : ManufacturedReflector w g e) (N : Nat) : List Nat :=
  (rawFirstWriterTimes w N (g, B.baseState)
      B.exploration.length).map
    (rawWriterAt w (g, B.baseState))

/-- Reserving `k0` outside both the old reusable support and the second
construction's productive first writers strengthens the coefficient-one
coordinate charge by exactly one. -/
theorem ManufacturedReflector.reusable_add_second_first_writers_add_reserved_le
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (hk0 : k0 < N)
    (habsentA : Not (List.Mem k0 A.reusableSwitches))
    (habsentB : Not (List.Mem k0
      (B.constructionFirstWriterSwitches N))) :
    A.reusableSwitches.length +
        (rawFirstWriterTimes w N (e, B.baseState)
          B.exploration.length).length + 1 <= N := by
  classical
  let times :=
    rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length
  let writers := times.map (rawWriterAt w (e, B.baseState))
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
      forall oldSwitch, List.Mem oldSwitch A.reusableSwitches ->
        forall freshSwitch, List.Mem freshSwitch writers ->
          Ne oldSwitch freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
    have hkData := mem_rawFirstWriterTimes_iff.mp (by
      simpa [times] using hk)
    have houtside :=
      A.second_exploration_productive_writer_not_reusable B hbaseGrooves hpreGrooves
          hkData.1 hkData.2.1
    apply houtside
    rw [← hEq]
    exact hOld
  let occupied := A.reusableSwitches ++ writers
  have hoccupiedNodup : occupied.Nodup := by
    dsimp [occupied]
    exact List.nodup_append.mpr
      ⟨A.reusableSwitches_nodup, hwritersNodup, hdisjoint⟩
  have hk0NotOccupied : Not (List.Mem k0 occupied) := by
    intro hk
    rcases List.mem_append.mp hk with hOld | hFresh
    · exact habsentA hOld
    · apply habsentB
      dsimp [ManufacturedReflector.constructionFirstWriterSwitches,
        writers, times]
      exact hFresh
  have hallNodup : (k0 :: occupied).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hk0NotOccupied, hoccupiedNodup⟩
  have hallLt : forall C, List.Mem C (k0 :: occupied) -> C < N := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · exact hk0
    · rcases List.mem_append.mp hC with hOld | hFresh
      · exact A.reusableSwitch_lt hN hOld
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
        have hkData := mem_rawFirstWriterTimes_iff.mp (by
          simpa [times] using hk)
        exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hallNodup hallLt
  have hlength :
      (k0 :: occupied).length =
        A.reusableSwitches.length + times.length + 1 := by
    simp [occupied, writers]
  rw [hlength] at hbound
  simpa [times] using hbound

/-- Two distinct switches outside both the old reusable support and the
second construction's productive first writers buy two units in the same
coordinate charge. -/
theorem ManufacturedReflector.reusable_add_second_first_writers_add_two_reserved_le
    {w : Wiring} {N g e r1 r2 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves A.toSupported.paths B.preReturn.2)
    (hr1 : r1 < N) (hr2 : r2 < N) (hne : r1 ≠ r2)
    (habsentA1 : r1 ∉ A.reusableSwitches)
    (habsentB1 : r1 ∉ B.constructionFirstWriterSwitches N)
    (habsentA2 : r2 ∉ A.reusableSwitches)
    (habsentB2 : r2 ∉ B.constructionFirstWriterSwitches N) :
    A.reusableSwitches.length +
        (rawFirstWriterTimes w N (e, B.baseState)
          B.exploration.length).length + 2 ≤ N := by
  classical
  let times := rawFirstWriterTimes w N (e, B.baseState)
    B.exploration.length
  let writers := times.map (rawWriterAt w (e, B.baseState))
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
  have hdisjoint : forall oldSwitch, oldSwitch ∈ A.reusableSwitches ->
      forall freshSwitch, freshSwitch ∈ writers ->
        oldSwitch ≠ freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
    have hkData := mem_rawFirstWriterTimes_iff.mp (by
      simpa [times] using hk)
    have houtside := A.second_exploration_productive_writer_not_reusable B hbaseGrooves hpreGrooves hkData.1 hkData.2.1
    apply houtside
    rw [← hEq]
    exact hOld
  let occupied := A.reusableSwitches ++ writers
  have hoccupiedNodup : occupied.Nodup := by
    dsimp [occupied]
    exact List.nodup_append.mpr
      ⟨A.reusableSwitches_nodup, hwritersNodup, hdisjoint⟩
  have hr1Not : r1 ∉ occupied := by
    intro hm
    rcases List.mem_append.mp hm with hOld | hFresh
    · exact habsentA1 hOld
    · apply habsentB1
      dsimp [ManufacturedReflector.constructionFirstWriterSwitches,
        writers, times]
      exact hFresh
  have hr2Not : r2 ∉ occupied := by
    intro hm
    rcases List.mem_append.mp hm with hOld | hFresh
    · exact habsentA2 hOld
    · apply habsentB2
      dsimp [ManufacturedReflector.constructionFirstWriterSwitches,
        writers, times]
      exact hFresh
  have hallNodup : (r1 :: r2 :: occupied).Nodup := by
    simp only [List.nodup_cons]
    exact ⟨by
      intro hm
      rcases List.mem_cons.mp hm with heq | hm
      · exact hne heq
      · exact hr1Not hm,
      hr2Not, hoccupiedNodup⟩
  have hallLt : forall C, C ∈ (r1 :: r2 :: occupied) -> C < N := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · exact hr1
    · rcases List.mem_cons.mp hC with rfl | hC
      · exact hr2
      · rcases List.mem_append.mp hC with hOld | hFresh
        · exact A.reusableSwitch_lt hN hOld
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
          have hkData := mem_rawFirstWriterTimes_iff.mp (by
            simpa [times] using hk)
          exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hallNodup hallLt
  have hlength : (r1 :: r2 :: occupied).length =
      A.reusableSwitches.length + times.length + 2 := by
    simp [occupied, writers]
  rw [hlength] at hbound
  simpa [times] using hbound

/-- The reserved coordinate lowers the two-construction core from `N+3` to
`N+2`.  This is the one-state saving needed to adjoin the original boundary
vector without exceeding the old `N+3` construction budget. -/
theorem ManufacturedReflector.preservedTwoHistoryCore_length_le_N_add_two_of_reserved
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (hk0 : k0 < N)
    (habsentA : Not (List.Mem k0 A.reusableSwitches))
    (habsentB : Not (List.Mem k0
      (B.constructionFirstWriterSwitches N))) :
    (A.preservedTwoHistoryCore B N).length <= N + 2 := by
  have hboundary :
      VectorCount.restrict N A.activatedState ∈
        B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge :=
    A.reusable_add_second_first_writers_add_reserved_le
      hN B hbaseGrooves hpreGrooves hk0 habsentA habsentB
  have houter := A.exploration_length_le_reusable_add_one
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

/-- Two reserved coordinates lower the complete two-construction core to
`N + 1`.  After adjoining the arbitrary pre-passage vector this leaves an
`N + 2` history, exactly enough for a generic two-vector protected tail. -/
theorem ManufacturedReflector.preservedTwoHistoryCore_length_le_N_add_one_of_two_reserved
    {w : Wiring} {N g e r1 r2 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves A.toSupported.paths B.preReturn.2)
    (hr1 : r1 < N) (hr2 : r2 < N) (hne : r1 ≠ r2)
    (habsentA1 : r1 ∉ A.reusableSwitches)
    (habsentB1 : r1 ∉ B.constructionFirstWriterSwitches N)
    (habsentA2 : r2 ∉ A.reusableSwitches)
    (habsentB2 : r2 ∉ B.constructionFirstWriterSwitches N) :
    (A.preservedTwoHistoryCore B N).length ≤ N + 1 := by
  have hboundary : VectorCount.restrict N A.activatedState ∈
      B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge :=
    A.reusable_add_second_first_writers_add_two_reserved_le
      hN B hbaseGrooves hpreGrooves hr1 hr2 hne
        habsentA1 habsentB1 habsentA2 habsentB2
  have houter := A.exploration_length_le_reusable_add_one
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

end GeneralN
