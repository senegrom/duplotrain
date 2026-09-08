import TwoHistoryUnionCharge

/-!
# Coordinate preservation and continuation after a reflector

A switch-simple trace whose endpoints agree on a groove preserves that
groove throughout. Combine this with construction histories to count a
simple continuation into a stable cycle or another reflector. Dead-end
continuations need no dedicated bound after total-wiring completion.
-/

namespace GeneralN

/-- A switch-simple trace grooved at both endpoints stays grooved at every
intermediate configuration. Each relevant tongue equals an endpoint value,
and the two endpoint values agree because they groove the same passage. -/
theorem PhysicalTrace.pathGrooves_at_prefix_of_endpoints {w : Wiring}
    {start finish middle : Nat × Tongues} {passages : List Passage}
    {paths : List (List Passage)}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PathGrooves paths start.2) (hend : PathGrooves paths finish.2)
    {k : Nat} (hk : k ≤ passages.length)
    (hrun : stepN w k start = some middle) : PathGrooves paths middle.2 := by
  intro path hpath passage hpassage
  have hg0 := hbase path hpath passage hpassage
  have hg1 := hend path hpath passage hpassage
  apply groove_transfer hg1
  rcases htrace.prefix_coordinate_eq_endpoint hsimple hk hrun (passage.2 / 3)
      with h | h
  · exact h.trans (grooved_states_agree_on_passage hg0 hg1)
  · exact h

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
    rw [hkEq, restrictedTonguesAt_add_of_reaches hreachA
      (stepN_prefix_some hd htrace.sound)]
    exact A.mem_continuationHistory
      (N := N) (finish := finish) (passages := passages)
      htrace hsimple hd

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
  have hreach : stepN w
      (A.exploration.length + A.runway.length + 1 + lead.length)
      (g, A.baseState) = some atRepeat := by
    rw [stepN_add, A.manufacturing_journey_reaches_activated hA]
    exact hlead.sound
  have hcover := history_then_settled_one_novelty (N := N) hreach
    (fun _ hk => A.journey_then_continuation_mem hA hlead hleadSimple hk) htail times
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistory := A.continuationHistory_length_le hN rfl hlead hleadSimple hA hend
  omega

end GeneralN
