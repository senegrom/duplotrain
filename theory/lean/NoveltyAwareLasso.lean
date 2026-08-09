import FirstActivatedExact
import SharpStateLawAssembly

/-! Novelty-aware assembly of two construction journeys and a repair lasso. -/

namespace GeneralN

/-- The complete lasso window, represented as restricted tongue vectors. -/
def EventuallyPeriodicWithin.tongueHistory
    {w : Wiring} (h : EventuallyPeriodicWithin w start cap)
    (N : Nat) : List (List Bool) :=
  (List.range cap).map (restrictedTonguesAt w N start)

/-- Every local time is represented in the bounded lasso tongue history. -/
theorem EventuallyPeriodicWithin.mem_tongueHistory
    {w : Wiring} {start : Nat × Tongues} {cap N k : Nat}
    (h : EventuallyPeriodicWithin w start cap) :
    restrictedTonguesAt w N start k ∈ h.tongueHistory N := by
  obtain ⟨r, hr, heq⟩ := h.reduce_time (k := k)
  unfold EventuallyPeriodicWithin.tongueHistory
  apply List.mem_map.mpr
  refine ⟨r, List.mem_range.mpr hr, ?_⟩
  simp [restrictedTonguesAt, tonguesAt, heq]

private theorem zero_novelty_cover_of_mem
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (times : List Nat) (history : List (List Bool))
    (hmem : ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈ history) :
    NoveltyCoverOn w N start times history 0 := by
  refine ⟨[], by simp, ?_⟩
  intro k hk
  simpa using hmem k hk

/-- Two exact manufactured journeys followed by a bounded local lasso expose
at most `24*N+4` pairwise-distinct tongue vectors. -/
theorem two_manufacturing_journeys_then_repair_distinct_le
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (A : ManufacturedReflector w start.1 e)
    (B : ManufacturedReflector w e start.1)
    (stateA stateB : Tongues)
    (hbaseA : A.baseState = start.2)
    (hactivatedA : stateA = A.activatedState)
    (hreachA : stepN w
      (A.exploration.length + A.runway.length + 1) start =
        some (e, stateA))
    (hgroovesA : PathGrooves A.toSupported.paths stateA)
    (hbaseB : B.baseState = stateA)
    (hactivatedB : stateB = B.activatedState)
    (hreachB : stepN w
      (B.exploration.length + B.runway.length + 1) (e, stateA) =
        some (start.1, stateB))
    (hgroovesB : PathGrooves B.toSupported.paths stateB)
    (hlocal : EventuallyPeriodicWithin w (start.1, stateB) (22 * N))
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 24 * N + 4 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let secondTravel := B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let firstHistory := A.sharpConstructionHistory N
  let secondHistory := B.sharpConstructionHistory N
  let tailHistory := hlocal.tongueHistory N
  let history := (firstHistory ++ secondHistory) ++ tailHistory
  have hreachTotal : stepN w totalTravel start =
      some (start.1, stateB) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachB
  have hmem : ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈ history := by
    intro k hk
    by_cases hfirst : k ≤ firstTravel
    · apply List.mem_append_left tailHistory
      apply List.mem_append_left secondHistory
      dsimp [firstHistory]
      have hm := A.manufacturing_journey_mem_sharpHistory
        hgroovesA (j := k) (by simpa [firstTravel] using hfirst)
      simpa [hbaseA] using hm
    · by_cases hsecond : k ≤ totalTravel
      · let d := k - firstTravel
        have hkEq : k = firstTravel + d := by
          dsimp [d]
          omega
        have hdLe : d ≤ secondTravel := by
          dsimp [totalTravel] at hsecond
          dsimp [d]
          omega
        have hliveD := stepN_prefix_some hdLe hreachB
        have hshift := tonguesAt_add_of_reaches hreachA hliveD
        have hm := B.manufacturing_journey_mem_sharpHistory
          hgroovesB (j := d) (by simpa [secondTravel] using hdLe)
        apply List.mem_append_left tailHistory
        apply List.mem_append_right firstHistory
        have heq : restrictedTonguesAt w N start k =
            restrictedTonguesAt w N (e, stateA) d := by
          unfold restrictedTonguesAt
          rw [hkEq]
          exact congrArg (VectorCount.restrict N) hshift
        rw [heq]
        simpa [hbaseB] using hm
      · let d := k - totalTravel
        have hkEq : k = totalTravel + d := by
          dsimp [d]
          omega
        have hkLive := hlive k hk
        have hlocalLive : ∃ finish,
            stepN w d (start.1, stateB) = some finish := by
          cases hd : stepN w d (start.1, stateB) with
          | none =>
              have hnone : stepN w k start = none := by
                rw [hkEq, stepN_add, hreachTotal, hd]
              rw [hnone] at hkLive
              simp at hkLive
          | some finish => exact ⟨finish, rfl⟩
        have hshift := tonguesAt_add_of_reaches hreachTotal hlocalLive
        apply List.mem_append_right (firstHistory ++ secondHistory)
        have hm := hlocal.mem_tongueHistory (N := N) (k := d)
        have heq : restrictedTonguesAt w N start k =
            restrictedTonguesAt w N (start.1, stateB) d := by
          unfold restrictedTonguesAt
          rw [hkEq]
          exact congrArg (VectorCount.restrict N) hshift
        rw [heq]
        exact hm
  have hcover := zero_novelty_cover_of_mem times history hmem
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hfirstLen := A.sharpConstructionHistory_length hN
  have hsecondLen := B.sharpConstructionHistory_length hN
  have htailLen : tailHistory.length = 22 * N := by
    simp [tailHistory, EventuallyPeriodicWithin.tongueHistory]
  dsimp [history] at hcount
  simp only [List.length_append] at hcount
  dsimp [firstHistory, secondHistory, tailHistory] at hcount
  omega

end GeneralN
