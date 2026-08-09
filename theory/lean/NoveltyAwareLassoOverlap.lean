import NoveltyAwareLasso

/-!
# Overlap-aware novelty lasso

Two manufactured construction histories and a subsequent bounded lasso share
their boundary vectors.  The activated state of the first reflector is the
base state of the second, and the activated state of the second is time zero
of the lasso.  Erasing one copy at each boundary saves two vectors.
-/

namespace GeneralN

private theorem overlap_zero_novelty_cover_of_mem
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (times : List Nat) (history : List (List Bool))
    (hmem : ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈ history) :
    NoveltyCoverOn w N start times history 0 := by
  refine ⟨[], by simp, ?_⟩
  intro k hk
  simpa using hmem k hk

/-- **Generic overlap-aware lasso count.**  If the suffix lasso has cap
`cap`, two exact manufactured construction journeys followed by that suffix
expose at most `2*N + cap + 2` pairwise-distinct tongue vectors. -/
theorem two_manufacturing_journeys_then_lasso_distinct_le_overlap
    {w : Wiring} {N e cap : Nat}
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
    (hlocal : EventuallyPeriodicWithin w (start.1, stateB) cap)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + cap + 2 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let secondTravel := B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let firstHistory := A.sharpConstructionHistory N
  let secondHistory := B.sharpConstructionHistory N
  let tailHistory := hlocal.tongueHistory N
  let aBoundary := VectorCount.restrict N stateA
  let bBoundary := VectorCount.restrict N stateB
  let secondReduced := secondHistory.erase aBoundary
  let tailReduced := tailHistory.erase bBoundary
  let history := (firstHistory ++ secondReduced) ++ tailReduced
  have hgroovesAActivated :
      PathGrooves A.toSupported.paths A.activatedState := by
    rw [← hactivatedA]
    exact hgroovesA
  have hgroovesBActivated :
      PathGrooves B.toSupported.paths B.activatedState := by
    rw [← hactivatedB]
    exact hgroovesB
  have hreachTotal : stepN w totalTravel start =
      some (start.1, stateB) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachB
  have hAFirst : aBoundary ∈ firstHistory := by
    dsimp [aBoundary, firstHistory]
    simp [ManufacturedReflector.sharpConstructionHistory, hactivatedA]
  have hASecond : aBoundary ∈ secondHistory := by
    dsimp [aBoundary, secondHistory]
    unfold ManufacturedReflector.sharpConstructionHistory
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨0, List.mem_range.mpr (by omega), ?_⟩
    simp [restrictedTonguesAt, tonguesAt, stepN, hbaseB]
  have hBSecond : bBoundary ∈ secondHistory := by
    dsimp [bBoundary, secondHistory]
    simp [ManufacturedReflector.sharpConstructionHistory, hactivatedB]
  have hBCombined : bBoundary ∈ firstHistory ++ secondReduced := by
    by_cases hBA : bBoundary = aBoundary
    · rw [hBA]
      exact List.mem_append_left _ hAFirst
    · apply List.mem_append_right firstHistory
      exact (List.mem_erase_of_ne hBA).mpr hBSecond
  have hBTail : bBoundary ∈ tailHistory := by
    have hm := hlocal.mem_tongueHistory (N := N) (k := 0)
    have hzero :
        restrictedTonguesAt w N (start.1, stateB) 0 = bBoundary := by
      dsimp [bBoundary]
      simp [restrictedTonguesAt, tonguesAt, stepN]
    rw [← hzero]
    simpa [tailHistory] using hm
  have hmem : ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈ history := by
    intro k hk
    by_cases hfirst : k ≤ firstTravel
    · apply List.mem_append_left tailReduced
      apply List.mem_append_left secondReduced
      dsimp [firstHistory]
      have hm := A.manufacturing_journey_mem_sharpHistory
        (N := N) hgroovesAActivated (j := k)
          (by simpa [firstTravel] using hfirst)
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
          (N := N) hgroovesBActivated (j := d)
            (by simpa [secondTravel] using hdLe)
        have hm' : restrictedTonguesAt w N (e, stateA) d ∈
            secondHistory := by
          simpa [secondHistory, hbaseB] using hm
        have heq : restrictedTonguesAt w N start k =
            restrictedTonguesAt w N (e, stateA) d := by
          unfold restrictedTonguesAt
          rw [hkEq]
          exact congrArg (VectorCount.restrict N) hshift
        rw [heq]
        by_cases ha :
            restrictedTonguesAt w N (e, stateA) d = aBoundary
        · rw [ha]
          apply List.mem_append_left tailReduced
          exact List.mem_append_left secondReduced hAFirst
        · apply List.mem_append_left tailReduced
          apply List.mem_append_right firstHistory
          exact (List.mem_erase_of_ne ha).mpr hm'
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
                rw [hkEq, stepN_add, hreachTotal]
                simp [hd]
              rw [hnone] at hkLive
              simp at hkLive
          | some finish => exact ⟨finish, rfl⟩
        have hshift := tonguesAt_add_of_reaches hreachTotal hlocalLive
        have hm := hlocal.mem_tongueHistory (N := N) (k := d)
        have hm' : restrictedTonguesAt w N (start.1, stateB) d ∈
            tailHistory := by
          simpa [tailHistory] using hm
        have heq : restrictedTonguesAt w N start k =
            restrictedTonguesAt w N (start.1, stateB) d := by
          unfold restrictedTonguesAt
          rw [hkEq]
          exact congrArg (VectorCount.restrict N) hshift
        rw [heq]
        by_cases hb :
            restrictedTonguesAt w N (start.1, stateB) d = bBoundary
        · rw [hb]
          exact List.mem_append_left tailReduced hBCombined
        · apply List.mem_append_right (firstHistory ++ secondReduced)
          exact (List.mem_erase_of_ne hb).mpr hm'
  have hcover := overlap_zero_novelty_cover_of_mem times history hmem
  have hcountRaw := noveltyCoverOn_distinct_count hcover hnd
  have hcount : times.length ≤ history.length := by
    simpa using hcountRaw
  have hfirstLen : firstHistory.length ≤ N + 2 := by
    dsimp [firstHistory]
    exact A.sharpConstructionHistory_length hN
  have hsecondLen : secondHistory.length ≤ N + 2 := by
    dsimp [secondHistory]
    exact B.sharpConstructionHistory_length hN
  have htailLen : tailHistory.length = cap := by
    simp [tailHistory, EventuallyPeriodicWithin.tongueHistory]
  have hsecondReducedLen :
      secondReduced.length = secondHistory.length - 1 := by
    dsimp [secondReduced]
    exact List.length_erase_of_mem hASecond
  have htailReducedLen :
      tailReduced.length = tailHistory.length - 1 := by
    dsimp [tailReduced]
    exact List.length_erase_of_mem hBTail
  have htailPositive : 0 < cap := by
    obtain ⟨lead, period, settled, hperiodPos, hcap, _hlead, _hperiod⟩ :=
      hlocal
    omega
  have hhistoryLen : history.length ≤ 2 * N + cap + 2 := by
    dsimp [history]
    simp only [List.length_append]
    omega
  exact Nat.le_trans hcount hhistoryLen

/-- The original `22*N` repair-lasso corollary. -/
theorem two_manufacturing_journeys_then_repair_distinct_le_overlap
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
    times.length ≤ 24 * N + 2 := by
  have h := two_manufacturing_journeys_then_lasso_distinct_le_overlap
    hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
    hbaseB hactivatedB hreachB hgroovesB hlocal times hlive hnd
  omega

end GeneralN
