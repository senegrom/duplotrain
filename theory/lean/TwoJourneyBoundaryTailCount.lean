import BoundaryOverlapTailCount
import NoveltyAwareLassoOverlap

/-!
# Boundary-aware assembly of two manufacturing journeys and a direct tail
-/

namespace GeneralN

/-- Two exact manufacturing journeys followed by a directly counted suffix of
size `tailCap` expose at most `2*N + tailCap + 2` vectors.  Compared with the
older direct-tail assembly this saves the endpoint vector shared by the second
journey and suffix time zero. -/
theorem two_manufacturing_journeys_then_boundary_tail_distinct_le
    {w : Wiring} {N e tailCap : Nat}
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
    (htail : ∀ (tailTimes : List Nat),
      (∀ k ∈ tailTimes,
        (stepN w k (start.1, stateB)).isSome) →
      (tailTimes.map (restrictedTonguesAt w N
        (start.1, stateB))).Nodup →
      tailTimes.length ≤ tailCap)
    (htailPos : 0 < tailCap)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + tailCap + 2 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let secondTravel := B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let firstHistory := A.sharpConstructionHistory N
  let secondHistory := B.sharpConstructionHistory N
  let aBoundary := VectorCount.restrict N stateA
  let bBoundary := VectorCount.restrict N stateB
  let secondReduced := secondHistory.erase aBoundary
  let prefixHistory := firstHistory ++ secondReduced
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
  have hBPrefix : bBoundary ∈ prefixHistory := by
    by_cases hBA : bBoundary = aBoundary
    · rw [hBA]
      exact List.mem_append_left secondReduced hAFirst
    · apply List.mem_append_right firstHistory
      exact (List.mem_erase_of_ne hBA).mpr hBSecond
  have hprefixCover : ∀ d, d ≤ totalTravel →
      restrictedTonguesAt w N start d ∈ prefixHistory := by
    intro d hd
    by_cases hfirst : d ≤ firstTravel
    · apply List.mem_append_left secondReduced
      dsimp [firstHistory]
      have hm := A.manufacturing_journey_mem_sharpHistory
        (N := N) hgroovesAActivated (j := d)
          (by simpa [firstTravel] using hfirst)
      simpa [hbaseA] using hm
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLe : q ≤ secondTravel := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hliveQ := stepN_prefix_some hqLe hreachB
      have hshift := tonguesAt_add_of_reaches hreachA hliveQ
      have hm := B.manufacturing_journey_mem_sharpHistory
        (N := N) hgroovesBActivated (j := q)
          (by simpa [secondTravel] using hqLe)
      have hm' : restrictedTonguesAt w N (e, stateA) q ∈
          secondHistory := by
        simpa [secondHistory, hbaseB] using hm
      have heq : restrictedTonguesAt w N start d =
          restrictedTonguesAt w N (e, stateA) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      by_cases ha :
          restrictedTonguesAt w N (e, stateA) q = aBoundary
      · rw [ha]
        exact List.mem_append_left secondReduced hAFirst
      · apply List.mem_append_right firstHistory
        exact (List.mem_erase_of_ne ha).mpr hm'
  have hboundary :
      VectorCount.restrict N (start.1, stateB).2 ∈ prefixHistory := by
    simpa [bBoundary] using hBPrefix
  have hcount := boundary_history_then_direct_tail_distinct_le
    hreachTotal prefixHistory hprefixCover hboundary htail htailPos
      times hlive hnd
  have hfirstLen : firstHistory.length ≤ N + 2 := by
    dsimp [firstHistory]
    exact A.sharpConstructionHistory_length hN
  have hsecondLen : secondHistory.length ≤ N + 2 := by
    dsimp [secondHistory]
    exact B.sharpConstructionHistory_length hN
  have hsecondReducedLen :
      secondReduced.length = secondHistory.length - 1 := by
    dsimp [secondReduced]
    exact List.length_erase_of_mem hASecond
  have hprefixLen : prefixHistory.length ≤ 2 * N + 3 := by
    dsimp [prefixHistory]
    simp only [List.length_append]
    omega
  omega

end GeneralN
