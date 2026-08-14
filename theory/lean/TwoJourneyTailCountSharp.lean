import SharpStateLawAssembly
import ManufacturedPairNovelty
import FirstActivatedExact

/-!
# Two manufacturing journeys followed by a directly counted tail

The physical length of the tail is irrelevant here.  We split selected raw
times at the exact end of the second manufacturing journey.  Earlier samples
are covered by the two canonical construction histories, with their shared
`stateA` boundary erased once.  Later samples are shifted to `stateB` and
passed to an arbitrary tongue-vector counting theorem.
-/

namespace GeneralN

private theorem tailsharp_nodup_of_map_nodup
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

private theorem tailsharp_nodup_map_filter
    {α : Type} [BEq α] [LawfulBEq α]
    {f : Nat → α} (p : Nat → Bool) :
    ∀ {xs : List Nat},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
            apply hnd.1
            exact List.mem_map.mpr
              ⟨y, (List.mem_filter.mp hy).1, hfy⟩
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem tailsharp_lt_ge_partition (L : Nat) :
    ∀ xs : List Nat,
      (xs.filter (fun k => decide (k < L))).length +
        (xs.filter (fun k => decide (L ≤ k))).length = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons k rest ih =>
      by_cases hk : k < L
      · have hnot : ¬ L ≤ k := by omega
        simp [hk, hnot]
        omega
      · have hge : L ≤ k := by omega
        simp [hk, hge]
        omega

private theorem tailsharp_zero_novelty_cover_of_mem
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (times : List Nat) (history : List (List Bool))
    (hmem : ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈ history) :
    NoveltyCoverOn w N start times history 0 := by
  refine ⟨[], by simp, ?_⟩
  intro k hk
  simpa using hmem k hk

/-- Generic direct-tail assembly.  If every distinct live sample list of the
suffix beginning at `stateB` has size at most `tailCap`, then the complete
raw run has at most `2*N+3+tailCap` distinct restricted tongue vectors. -/
theorem two_manufacturing_journeys_then_direct_tail_distinct_le
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
      (tailTimes.map
        (restrictedTonguesAt w N (start.1, stateB))).Nodup →
      tailTimes.length ≤ tailCap)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 3 + tailCap := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let secondTravel := B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let firstHistory := A.sharpConstructionHistory N
  let secondHistory := B.sharpConstructionHistory N
  let aBoundary := VectorCount.restrict N stateA
  let secondReduced := secondHistory.erase aBoundary
  let constructionHistory := firstHistory ++ secondReduced
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
  have hconstructionLen : constructionHistory.length ≤ 2 * N + 3 := by
    dsimp [constructionHistory]
    simp only [List.length_append]
    omega
  have htimesNodup : times.Nodup :=
    tailsharp_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  let preTimes := times.filter (fun k => decide (k < totalTravel))
  let postTimes := times.filter (fun k => decide (totalTravel ≤ k))
  let shifted := postTimes.map (fun k => k - totalTravel)
  have hpreMapNodup :
      (preTimes.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [preTimes]
    exact tailsharp_nodup_map_filter _ hnd
  have hpreMem : ∀ k ∈ preTimes,
      restrictedTonguesAt w N start k ∈ constructionHistory := by
    intro k hk
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkTotal : k < totalTravel :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    by_cases hfirst : k ≤ firstTravel
    · apply List.mem_append_left
      dsimp [firstHistory]
      have hm := A.manufacturing_journey_mem_sharpHistory
        (N := N) hgroovesAActivated (j := k)
          (by simpa [firstTravel] using hfirst)
      simpa [hbaseA] using hm
    · let d := k - firstTravel
      have hkEq : k = firstTravel + d := by
        dsimp [d]
        omega
      have hdLe : d ≤ secondTravel := by
        dsimp [totalTravel] at hkTotal
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
        exact List.mem_append_left _ hAFirst
      · apply List.mem_append_right firstHistory
        exact (List.mem_erase_of_ne ha).mpr hm'
  have hpreCover := tailsharp_zero_novelty_cover_of_mem
    preTimes constructionHistory hpreMem
  have hpreCountRaw := noveltyCoverOn_distinct_count hpreCover hpreMapNodup
  have hpreBound : preTimes.length ≤ 2 * N + 3 := by
    have hpreCount : preTimes.length ≤ constructionHistory.length := by
      simpa using hpreCountRaw
    exact Nat.le_trans hpreCount hconstructionLen
  have hpostMapNodup :
      (postTimes.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [postTimes]
    exact tailsharp_nodup_map_filter _ hnd
  have hshiftVector : shifted.map
      (restrictedTonguesAt w N (start.1, stateB)) =
      postTimes.map (restrictedTonguesAt w N start) := by
    dsimp [shifted]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hkGe : totalTravel ≤ k :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkEq : k = totalTravel + (k - totalTravel) := by omega
    have hkLive := hlive k hkTimes
    have hrun : stepN w k start =
        stepN w (k - totalTravel) (start.1, stateB) := by
      rw [hkEq, stepN_add, hreachTotal]
      simp
    cases htailRun : stepN w (k - totalTravel) (start.1, stateB) with
    | none =>
        rw [hrun, htailRun] at hkLive
        simp at hkLive
    | some finish =>
        have hglobal : stepN w k start = some finish := by
          rw [hrun, htailRun]
        simp [Function.comp_apply, restrictedTonguesAt, tonguesAt,
          hglobal, htailRun]
  have hshiftNodup :
      (shifted.map
        (restrictedTonguesAt w N (start.1, stateB))).Nodup := by
    rw [hshiftVector]
    exact hpostMapNodup
  have hshiftLive : ∀ d ∈ shifted,
      (stepN w d (start.1, stateB)).isSome := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkGe : totalTravel ≤ k :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    have hkEq : k = totalTravel + (k - totalTravel) := by omega
    have hkLive := hlive k hkTimes
    rw [hkEq, stepN_add, hreachTotal] at hkLive
    exact hkLive
  have hshiftBound : shifted.length ≤ tailCap :=
    htail shifted hshiftLive hshiftNodup
  have hpostLength : postTimes.length = shifted.length := by
    simp [shifted]
  have hpartition := tailsharp_lt_ge_partition totalTravel times
  dsimp [preTimes, postTimes] at hpartition hpreBound hpostLength
  omega

end GeneralN
