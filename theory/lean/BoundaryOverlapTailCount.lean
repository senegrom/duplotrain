import TwoJourneyTailCountSharp

/-!
# Boundary-aware direct-tail counting

A directly counted suffix starts at a vector already present at the end of the
prefix.  Filter later suffix samples equal to that boundary; for all remaining
samples, adjoin suffix time zero and invoke the tail cap.  This saves one
vector exactly compared with naïvely adding the two cardinality bounds.
-/

namespace GeneralN

private theorem bot_nodup_of_map_nodup
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
      exact ⟨fun hx => hnd.1 (List.mem_map.mpr ⟨x, hx, rfl⟩),
        ih hnd.2⟩

private theorem bot_nodup_map_filter
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

/-- Generic boundary-overlap theorem.  `prefixHistory` covers every time up to
and including `lead`; the suffix begins at `endpoint`, whose vector is already
in that history.  A direct suffix cap `cap` then contributes only `cap-1`
additional vectors. -/
theorem boundary_history_then_direct_tail_distinct_le
    {w : Wiring} {N lead cap : Nat}
    {start endpoint : Nat × Tongues}
    (hreach : stepN w lead start = some endpoint)
    (prefixHistory : List (List Bool))
    (hprefixCover : ∀ d, d ≤ lead →
      restrictedTonguesAt w N start d ∈ prefixHistory)
    (hboundary : VectorCount.restrict N endpoint.2 ∈ prefixHistory)
    (htail : ∀ (tailTimes : List Nat),
      (∀ k ∈ tailTimes, (stepN w k endpoint).isSome) →
      (tailTimes.map (restrictedTonguesAt w N endpoint)).Nodup →
      tailTimes.length ≤ cap)
    (hcapPos : 0 < cap)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ prefixHistory.length + cap - 1 := by
  let late := times.filter (fun k => decide (lead < k))
  let shifted := late.map (fun k => k - lead)
  let boundary := VectorCount.restrict N endpoint.2
  let other := shifted.filter (fun d =>
    decide (restrictedTonguesAt w N endpoint d ≠ boundary))
  let otherVectors := other.map (restrictedTonguesAt w N endpoint)
  have hlateVector : shifted.map
      (restrictedTonguesAt w N endpoint) =
      late.map (restrictedTonguesAt w N start) := by
    dsimp [shifted]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkGt : lead < k :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    have hkEq : k = lead + (k - lead) := by omega
    have hkLive := hlive k hkTimes
    cases htailRun : stepN w (k - lead) endpoint with
    | none =>
        have hglobalNone : stepN w k start = none := by
          rw [hkEq, stepN_add, hreach]
          simp [htailRun]
        rw [hglobalNone] at hkLive
        simp at hkLive
    | some finish =>
        have hshift := tonguesAt_add_of_reaches
          hreach ⟨finish, htailRun⟩
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
  have hlateNodup :
      (late.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [late]
    exact bot_nodup_map_filter _ hnd
  have hshiftedNodup :
      (shifted.map (restrictedTonguesAt w N endpoint)).Nodup := by
    rw [hlateVector]
    exact hlateNodup
  have hotherNodup : otherVectors.Nodup := by
    dsimp [otherVectors, other]
    exact bot_nodup_map_filter _ hshiftedNodup
  have hzeroVector : restrictedTonguesAt w N endpoint 0 = boundary := by
    dsimp [boundary]
    simp [restrictedTonguesAt, tonguesAt, stepN]
  have hboundaryNotOther :
      boundary ∉ otherVectors := by
    intro hm
    obtain ⟨d, hd, hEq⟩ := List.mem_map.mp hm
    have hne : restrictedTonguesAt w N endpoint d ≠ boundary :=
      of_decide_eq_true (List.mem_filter.mp hd).2
    exact hne hEq
  have hzeroOtherNodup :
      ((0 :: other).map
        (restrictedTonguesAt w N endpoint)).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    constructor
    · intro hm
      rw [hzeroVector] at hm
      exact hboundaryNotOther hm
    · exact hotherNodup
  have hotherLive : ∀ d ∈ other,
      (stepN w d endpoint).isSome := by
    intro d hd
    have hdShifted := (List.mem_filter.mp hd).1
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hdShifted
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkGt : lead < k :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    have hkEq : k = lead + (k - lead) := by omega
    have hkLive := hlive k hkTimes
    rw [hkEq, stepN_add, hreach] at hkLive
    exact hkLive
  have hzeroOtherLive : ∀ d ∈ 0 :: other,
      (stepN w d endpoint).isSome := by
    intro d hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · simp [stepN]
    · exact hotherLive d hd
  have htailBound : (0 :: other).length ≤ cap :=
    htail (0 :: other) hzeroOtherLive hzeroOtherNodup
  have hotherBound : other.length ≤ cap - 1 := by
    simp only [List.length_cons] at htailBound
    omega
  have hmem : ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈
        prefixHistory ++ otherVectors := by
    intro k hk
    by_cases hpre : k ≤ lead
    · exact List.mem_append_left otherVectors
        (hprefixCover k hpre)
    · have hkGt : lead < k := by omega
      let d := k - lead
      have hkEq : k = lead + d := by
        dsimp [d]
        omega
      have hkLive := hlive k hk
      have htailLive : ∃ finish,
          stepN w d endpoint = some finish := by
        cases hd : stepN w d endpoint with
        | none =>
            have hnone : stepN w k start = none := by
              rw [hkEq, stepN_add, hreach]
              simp [hd]
            rw [hnone] at hkLive
            simp at hkLive
        | some finish => exact ⟨finish, rfl⟩
      have hshift := tonguesAt_add_of_reaches hreach htailLive
      have heq : restrictedTonguesAt w N start k =
          restrictedTonguesAt w N endpoint d := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      by_cases hbd : restrictedTonguesAt w N endpoint d = boundary
      · rw [heq, hbd]
        exact List.mem_append_left otherVectors (by
          simpa [boundary] using hboundary)
      · rw [heq]
        apply List.mem_append_right prefixHistory
        dsimp [otherVectors]
        apply List.mem_map.mpr
        refine ⟨d, ?_, rfl⟩
        apply List.mem_filter.mpr
        constructor
        · dsimp [shifted, late, d]
          apply List.mem_map.mpr
          refine ⟨k, List.mem_filter.mpr ⟨hk, ?_⟩, ?_⟩
          · exact decide_eq_true hkGt
          · rfl
        · exact decide_eq_true hbd
  have hcover : NoveltyCoverOn w N start times
      (prefixHistory ++ otherVectors) 0 := by
    refine ⟨[], by simp, ?_⟩
    intro k hk
    simpa using hmem k hk
  have hcountRaw := noveltyCoverOn_distinct_count hcover hnd
  have hcount : times.length ≤
      prefixHistory.length + otherVectors.length := by
    simpa [List.length_append] using hcountRaw
  have hotherVectorsLen : otherVectors.length = other.length := by
    simp [otherVectors]
  rw [hotherVectorsLen] at hcount
  omega

end GeneralN
