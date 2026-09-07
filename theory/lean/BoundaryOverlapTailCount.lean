import SharpStateLawAssembly

/-!
# Boundary-aware direct-tail counting

A directly counted suffix starts at a vector already present at the end of the
prefix.  Filter later suffix samples equal to that boundary; for all remaining
samples, adjoin suffix time zero and invoke the tail cap.  This saves one
vector exactly compared with naïvely adding the two cardinality bounds.
-/

namespace GeneralN

/-- Filtering sample times keeps their mapped values duplicate-free. -/
theorem tailsharp_nodup_map_filter
    {α : Type}
    {f : Nat → α} (p : Nat → Bool) :
    ∀ {xs : List Nat},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by grind

/-- Cover-level form of boundary overlap. The boundary vector is already
historical, so a suffix with direct cap cap contributes at most cap-1 fresh
vectors. -/
theorem boundary_history_then_direct_tail_cover
    {w : Wiring} {N lead cap : Nat}
    {start endpoint : Prod Nat Tongues}
    (hreach : stepN w lead start = some endpoint)
    (prefixHistory : List (List Bool))
    (hprefixCover : forall d, d <= lead ->
      List.Mem (restrictedTonguesAt w N start d) prefixHistory)
    (hboundary :
      List.Mem (VectorCount.restrict N endpoint.2) prefixHistory)
    (htail : forall tailTimes : List Nat,
      (forall k, List.Mem k tailTimes ->
        (stepN w k endpoint).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N endpoint)).Nodup ->
      tailTimes.length <= cap)
    (hcapPos : 0 < cap)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    NoveltyCoverOn w N start times prefixHistory (cap - 1) := by
  let freshTimes := times.filter fun k =>
    decide (restrictedTonguesAt w N start k ∉ prefixHistory)
  let shifted := freshTimes.map (fun k => k - lead)
  let fresh := freshTimes.map (restrictedTonguesAt w N start)
  have hinfo : ∀ k ∈ freshTimes,
      (stepN w (k - lead) endpoint).isSome ∧
      restrictedTonguesAt w N endpoint (k - lead) =
        restrictedTonguesAt w N start k := by
    intro k hk
    obtain ⟨hkt, hfresh⟩ := List.mem_filter.mp hk
    have hlate : lead < k := by
      have hn := of_decide_eq_true hfresh
      by_cases h : k ≤ lead
      · exact (hn (hprefixCover k h)).elim
      · omega
    have heq : k = lead + (k - lead) := by omega
    have hl := hlive k hkt
    rw [heq, stepN_add, hreach] at hl
    have hl' : (stepN w (k - lead) endpoint).isSome := hl
    refine ⟨hl', ?_⟩
    simpa only [← heq] using (restrictedTonguesAt_add_of_reaches hreach
      (Option.isSome_iff_exists.mp hl')).symm
  have hmap : shifted.map (restrictedTonguesAt w N endpoint) = fresh := by
    rw [List.map_map]
    exact List.map_congr_left fun k hk => (hinfo k hk).2
  have hzero : restrictedTonguesAt w N endpoint 0 =
      VectorCount.restrict N endpoint.2 := by
    simp [restrictedTonguesAt, tonguesAt, stepN]
  have hnd' : ((0 :: shifted).map (restrictedTonguesAt w N endpoint)).Nodup := by
    rw [List.map_cons, hmap, List.nodup_cons, hzero]
    constructor
    · intro hm
      obtain ⟨k, hk, heq⟩ := List.mem_map.mp hm
      exact (of_decide_eq_true (List.mem_filter.mp hk).2) (heq.symm ▸ hboundary)
    · exact tailsharp_nodup_map_filter _ hnd
  have hbound := htail (0 :: shifted) (by
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · simp [stepN]
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
      exact (hinfo k hk).1) hnd'
  refine ⟨fresh, ?_, ?_⟩
  · have : freshTimes.length + 1 ≤ cap := by simpa [shifted] using hbound
    simp only [fresh, List.length_map]
    omega
  · intro k hk
    by_cases hh : restrictedTonguesAt w N start k ∈ prefixHistory
    · exact List.mem_append_left _ hh
    · exact List.mem_append_right _ (List.mem_map.mpr
        ⟨k, List.mem_filter.mpr ⟨hk, decide_eq_true hh⟩, rfl⟩)

end GeneralN
