import TrackFiniteAlternation

/-!
# Endpoint/matching semantics of a productive lazy-point pass

For a tongue state `u`, switch `C` selects one internal edge between its stem
and `selectedBranch u C`.  The other branch, `unmatchedBranch u C`, is the
endpoint (defect) of that local matching.

The central theorem `rawProductiveAt_is_endpoint_pivot` proves directly from
`Wiring`/`stepN` that every productive event counted by
`TrackFiniteAlternation` enters exactly this unmatched endpoint, replaces the
selected internal edge by the endpoint edge, moves the endpoint to the old
selected branch, and leaves the traversed edge ready for exact reversal.

This is the rigorous bridge from tongue-vector accounting to the proposed
matching/endpoint walk. No periodicity, geometry, or finite-`N` enumeration is
used.
-/

namespace GeneralN

/-- Equality of restricted vectors gives equality at every represented
switch coordinate. -/
theorem restrict_eq_apply
    {N C : Nat} {u v : Tongues}
    (h : VectorCount.restrict N u = VectorCount.restrict N v)
    (hC : C < N) : u C = v C := by
  have hget := congrArg (fun xs : List Bool => xs[C]?) h
  simpa [VectorCount.restrict, List.getElem?_map,
    List.getElem?_range hC] using hget

/-- Branch currently joined to the stem by the selected internal edge. -/
def selectedBranch (u : Tongues) (C : Nat) : Nat :=
  branchPort C (u C)

/-- The other branch: the local unmatched endpoint/defect. -/
def unmatchedBranch (u : Tongues) (C : Nat) : Nat :=
  branchPort C (!(u C))

theorem selectedBranch_switch (u : Tongues) (C : Nat) :
    selectedBranch u C / 3 = C := by
  cases h : u C <;> simp [selectedBranch, branchPort, h] <;> omega

theorem unmatchedBranch_switch (u : Tongues) (C : Nat) :
    unmatchedBranch u C / 3 = C := by
  cases h : u C <;> simp [unmatchedBranch, branchPort, h] <;> omega

theorem selectedBranch_is_branch (u : Tongues) (C : Nat) :
    selectedBranch u C % 3 ≠ 0 := by
  cases h : u C <;> simp [selectedBranch, branchPort, h] <;> omega

theorem unmatchedBranch_is_branch (u : Tongues) (C : Nat) :
    unmatchedBranch u C % 3 ≠ 0 := by
  cases h : u C <;> simp [unmatchedBranch, branchPort, h] <;> omega

theorem selected_unmatched_ne (u : Tongues) (C : Nat) :
    selectedBranch u C ≠ unmatchedBranch u C := by
  cases h : u C <;>
    simp [selectedBranch, unmatchedBranch, branchPort, h]

/-- Facing the stem traverses the selected matching edge without a write. -/
theorem arrive_stem_selected (u : Tongues) (C : Nat) :
    arrive u (3*C) = (selectedBranch u C, u) := by
  simp [arrive, selectedBranch]

theorem arrive_unmatched_pivots (u : Tongues) (C : Nat) :
    arrive u (unmatchedBranch u C) = (3*C, flipAt u C) := by
  have hbranch := unmatchedBranch_is_branch u C
  have hswitch := unmatchedBranch_switch u C
  have hvalue : bval (unmatchedBranch u C) = !(u C) := by
    cases h : u C <;>
      simp [unmatchedBranch, branchPort, bval, h] <;> omega
  have hpin : pin u (unmatchedBranch u C) = flipAt u C :=
    pin_eq_flipAt hswitch hvalue
  simp [arrive, hbranch, hswitch, hpin]

/-- After the pivot, the old selected branch is the new unmatched endpoint. -/
theorem selected_after_flip_eq_unmatched (u : Tongues) (C : Nat) :
    selectedBranch (flipAt u C) C = unmatchedBranch u C := by
  cases h : u C <;>
    simp [selectedBranch, unmatchedBranch, branchPort, flipAt, h]

/-- The traversed pivot edge is immediately grooved for exact reversal. -/
theorem arrive_pivot_back (u : Tongues) (C : Nat) :
    arrive (flipAt u C) (3*C) =
      (unmatchedBranch u C, flipAt u C) := by
  rw [arrive_stem_selected, selected_after_flip_eq_unmatched]

private theorem productive_step_configs
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    ∃ cur next,
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next := by
  cases hnext : stepN w (k+1) start with
  | none =>
      have hlive := hprod.1
      simp [hnext] at hlive
  | some next =>
      have hsplit := stepN_add w k 1 start
      rw [hnext] at hsplit
      cases hcur : stepN w k start with
      | none => simp [hcur] at hsplit
      | some cur =>
          rw [hcur] at hsplit
          have hone : stepN w 1 cur = some next := by
            simpa using hsplit.symm
          have hstep : step w cur = some next := by
            simpa [stepN] using hone
          exact ⟨cur, next, rfl, rfl, hstep⟩

/-- Any successful successor time exposes the corresponding one-step raw
transition. -/
theorem live_successor_configs
    {w : Wiring} {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k+1) start).isSome) :
    ∃ cur next,
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next := by
  cases hnext : stepN w (k+1) start with
  | none => simp [hnext] at hlive
  | some next =>
      have hsplit := stepN_add w k 1 start
      rw [hnext] at hsplit
      cases hcur : stepN w k start with
      | none => simp [hcur] at hsplit
      | some cur =>
          rw [hcur] at hsplit
          have hone : stepN w 1 cur = some next := by
            simpa using hsplit.symm
          have hstep : step w cur = some next := by
            simpa [stepN] using hone
          exact ⟨cur, next, rfl, rfl, hstep⟩

/-- If one represented tongue changes across a successful raw step, that
step is productive and its writer is exactly that switch. -/
theorem raw_tongue_change_is_productive_writer
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start : Nat × Tongues} {k : Nat}
    {cur next : Nat × Tongues}
    (hcur : stepN w k start = some cur)
    (hnext : stepN w (k+1) start = some next)
    (hstep : step w cur = some next)
    (hchange : next.2 C ≠ cur.2 C) :
    RawProductiveAt w N start k ∧ rawWriterAt w start k = C := by
  have hparts := step_some_parts hstep
  have harrived : next.2 = (arrive cur.2 cur.1).2 := by
    simpa [arrivedTongues] using hparts.2
  have hwriter : cur.1/3 = C := by
    apply Classical.byContradiction
    intro hne
    apply hchange
    rw [harrived]
    exact arrive_preserves_other rfl (Ne.symm hne)
  have hvectorChange : restrictedTonguesAt w N start (k+1) ≠
      restrictedTonguesAt w N start k := by
    intro hEq
    have hfull : VectorCount.restrict N next.2 =
        VectorCount.restrict N cur.2 := by
      simpa [restrictedTonguesAt, tonguesAt, hcur, hnext] using hEq
    have hbit := restrict_eq_apply hfull hC
    exact hchange hbit
  constructor
  · exact ⟨by simp [hnext], hvectorChange⟩
  · simp [rawWriterAt, rawEntryAt, hcur, hwriter]

/-- If no earlier productive event has writer `C`, tongue `C` is still at
its initial value. This remains true if the train has already fallen off,
because `tonguesAt` then uses the initial configuration as its default. -/
theorem raw_tongue_stable_before_writer
    {w : Wiring} {N C : Nat} (hC : C < N)
    (start : Nat × Tongues) :
    ∀ k,
      (∀ j, j < k → RawProductiveAt w N start j →
        rawWriterAt w start j ≠ C) →
      (tonguesAt w start k) C = start.2 C := by
  intro k
  induction k with
  | zero =>
      intro _hno
      simp [tonguesAt, stepN]
  | succ n ih =>
      intro hno
      cases hnext : stepN w (n+1) start with
      | none => simp [tonguesAt, hnext]
      | some next =>
          have hlive : (stepN w (n+1) start).isSome := by
            simp [hnext]
          obtain ⟨cur, next', hcur, hnext', hstep⟩ :=
            live_successor_configs hlive
          have hnextEq : next' = next := by
            have heq := hnext'
            rw [hnext] at heq
            injection heq with h
            exact h.symm
          subst next'
          have hprior : (tonguesAt w start n) C = start.2 C :=
            ih (fun j hj hprod => hno j (by omega) hprod)
          by_cases hchange : next.2 C = cur.2 C
          · simpa [tonguesAt, hcur, hnext, hchange] using hprior
          · obtain ⟨hprod, hwriter⟩ :=
              raw_tongue_change_is_productive_writer
                hC hcur hnext hstep hchange
            exact (hno n (by omega) hprod hwriter).elim

/-- Restricted-vector productivity is a genuine change of the entered
switch's own tongue. -/
theorem rawProductiveAt_changes_writer
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    ∃ cur next,
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next ∧
      next.2 (cur.1/3) ≠ cur.2 (cur.1/3) := by
  obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
    productive_step_configs hprod
  have hparts := step_some_parts hstep
  have hwriterLt : cur.1/3 < N := by
    have hraw : rawWriterAt w start k = cur.1/3 := by
      simp [rawWriterAt, rawEntryAt, hcur]
    rw [← hraw]
    exact rawProductiveAt_writer_lt hN hprod
  have harrived : next.2 = (arrive cur.2 cur.1).2 := by
    simpa [arrivedTongues] using hparts.2
  have hchanged : next.2 (cur.1/3) ≠ cur.2 (cur.1/3) := by
    intro hsame
    apply hprod.2
    have hrestrict : VectorCount.restrict N next.2 =
        VectorCount.restrict N cur.2 := by
      unfold VectorCount.restrict
      apply List.map_congr_left
      intro j hj
      have hjN : j < N := List.mem_range.mp hj
      by_cases hjWriter : j = cur.1/3
      · simpa [hjWriter] using hsame
      · rw [harrived]
        exact arrive_preserves_other rfl hjWriter
    simpa [restrictedTonguesAt, tonguesAt, hcur, hnext] using hrestrict
  exact ⟨cur, next, hcur, hnext, hstep, hchanged⟩

/-- A first productive writer always creates a globally novel restricted
tongue vector. -/
theorem rawFirstWriterAt_novel
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hfirst : RawFirstWriterAt w N start k) :
    RawNovelAt w N start k := by
  have hwriterLt : rawWriterAt w start k < N :=
    rawProductiveAt_writer_lt hN hfirst.1
  obtain ⟨cur, next, hcur, hnext, _hstep, hchange⟩ :=
    rawProductiveAt_changes_writer hN hfirst.1
  let C := rawWriterAt w start k
  have hcurWriter : cur.1/3 = C := by
    simp [C, rawWriterAt, rawEntryAt, hcur]
  have hstable : ∀ t, t ≤ k →
      (tonguesAt w start t) C = start.2 C := by
    intro t ht
    apply raw_tongue_stable_before_writer hwriterLt start t
    intro j hj hprod
    exact hfirst.2 j (by omega) hprod
  intro hseen
  obtain ⟨j, hj, hvectorEq⟩ := List.mem_map.mp hseen
  have hjlt : j < k+1 := List.mem_range.mp hj
  have hbitEq : (tonguesAt w start j) C =
      (tonguesAt w start (k+1)) C := by
    apply restrict_eq_apply hvectorEq hwriterLt
  have hjStable := hstable j (by omega)
  have hkStable := hstable k (Nat.le_refl _)
  have hnextChange : (tonguesAt w start (k+1)) C ≠
      (tonguesAt w start k) C := by
    simpa [tonguesAt, hcur, hnext, C, hcurWriter] using hchange
  apply hnextChange
  rw [← hbitEq, hjStable, hkStable]

/-- A repeated-writer novelty post-vector cannot be hidden in the initial
vector or among any first-writer post-vector, whether that first writer lies
earlier or later in the finite horizon. -/
theorem repeatedWriterPost_not_mem_firstHistory
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {K k : Nat}
    (hk : k ∈ rawRepeatedWriterNovelTimes w N start K) :
    restrictedTonguesAt w N start (k+1) ∉
      rawFirstWriterHistory w N start K := by
  classical
  have hkEvent : RawRepeatedWriterNovelAt w N start k :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp hk).2
  intro hmem
  rcases List.mem_cons.mp hmem with hinitial | hfirstPost
  · apply hkEvent.2.2
    apply List.mem_map.mpr
    exact ⟨0, List.mem_range.mpr (by omega), hinitial.symm⟩
  · obtain ⟨i, hi, hvector⟩ := List.mem_map.mp hfirstPost
    have hiFirst : RawFirstWriterAt w N start i :=
      (mem_rawFirstWriterTimes_iff.mp hi).2
    have hiNovel : RawNovelAt w N start i :=
      rawFirstWriterAt_novel hN hiFirst
    have hik : i = k :=
      rawNovelAt_post_injective hiNovel hkEvent.2.2 hvector
    subst i
    exact hkEvent.2.1 hiFirst

/-- Every sampled repeated-writer post-time is genuinely outside the complete
first-writer history. -/
theorem repeatedWriterPostTimes_avoid_firstHistory
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    (start : Nat × Tongues) (K : Nat) :
    ∀ t ∈ rawRepeatedWriterPostTimes w N start K,
      restrictedTonguesAt w N start t ∉
        rawFirstWriterHistory w N start K := by
  classical
  intro t ht
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
  exact repeatedWriterPost_not_mem_firstHistory hN hk

/-- **Exact cover interface for the endpoint/matching proof. OPEN.**

The local structural argument may return its exceptional vectors rather than
counting event times directly.  It must cover the post-times of *all*
repeated-writer novelties by the first-writer history plus at most five
vectors.  Unlike a periodic-tail statement, this quantifies over every finite
horizon and makes no recurrence assumption. -/
def FiveRepeatedWriterNoveltyCover : Prop :=
  ∀ (w : Wiring) (N : Nat),
    (∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N) →
    ∀ (start : Nat × Tongues) (K : Nat),
      NoveltyCoverOn w N start
        (rawRepeatedWriterPostTimes w N start K)
        (rawFirstWriterHistory w N start K) 5

/-- The cover interface is exactly strong enough to discharge the finite
constant-five target: its sampled vectors are fresh and duplicate-free by
construction. -/
theorem fiveRepeatedWriterNovelty_of_cover
    (hcover : FiveRepeatedWriterNoveltyCover) :
    FiveRepeatedWriterNovelty := by
  intro w N hN start K
  have hnd : ((rawRepeatedWriterPostTimes w N start K).map
      (restrictedTonguesAt w N start)).Nodup := by
    rw [map_repeatedWriterPostTimes_eq_fresh]
    exact rawRepeatedWriterFresh_nodup w N start K
  have hcount := noveltyCoverOn_fresh_distinct_count
    (hcover w N hN start K)
    (repeatedWriterPostTimes_avoid_firstHistory hN start K) hnd
  simpa [rawRepeatedWriterPostTimes] using hcount

theorem rawProductiveAt_is_endpoint_pivot
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    ∃ cur next C,
      C = rawWriterAt w start k ∧
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next ∧
      cur.1 = unmatchedBranch cur.2 C ∧
      exitPort cur = 3*C ∧
      next.2 = flipAt cur.2 C ∧
      arrive next.2 (3*C) = (cur.1, next.2) := by
  obtain ⟨cur, next, hcur, hnext, hstep, hchanged⟩ :=
    rawProductiveAt_changes_writer hN hprod
  let C := cur.1/3
  have hC : C = rawWriterAt w start k := by
    simp [C, rawWriterAt, rawEntryAt, hcur]
  have hparts := step_some_parts hstep
  have harrive : arrive cur.2 cur.1 = (exitPort cur, next.2) := by
    apply Prod.ext
    · rfl
    · exact hparts.2.symm
  obtain ⟨hbranch, hexit, hpin, hback⟩ :=
    changed_arrival_is_trailing harrive hchanged
  have hflip : next.2 = flipAt cur.2 C := by
    exact changed_arrival_eq_flipAt harrive hchanged
  have hpinValue : next.2 C = bval cur.1 := by
    rw [hpin]
    simp [pin, C]
  have hopposite : bval cur.1 = !(cur.2 C) := by
    have hne : bval cur.1 ≠ cur.2 C := by
      intro heq
      apply hchanged
      rw [hpinValue, heq]
    cases hc : cur.2 C <;> cases hb : bval cur.1 <;> simp_all
  have hentry : cur.1 = unmatchedBranch cur.2 C := by
    have hrecover := branchPort_bval hbranch
    unfold unmatchedBranch
    rw [← hopposite]
    exact hrecover.symm
  refine ⟨cur, next, C, hC, hcur, hnext, hstep, hentry, ?_,
    hflip, ?_⟩
  · simpa [C] using hexit
  · rw [← hexit]
    exact hback

end GeneralN
