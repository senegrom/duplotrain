import TrackCurveGrowth

/-!
# Finite train-curve growth between self pivots

Koizumi's empty-curve argument has a dual formulation from the train's
point of view.  At a productive endpoint pivot which does not join two
points of the train's current selected curve, the whole current curve is
carried into the next curve and at least the pivot stem is added.

This file turns the local `CurveReach` theorem into a finite, raw-`stepN`
count.  In particular, a consecutive productive prefix containing no
self-pivot has length at most `3*N`, because there are only `3*N` physical
ports.  This is an unconditional theorem about that raw dynamical case, not
an assumed global decomposition.  The complementary self-pivot nesting is
still the obstruction to applying the measure across an arbitrary run.
-/

namespace GeneralN

/-- The represented ports on one selected train curve. -/
noncomputable def finiteCurvePorts
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) : List Nat := by
  classical
  exact (List.range (3 * N)).filter
    (fun p => decide (CurveReach w u root p))

theorem mem_finiteCurvePorts_iff
    {w : Wiring} {N : Nat} {u : Tongues} {root p : Nat} :
    p ∈ finiteCurvePorts w N u root ↔
      p < 3 * N ∧ CurveReach w u root p := by
  classical
  simp [finiteCurvePorts]

private theorem nodup_filter_nat_curve (pred : Nat → Bool) :
    ∀ {xs : List Nat}, xs.Nodup → (xs.filter pred).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : pred x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hmem => hnd.1 ((List.mem_filter.mp hmem).1),
            ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

theorem finiteCurvePorts_nodup
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) :
    (finiteCurvePorts w N u root).Nodup := by
  classical
  unfold finiteCurvePorts
  exact nodup_filter_nat_curve _ List.nodup_range

theorem finiteCurvePorts_length_le
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) :
    (finiteCurvePorts w N u root).length ≤ 3 * N := by
  classical
  unfold finiteCurvePorts
  have h := List.length_filter_le
    (fun p => decide (CurveReach w u root p)) (List.range (3 * N))
  simpa using h

private theorem nodup_subset_length_curve
    {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs ys : List α},
      xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length := by
  intro xs
  induction xs with
  | nil => intro ys _ _; exact Nat.zero_le _
  | cons x rest ih =>
      intro ys hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hrest : ∀ y ∈ rest, y ∈ ys.erase x := by
        intro y hy
        have hy' : y ∈ ys := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun heq => hnd.1 (heq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hy'
      have hle := ih hnd.2 hrest
      have herase : (ys.erase x).length = ys.length - 1 :=
        List.length_erase_of_mem hx
      have hpositive : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

private theorem length_lt_of_strict_subset_curve
    {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α}
    (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys)
    (y : α) (hy : y ∈ ys) (hnot : y ∉ xs) :
    xs.length < ys.length := by
  have hcons : (y :: xs).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hnot, hnd⟩
  have hconsSub : ∀ x ∈ y :: xs, x ∈ ys := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hy
    · exact hsub x hx
  have hle := nodup_subset_length_curve hcons hconsSub
  simp only [List.length_cons] at hle
  omega

/-- A non-self productive endpoint pivot strictly enlarges the finite train
curve, even after re-rooting that curve at the next raw entry port. -/
theorem nonself_endpoint_pivot_finiteCurvePorts_growth
    {w : Wiring} {N C : Nat} {cur next : Nat × Tongues}
    (hC : C < N)
    (hstep : step w cur = some next)
    (hentry : cur.1 = unmatchedBranch cur.2 C)
    (hexit : exitPort cur = 3 * C)
    (hflip : next.2 = flipAt cur.2 C)
    (houtside : ¬ CurveReach w cur.2 cur.1 (3 * C)) :
    (finiteCurvePorts w N cur.2 cur.1).length <
      (finiteCurvePorts w N next.2 next.1).length := by
  have hgrowth := unmatched_pivot_strict_curve_growth cur.2 C (by
    simpa [hentry] using houtside)
  have hlink : w.link (3 * C) = some next.1 := by
    have hp := (step_some_parts hstep).1
    simpa [hexit] using hp
  have hrootStem :
      CurveReach w next.2 cur.1 (3 * C) := by
    simpa [hentry, hflip] using hgrowth.2.1
  have hrootNext : CurveReach w next.2 cur.1 next.1 :=
    CurveReach.step hrootStem (Or.inl hlink)
  have hnextRoot : CurveReach w next.2 next.1 cur.1 :=
    curveReach_symm hrootNext
  have hlift : ∀ p, CurveReach w cur.2 cur.1 p →
      CurveReach w next.2 next.1 p := by
    intro p hp
    have hp' : CurveReach w next.2 cur.1 p := by
      simpa [hentry, hflip] using hgrowth.1 p (by
        simpa [hentry] using hp)
    exact curveReach_trans hnextRoot hp'
  have hstemNew : CurveReach w next.2 next.1 (3 * C) :=
    curveReach_trans hnextRoot hrootStem
  have hsubset : ∀ p,
      p ∈ finiteCurvePorts w N cur.2 cur.1 →
      p ∈ finiteCurvePorts w N next.2 next.1 := by
    intro p hp
    rw [mem_finiteCurvePorts_iff] at hp ⊢
    exact ⟨hp.1, hlift p hp.2⟩
  have hstemMem : 3 * C ∈ finiteCurvePorts w N next.2 next.1 := by
    rw [mem_finiteCurvePorts_iff]
    exact ⟨by omega, hstemNew⟩
  have hstemNot : 3 * C ∉ finiteCurvePorts w N cur.2 cur.1 := by
    intro hm
    exact houtside (mem_finiteCurvePorts_iff.mp hm).2
  exact length_lt_of_strict_subset_curve
    (finiteCurvePorts_nodup w N cur.2 cur.1)
    hsubset (3 * C) hstemMem hstemNot

/-- A newly selected internal edge at `C` never escapes the old selected
curve when the pivot is a self-join.  Away from `C` the internal edge is
unchanged; at `C` both of its endpoints were already on the old curve. -/
theorem flipped_internal_edge_stays_in_self_curve
    {w : Wiring} {u : Tongues} {C p q : Nat}
    (hself : CurveReach w u (unmatchedBranch u C) (3 * C))
    (hp : CurveReach w u (unmatchedBranch u C) p)
    (hedge : InternalCurveEdge (flipAt u C) p q) :
    CurveReach w u (unmatchedBranch u C) q := by
  by_cases hpC : p / 3 = C
  · unfold InternalCurveEdge at hedge
    have hends := arrive_stem_endpoint (flipAt u C) p
    rw [hedge] at hends
    rcases hends with hpStem | hqStem
    · have hpEq : p = 3 * C := by omega
      subst p
      have hpivot := arrive_pivot_back u C
      rw [hpivot] at hedge
      injection hedge with hq
      subst q
      exact CurveReach.refl
    · have hqEq : q = 3 * C := by omega
      simpa [hqEq] using hself
  · have hold : InternalCurveEdge u p q := by
      have hback := internalCurveEdge_flip_other
        (u := flipAt u C) (C := C) hedge hpC
      simpa [flipAt_flipAt] using hback
    exact CurveReach.step hp (Or.inr hold)

/-- At a self-pivot the next train curve is contained in the old one.  This
is the shrinking half dual to `unmatched_pivot_strict_curve_growth`. -/
theorem self_endpoint_pivot_finiteCurvePorts_nonincrease
    {w : Wiring} {N C : Nat} {cur next : Nat × Tongues}
    (hstep : step w cur = some next)
    (hentry : cur.1 = unmatchedBranch cur.2 C)
    (hexit : exitPort cur = 3 * C)
    (hflip : next.2 = flipAt cur.2 C)
    (hself : CurveReach w cur.2 cur.1 (3 * C)) :
    (finiteCurvePorts w N next.2 next.1).length ≤
      (finiteCurvePorts w N cur.2 cur.1).length := by
  have hparts := step_some_parts hstep
  have hlink : w.link (3 * C) = some next.1 := by
    simpa [hexit] using hparts.1
  have hrootNextOld : CurveReach w cur.2 cur.1 next.1 :=
    CurveReach.step hself (Or.inl hlink)
  have hself' :
      CurveReach w cur.2 (unmatchedBranch cur.2 C) (3 * C) := by
    simpa [hentry] using hself
  have hlift : ∀ p, CurveReach w next.2 next.1 p →
      CurveReach w cur.2 cur.1 p := by
    intro p hreach
    induction hreach with
    | refl => exact hrootNextOld
    | @step x y hprefix hedge ih =>
        rcases hedge with htrack | hinternal
        · exact CurveReach.step ih (Or.inl htrack)
        · have hy :
              CurveReach w cur.2 (unmatchedBranch cur.2 C) y := by
            apply flipped_internal_edge_stays_in_self_curve hself'
            · simpa [hentry] using ih
            · simpa [hflip] using hinternal
          simpa [hentry] using hy
  have hsubset : ∀ p,
      p ∈ finiteCurvePorts w N next.2 next.1 →
      p ∈ finiteCurvePorts w N cur.2 cur.1 := by
    intro p hp
    rw [mem_finiteCurvePorts_iff] at hp ⊢
    exact ⟨hp.1, hlift p hp.2⟩
  exact nodup_subset_length_curve
    (finiteCurvePorts_nodup w N next.2 next.1) hsubset

/-- The selected train curve at a raw time, represented by its in-range
ports.  The default configuration matters only after a fall-off; all growth
theorems below assume the relevant productive step is live. -/
noncomputable def rawFiniteCurveSizeAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Nat :=
  let cur := (stepN w k start).getD start
  (finiteCurvePorts w N cur.2 cur.1).length

/-- The raw productive pivot at time `k` is a self-pivot when its unmatched
entry endpoint already lies on the selected curve containing its stem. -/
def RawCurveSelfAt
    (w : Wiring) (start : Nat × Tongues) (k : Nat) : Prop :=
  let cur := (stepN w k start).getD start
  CurveReach w cur.2 cur.1 (3 * (cur.1 / 3))

/-- Raw `stepN` form of strict train-curve growth. -/
theorem rawProductiveAt_nonself_curve_growth
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hnonself : ¬ RawCurveSelfAt w start k) :
    rawFiniteCurveSizeAt w N start k <
      rawFiniteCurveSizeAt w N start (k+1) := by
  obtain ⟨cur, next, C, hCwriter, hcur, hnext, hstep,
      hentry, hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hwriterLt := rawProductiveAt_writer_lt hN hprod
  have hC : C < N := by
    rw [hCwriter]
    exact hwriterLt
  have hCcur : C = cur.1 / 3 := by
    simpa [rawWriterAt, rawEntryAt, hcur] using hCwriter
  have houtside : ¬ CurveReach w cur.2 cur.1 (3 * C) := by
    unfold RawCurveSelfAt at hnonself
    simpa [hcur, hCcur] using hnonself
  have hgrowth := nonself_endpoint_pivot_finiteCurvePorts_growth
    hC hstep hentry hexit hflip houtside
  simpa [rawFiniteCurveSizeAt, hcur, hnext] using hgrowth

/-- Raw `stepN` form of the shrinking half: a productive self-pivot cannot
increase the finite train curve. -/
theorem rawProductiveAt_self_curve_nonincrease
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hself : RawCurveSelfAt w start k) :
    rawFiniteCurveSizeAt w N start (k+1) ≤
      rawFiniteCurveSizeAt w N start k := by
  obtain ⟨cur, next, C, hCwriter, hcur, hnext, hstep,
      hentry, hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hCcur : C = cur.1 / 3 := by
    simpa [rawWriterAt, rawEntryAt, hcur] using hCwriter
  have hself' : CurveReach w cur.2 cur.1 (3 * C) := by
    unfold RawCurveSelfAt at hself
    simpa [hcur, hCcur] using hself
  have hshrink := self_endpoint_pivot_finiteCurvePorts_nonincrease
    (N := N) hstep hentry hexit hflip hself'
  simpa [rawFiniteCurveSizeAt, hcur, hnext] using hshrink

/-- A live raw step which is not productive leaves the complete tongue
vector unchanged.  Boundedness is used only to know that the current writer
is one of the represented `N` switches. -/
theorem rawNonproductiveAt_tongues_eq
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start cur next : Nat × Tongues} {k : Nat}
    (hcur : stepN w k start = some cur)
    (hnext : stepN w (k+1) start = some next)
    (hstep : step w cur = some next)
    (hnot : ¬ RawProductiveAt w N start k) :
    next.2 = cur.2 := by
  have hparts := step_some_parts hstep
  have hwriterLt : cur.1 / 3 < N := by
    have hexitLt := (hN _ _ hparts.1).1
    rw [← arrive_exit_switch cur.2 cur.1]
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    simpa [exitPort, Nat.mul_comm] using hexitLt
  have hwriter : next.2 (cur.1 / 3) = cur.2 (cur.1 / 3) := by
    by_cases heq : next.2 (cur.1 / 3) = cur.2 (cur.1 / 3)
    · exact heq
    · exact (hnot (raw_tongue_change_is_productive_writer
        hwriterLt hcur hnext hstep heq).1).elim
  funext j
  by_cases hj : j = cur.1 / 3
  · simpa [hj] using hwriter
  · have harrived : next.2 = (arrive cur.2 cur.1).2 := by
      simpa [arrivedTongues] using hparts.2
    rw [harrived]
    exact arrive_preserves_other rfl hj

/-- A live nonproductive step only moves the root along its present selected
curve.  Consequently the represented finite curve, and hence its size, is
unchanged. -/
theorem rawNonproductiveAt_curve_size_eq
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k+1) start).isSome)
    (hnot : ¬ RawProductiveAt w N start k) :
    rawFiniteCurveSizeAt w N start (k+1) =
      rawFiniteCurveSizeAt w N start k := by
  obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
    live_successor_configs hlive
  have hstate := rawNonproductiveAt_tongues_eq
    hN hcur hnext hstep hnot
  have hparts := step_some_parts hstep
  have hinternal : InternalCurveEdge cur.2 cur.1 (exitPort cur) := by
    unfold InternalCurveEdge
    apply Prod.ext
    · rfl
    · change arrivedTongues cur = cur.2
      rw [← hparts.2, hstate]
  have hcurNext : CurveReach w cur.2 cur.1 next.1 :=
    CurveReach.step
      (curveReach_edge (Or.inr hinternal))
      (Or.inl hparts.1)
  have hnextCur : CurveReach w cur.2 next.1 cur.1 :=
    curveReach_symm hcurNext
  have hforward : ∀ p,
      p ∈ finiteCurvePorts w N cur.2 cur.1 →
      p ∈ finiteCurvePorts w N next.2 next.1 := by
    intro p hp
    rw [mem_finiteCurvePorts_iff] at hp ⊢
    rw [hstate]
    exact ⟨hp.1, curveReach_trans hnextCur hp.2⟩
  have hbackward : ∀ p,
      p ∈ finiteCurvePorts w N next.2 next.1 →
      p ∈ finiteCurvePorts w N cur.2 cur.1 := by
    intro p hp
    rw [mem_finiteCurvePorts_iff] at hp ⊢
    rw [hstate] at hp
    exact ⟨hp.1, curveReach_trans hcurNext hp.2⟩
  have hleForward := nodup_subset_length_curve
    (finiteCurvePorts_nodup w N cur.2 cur.1) hforward
  have hleBackward := nodup_subset_length_curve
    (finiteCurvePorts_nodup w N next.2 next.1) hbackward
  have hlength : (finiteCurvePorts w N cur.2 cur.1).length =
      (finiteCurvePorts w N next.2 next.1).length := by omega
  unfold rawFiniteCurveSizeAt
  simp only [hcur, hnext, Option.getD_some]
  exact hlength.symm

/-- Productive event times in a finite raw prefix. -/
noncomputable def rawProductiveCurveTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (List.range K).filter
    (fun k => decide (RawProductiveAt w N start k))

theorem mem_rawProductiveCurveTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawProductiveCurveTimes w N start K ↔
      k < K ∧ RawProductiveAt w N start k := by
  classical
  simp [rawProductiveCurveTimes]

private theorem rawProductiveCurveTimes_length_succ_of_productive
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    RawProductiveAt w N start K →
    (rawProductiveCurveTimes w N start (K+1)).length =
      (rawProductiveCurveTimes w N start K).length + 1 := by
  classical
  intro hprod
  simp [rawProductiveCurveTimes, List.range_succ, hprod]

private theorem rawProductiveCurveTimes_length_succ_of_nonproductive
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    ¬ RawProductiveAt w N start K →
    (rawProductiveCurveTimes w N start (K+1)).length =
      (rawProductiveCurveTimes w N start K).length := by
  classical
  intro hnot
  simp [rawProductiveCurveTimes, List.range_succ, hnot]

/-- **Global finite growth bound for a merge-only raw prefix.**

If every step of a consecutive prefix is a productive endpoint pivot and no
such pivot is a self-join, the prefix contains at most `3*N` steps.  This is
the finite port-count form of the curve-shrinking invariant on one merge
epoch. -/
theorem nonself_productive_prefix_le_three_mul_N
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hprod : ∀ k, k < K → RawProductiveAt w N start k)
    (hnonself : ∀ k, k < K → ¬ RawCurveSelfAt w start k) :
    K ≤ 3 * N := by
  let sizeAt := rawFiniteCurveSizeAt w N start
  have hgrow : ∀ k, k < K → sizeAt k < sizeAt (k+1) := by
    intro k hk
    exact rawProductiveAt_nonself_curve_growth hN
      (hprod k hk) (hnonself k hk)
  have hacc : ∀ j, j ≤ K → sizeAt 0 + j ≤ sizeAt j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        have hjK : j < K := by omega
        have hprev := ih (by omega)
        have hstep := hgrow j hjK
        omega
  have hfinal := hacc K (Nat.le_refl _)
  have hbound : sizeAt K ≤ 3 * N := by
    unfold sizeAt rawFiniteCurveSizeAt
    exact finiteCurvePorts_length_le w N
      ((stepN w K start).getD start).2
      ((stepN w K start).getD start).1
  omega

/-- **No-op-insensitive curve-growth bound.**

In an arbitrary live prefix, suppose every productive pivot is non-self.
Facing moves and already-grooved trailing moves may occur in between.  There
are nevertheless at most `3*N` productive pivots, because no-op steps keep
the finite train curve fixed while every productive pivot strictly enlarges
it. -/
theorem nonself_productive_times_le_three_mul_N
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (hnonself : ∀ k, k < K → RawProductiveAt w N start k →
      ¬ RawCurveSelfAt w start k) :
    (rawProductiveCurveTimes w N start K).length ≤ 3 * N := by
  let sizeAt := rawFiniteCurveSizeAt w N start
  let countAt := fun k => (rawProductiveCurveTimes w N start k).length
  have hacc : ∀ j, j ≤ K → sizeAt 0 + countAt j ≤ sizeAt j := by
    intro j hj
    induction j with
    | zero => simp [countAt, rawProductiveCurveTimes]
    | succ j ih =>
        have hjK : j < K := by omega
        have hprev := ih (by omega)
        by_cases hprod : RawProductiveAt w N start j
        · have hgrow : sizeAt j < sizeAt (j+1) :=
            rawProductiveAt_nonself_curve_growth hN hprod
              (hnonself j hjK hprod)
          have hcount := rawProductiveCurveTimes_length_succ_of_productive
            w N start j hprod
          change sizeAt 0 +
            (rawProductiveCurveTimes w N start j).length ≤ sizeAt j at hprev
          change sizeAt 0 +
            (rawProductiveCurveTimes w N start (j+1)).length ≤ sizeAt (j+1)
          rw [hcount]
          omega
        · have heq : sizeAt (j+1) = sizeAt j :=
            rawNonproductiveAt_curve_size_eq hN (hlive (j+1) (by omega)) hprod
          have hcount := rawProductiveCurveTimes_length_succ_of_nonproductive
            w N start j hprod
          change sizeAt 0 +
            (rawProductiveCurveTimes w N start j).length ≤ sizeAt j at hprev
          change sizeAt 0 +
            (rawProductiveCurveTimes w N start (j+1)).length ≤ sizeAt (j+1)
          rw [hcount, heq]
          exact hprev
  have hfinal := hacc K (Nat.le_refl _)
  change sizeAt 0 +
    (rawProductiveCurveTimes w N start K).length ≤ sizeAt K at hfinal
  have hbound : sizeAt K ≤ 3 * N := by
    unfold sizeAt rawFiniteCurveSizeAt
    exact finiteCurvePorts_length_le w N
      ((stepN w K start).getD start).2
      ((stepN w K start).getD start).1
  omega

end GeneralN
