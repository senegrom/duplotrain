import KoizumiFramePersistence

/-!
# Canonical self-pivot anchors for repeated novelties

`repeated_writer_close_self_or_interior_self` says that every repeated writer
frame contains a productive self-pivot.  This file makes that witness
canonical: choose the latest self-pivot no later than the novel closing time.
The canonical anchors are monotone in closing time, and no further self-pivot
may occur between an anchor and its close.

This is the finite charging interface for five hypothetical novel repeated
frames.  The remaining physical step is to show that a plateau of equal
anchors is a bounded reflector/interlacement tail, while a strict increase
is a newly nested shrink frame chargeable to its writer.
-/

namespace GeneralN

/-- A productive raw event which is also a train-curve self-pivot. -/
def RawSelfPivotAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : Prop :=
  RawProductiveAt w N start k ∧ RawTrainCurveSelfAt w start k

/-- The last productive self-pivot at or before `close`. -/
structure LatestSelfAnchor
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (close anchor : Nat) : Prop where
  le_close : anchor ≤ close
  self_pivot : RawSelfPivotAt w N start anchor
  latest : ∀ j, anchor < j → j ≤ close →
    ¬ RawSelfPivotAt w N start j

private theorem exists_last_lt_anchor
    (P : Nat → Prop) [DecidablePred P] :
    ∀ {bound : Nat}, (∃ i, i < bound ∧ P i) →
      ∃ i, i < bound ∧ P i ∧
        ∀ j, i < j → j < bound → ¬ P j := by
  intro bound
  induction bound with
  | zero =>
      rintro ⟨i, hi, _⟩
      omega
  | succ n ih =>
      intro hex
      by_cases hn : P n
      · exact ⟨n, by omega, hn, by omega⟩
      · have hbelow : ∃ i, i < n ∧ P i := by
          obtain ⟨i, hi, hPi⟩ := hex
          by_cases hin : i = n
          · exact (hn (hin ▸ hPi)).elim
          · exact ⟨i, by omega, hPi⟩
        obtain ⟨i, hi, hPi, hlast⟩ := ih hbelow
        exact ⟨i, by omega, hPi, fun j hij hj => by
          by_cases hjn : j = n
          · subst j
            exact hn
          · exact hlast j hij (by omega)⟩

/-- Every repeated-writer novelty has some productive self-pivot no later
than its closing time. -/
theorem RawRepeatedWriterNovelAt.has_self_pivot_anchor
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {close : Nat}
    (h : RawRepeatedWriterNovelAt w N start close) :
    ∃ anchor, anchor ≤ close ∧ RawSelfPivotAt w N start anchor := by
  have hprevious : ∃ left, left < close ∧
      RawProductiveAt w N start left ∧
      rawWriterAt w start left = rawWriterAt w start close := by
    apply Classical.byContradiction
    intro hnone
    apply h.2.1
    refine ⟨h.1, ?_⟩
    intro j hj hjprod hsame
    exact hnone ⟨j, hj, hjprod, hsame⟩
  obtain ⟨left, hleft, hleftProd, hsame⟩ := hprevious
  rcases repeated_writer_close_self_or_interior_self
      hN hleft hleftProd h.1 hsame with
    hclose | hinterior
  · exact ⟨close, Nat.le_refl _, h.1, hclose⟩
  · obtain ⟨j, _hlj, hjc, hprod, hself⟩ := hinterior
    exact ⟨j, by omega, hprod, hself⟩

/-- Canonicalize the preceding existence result by taking the last such
self-pivot. -/
theorem RawRepeatedWriterNovelAt.has_latest_self_anchor
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {close : Nat}
    (h : RawRepeatedWriterNovelAt w N start close) :
    ∃ anchor, LatestSelfAnchor w N start close anchor := by
  classical
  obtain ⟨someAnchor, hle, hself⟩ := h.has_self_pivot_anchor hN
  let P : Nat → Prop := fun j => RawSelfPivotAt w N start j
  have hex : ∃ j, j < close + 1 ∧ P j :=
    ⟨someAnchor, by omega, hself⟩
  obtain ⟨anchor, hlt, hP, hlast⟩ :=
    exists_last_lt_anchor P hex
  exact ⟨anchor, {
    le_close := by omega
    self_pivot := hP
    latest := fun j haj hjc => hlast j haj (by omega)
  }⟩

/-- Latest anchors are unique. -/
theorem LatestSelfAnchor.unique
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {close a b : Nat}
    (A : LatestSelfAnchor w N start close a)
    (B : LatestSelfAnchor w N start close b) : a = b := by
  by_cases hab : a = b
  · exact hab
  · by_cases hlt : a < b
    · exact (A.latest b hlt B.le_close B.self_pivot).elim
    · have hba : b < a := by omega
      exact (B.latest a hba A.le_close A.self_pivot).elim

/-- Canonical self-pivot anchors move monotonically forward as closing times
move forward. -/
theorem LatestSelfAnchor.monotone
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {close₁ close₂ a₁ a₂ : Nat}
    (hclose : close₁ ≤ close₂)
    (A₁ : LatestSelfAnchor w N start close₁ a₁)
    (A₂ : LatestSelfAnchor w N start close₂ a₂) :
    a₁ ≤ a₂ := by
  by_cases hle : a₁ ≤ a₂
  · exact hle
  · exfalso
    have hlt : a₂ < a₁ := by omega
    exact A₂.latest a₁ hlt
      (Nat.le_trans A₁.le_close hclose) A₁.self_pivot

/-- Equal anchors give a self-pivot-free open interval all the way to the
later close.  This is the plateau case to be discharged by the physical
triple-interlacement/reflector theorem. -/
theorem LatestSelfAnchor.equal_plateau_no_later_self
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {close₁ close₂ anchor : Nat}
    (_A₁ : LatestSelfAnchor w N start close₁ anchor)
    (A₂ : LatestSelfAnchor w N start close₂ anchor) :
    ∀ j, anchor < j → j ≤ close₂ →
      ¬ RawSelfPivotAt w N start j :=
  A₂.latest

/-- Strictly later anchors exhibit a genuinely new productive self-pivot
after the earlier anchor and no later than the later close.  This is the
nested-shrink charge case. -/
theorem LatestSelfAnchor.strict_growth_supplies_new_self
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {close₁ close₂ a₁ a₂ : Nat}
    (_A₁ : LatestSelfAnchor w N start close₁ a₁)
    (A₂ : LatestSelfAnchor w N start close₂ a₂)
    (hlt : a₁ < a₂) :
    a₁ < a₂ ∧ a₂ ≤ close₂ ∧ RawSelfPivotAt w N start a₂ :=
  ⟨hlt, A₂.le_close, A₂.self_pivot⟩

/-- **Five-frame charging normal form.**

Five chronologically ordered repeated-writer novelties admit five canonical
self-pivot anchors in nondecreasing order.  Equal adjacent anchors are the
single plateau/interlacement case; every strict inequality exposes a new
nested shrink pivot.  This is the exact finite shape consumed by the final
four-novelty contradiction. -/
theorem five_repeated_novelties_have_monotone_self_anchors
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {r₀ r₁ r₂ r₃ r₄ : Nat}
    (h01 : r₀ < r₁) (h12 : r₁ < r₂)
    (h23 : r₂ < r₃) (h34 : r₃ < r₄)
    (H₀ : RawRepeatedWriterNovelAt w N start r₀)
    (H₁ : RawRepeatedWriterNovelAt w N start r₁)
    (H₂ : RawRepeatedWriterNovelAt w N start r₂)
    (H₃ : RawRepeatedWriterNovelAt w N start r₃)
    (H₄ : RawRepeatedWriterNovelAt w N start r₄) :
    ∃ a₀ a₁ a₂ a₃ a₄,
      LatestSelfAnchor w N start r₀ a₀ ∧
      LatestSelfAnchor w N start r₁ a₁ ∧
      LatestSelfAnchor w N start r₂ a₂ ∧
      LatestSelfAnchor w N start r₃ a₃ ∧
      LatestSelfAnchor w N start r₄ a₄ ∧
      a₀ ≤ a₁ ∧ a₁ ≤ a₂ ∧ a₂ ≤ a₃ ∧ a₃ ≤ a₄ := by
  obtain ⟨a₀, A₀⟩ := H₀.has_latest_self_anchor hN
  obtain ⟨a₁, A₁⟩ := H₁.has_latest_self_anchor hN
  obtain ⟨a₂, A₂⟩ := H₂.has_latest_self_anchor hN
  obtain ⟨a₃, A₃⟩ := H₃.has_latest_self_anchor hN
  obtain ⟨a₄, A₄⟩ := H₄.has_latest_self_anchor hN
  exact ⟨a₀, a₁, a₂, a₃, a₄, A₀, A₁, A₂, A₃, A₄,
    A₀.monotone (by omega) A₁,
    A₁.monotone (by omega) A₂,
    A₂.monotone (by omega) A₃,
    A₃.monotone (by omega) A₄⟩

end GeneralN
