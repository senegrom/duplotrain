import TrackEndpointMatching

/-!
# Monotone growth of the train curve

For a fixed tongue vector, ordinary track edges together with the selected
stem--branch passage at every switch form a disjoint union of curves.  This
file gives that picture a small raw-`Wiring` interface.

The local theorem `unmatched_pivot_strict_curve_growth` is the key point.  If
the train enters an unmatched branch and that branch is not already on the
same selected curve as the switch stem, then the pivot preserves every point
of the old train curve and adds the stem.  Thus a non-self pivot is a genuine
strict growth event.  The complementary self-pivot case is where the
reflector/restoration analysis has to act.

No finiteness, planarity, recurrence, or small-`N` assumption is used here.
-/

namespace GeneralN

/-- A currently selected internal switch passage.  Its tongue vector is
unchanged by traversing it. -/
def InternalCurveEdge (u : Tongues) (p q : Nat) : Prop :=
  arrive u p = (q, u)

/-- One undirected edge of the curve selected by `u`: either an ordinary
track edge or a selected internal switch passage. -/
def CurveEdge (w : Wiring) (u : Tongues) (p q : Nat) : Prop :=
  w.link p = some q ∨ InternalCurveEdge u p q

/-- Reachability on one selected curve. -/
inductive CurveReach (w : Wiring) (u : Tongues) (root : Nat) : Nat → Prop
  | refl : CurveReach w u root root
  | step {p q : Nat} :
      CurveReach w u root p → CurveEdge w u p q →
      CurveReach w u root q

theorem internalCurveEdge_symm
    {u : Tongues} {p q : Nat}
    (h : InternalCurveEdge u p q) :
    InternalCurveEdge u q p := by
  have hback := arrive_back u p
  unfold InternalCurveEdge at h ⊢
  rw [h] at hback
  exact hback

theorem curveEdge_symm
    {w : Wiring} {u : Tongues} {p q : Nat}
    (h : CurveEdge w u p q) :
    CurveEdge w u q p := by
  rcases h with htrack | hinternal
  · exact Or.inl (w.symm p q htrack)
  · exact Or.inr (internalCurveEdge_symm hinternal)

theorem curveReach_edge
    {w : Wiring} {u : Tongues} {p q : Nat}
    (h : CurveEdge w u p q) : CurveReach w u p q :=
  CurveReach.step CurveReach.refl h

theorem curveReach_trans
    {w : Wiring} {u : Tongues} {p q r : Nat}
    (hpq : CurveReach w u p q) (hqr : CurveReach w u q r) :
    CurveReach w u p r := by
  induction hqr with
  | refl => exact hpq
  | step hreach hedge ih => exact CurveReach.step ih hedge

theorem curveReach_symm
    {w : Wiring} {u : Tongues} {p q : Nat}
    (h : CurveReach w u p q) : CurveReach w u q p := by
  induction h with
  | refl => exact CurveReach.refl
  | @step x y hreach hedge ih =>
      exact curveReach_trans (curveReach_edge (curveEdge_symm hedge)) ih

/-- A selected passage avoiding switch `C` survives a flip at `C`. -/
theorem internalCurveEdge_flip_other
    {u : Tongues} {p q C : Nat}
    (h : InternalCurveEdge u p q) (hpC : p / 3 ≠ C) :
    InternalCurveEdge (flipAt u C) p q := by
  unfold InternalCurveEdge at h ⊢
  exact arrive_flip_other h hpC

/-- If neither endpoint is `C`'s stem, a curve edge survives a flip at `C`.
For an internal edge this follows because every switch passage uses its
stem. -/
theorem curveEdge_flip_stable_away_from_stem
    {w : Wiring} {u : Tongues} {p q C : Nat}
    (hp : p ≠ 3 * C) (hq : q ≠ 3 * C)
    (h : CurveEdge w u p q) :
    CurveEdge w (flipAt u C) p q := by
  rcases h with htrack | hinternal
  · exact Or.inl htrack
  · right
    apply internalCurveEdge_flip_other hinternal
    intro hpC
    have hstem := arrive_stem_endpoint u p
    unfold InternalCurveEdge at hinternal
    rw [hinternal] at hstem
    rcases hstem with hps | hqs
    · apply hp
      simpa [hpC] using hps
    · apply hq
      simpa [hpC] using hqs

/-- If the old curve rooted at `root` does not contain `C`'s stem, flipping
`C` preserves the whole old curve pointwise. -/
theorem curveReach_flip_subset_of_stem_outside
    {w : Wiring} {u : Tongues} {root C : Nat}
    (houtside : ¬ CurveReach w u root (3 * C)) :
    ∀ {p : Nat}, CurveReach w u root p →
      CurveReach w (flipAt u C) root p := by
  intro p hreach
  induction hreach with
  | refl => exact CurveReach.refl
  | @step x y hprefix hedge ih =>
      have hx : x ≠ 3 * C := by
        intro hEq
        apply houtside
        simpa [hEq] using hprefix
      have hy : y ≠ 3 * C := by
        intro hEq
        apply houtside
        simpa [hEq] using (CurveReach.step hprefix hedge)
      exact CurveReach.step ih
        (curveEdge_flip_stable_away_from_stem hx hy hedge)

/-- **Strict train-curve growth at a non-self endpoint pivot.**

Before the pivot, `unmatchedBranch u C` is an endpoint.  If its selected
curve does not already contain the stem `3*C`, then after the pivot:

1. every point of the old curve is still on the new curve; and
2. the stem is on the new curve although it was not on the old one.

This is the precise monotone component-growth invariant behind the
curve-shrinking argument for lazy railway points. -/
theorem unmatched_pivot_strict_curve_growth
    {w : Wiring} (u : Tongues) (C : Nat)
    (houtside : ¬ CurveReach w u (unmatchedBranch u C) (3 * C)) :
    (∀ p, CurveReach w u (unmatchedBranch u C) p →
      CurveReach w (flipAt u C) (unmatchedBranch u C) p) ∧
    CurveReach w (flipAt u C) (unmatchedBranch u C) (3 * C) ∧
    ¬ CurveReach w u (unmatchedBranch u C) (3 * C) := by
  constructor
  · intro p hp
    exact curveReach_flip_subset_of_stem_outside houtside hp
  · constructor
    · apply curveReach_edge
      right
      apply internalCurveEdge_symm
      exact arrive_pivot_back u C
    · exact houtside

end GeneralN
