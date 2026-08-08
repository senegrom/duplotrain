import SparseCombinatoricsCore

/-!
# Aggregating eighth-power epoch bounds

If every epoch size `s` satisfies `s^8 ≤ X`, then the sum of `K` epoch sizes
satisfies

    (Σ s)^8 ≤ K^8 X.

The proof uses `Σs ≤ K * max(s)` and never extracts an eighth root.  Therefore
linearly many support epochs preserve the strict exponential base and cost only
a polynomial factor.
-/

namespace Echo

/-- Maximum of a natural-number list. -/
def epochMax : List Nat → Nat
  | [] => 0
  | x :: rest => Nat.max x (epochMax rest)

/-- Every member is bounded by the list maximum. -/
theorem mem_le_epochMax {x : Nat} : ∀ {xs : List Nat},
    x ∈ xs → x ≤ epochMax xs := by
  intro xs hx
  induction xs with
  | nil => cases hx
  | cons y rest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

/-- The tail maximum is no larger than the whole maximum. -/
theorem epochMax_tail_le (x : Nat) (xs : List Nat) :
    epochMax xs ≤ epochMax (x :: xs) := by
  exact Nat.le_max_right _ _

/-- Sum bounded by length times maximum. -/
theorem sum_le_length_mul_epochMax : ∀ xs : List Nat,
    xs.sum ≤ xs.length * epochMax xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      have hx : x ≤ epochMax (x :: rest) :=
        Nat.le_max_left _ _
      have htailMax := epochMax_tail_le x rest
      have htail : rest.sum ≤ rest.length * epochMax (x :: rest) :=
        Nat.le_trans ih
          (Nat.mul_le_mul_left rest.length htailMax)
      simp only [List.sum_cons, List.length_cons]
      omega

/-- Monotonicity of the eighth-power helper. -/
theorem sparseCoreEighth_mono {x y : Nat} (h : x ≤ y) :
    sparseCoreEighth x ≤ sparseCoreEighth y := by
  unfold sparseCoreEighth
  have h4 := sparseCore_fourth_mono h
  exact Nat.mul_le_mul h4 h4

/-- Eighth powers distribute over multiplication. -/
theorem sparseCoreEighth_mul (x y : Nat) :
    sparseCoreEighth (x*y) =
      sparseCoreEighth x * sparseCoreEighth y := by
  unfold sparseCoreEighth
  rw [sparseCore_fourth_mul]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The maximum inherits any pointwise eighth-power bound. -/
theorem epochMax_eighth_le
    (xs : List Nat) (X : Nat)
    (h : ∀ x ∈ xs, sparseCoreEighth x ≤ X) :
    sparseCoreEighth (epochMax xs) ≤ X := by
  induction xs with
  | nil =>
      simp [epochMax, sparseCoreEighth, fourth]
  | cons x rest ih =>
      have hx := h x List.mem_cons_self
      have hr : ∀ y ∈ rest, sparseCoreEighth y ≤ X := by
        intro y hy
        exact h y (List.mem_cons_of_mem _ hy)
      have hi := ih hr
      by_cases hxr : x ≤ epochMax rest
      · rw [epochMax, Nat.max_eq_right hxr]
        exact hi
      · have hrx : epochMax rest ≤ x := by omega
        rw [epochMax, Nat.max_eq_left hrx]
        exact hx

/-- **Aggregate a uniform epoch bound.** -/
theorem aggregate_eighth_bound
    (sizes : List Nat) (X : Nat)
    (h : ∀ s ∈ sizes, sparseCoreEighth s ≤ X) :
    sparseCoreEighth sizes.sum ≤
      sparseCoreEighth sizes.length * X := by
  have hsum := sum_le_length_mul_epochMax sizes
  have hp := sparseCoreEighth_mono hsum
  rw [sparseCoreEighth_mul] at hp
  exact Nat.le_trans hp
    (Nat.mul_le_mul_left (sparseCoreEighth sizes.length)
      (epochMax_eighth_le sizes X h))

/-- A bound on the number of epochs replaces the exact list length. -/
theorem aggregate_eighth_bound_of_length
    (sizes : List Nat) (K X : Nat)
    (hlen : sizes.length ≤ K)
    (h : ∀ s ∈ sizes, sparseCoreEighth s ≤ X) :
    sparseCoreEighth sizes.sum ≤ sparseCoreEighth K * X := by
  have hagg := aggregate_eighth_bound sizes X h
  have hk := sparseCoreEighth_mono hlen
  exact Nat.le_trans hagg (Nat.mul_le_mul_right X hk)

/-- Applying the fixed-epoch strict bound to at most `N+1` support epochs. -/
theorem aggregate_support_epoch_bound
    (N : Nat) (sizes : List Nat)
    (hlen : sizes.length ≤ N+1)
    (h : ∀ s ∈ sizes,
      sparseCoreEighth s ≤ 2^(7*N+8)) :
    sparseCoreEighth sizes.sum ≤
      sparseCoreEighth (N+1) * 2^(7*N+8) := by
  exact aggregate_eighth_bound_of_length sizes (N+1)
    (2^(7*N+8)) hlen h

end Echo
