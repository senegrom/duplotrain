import BlockSparseBoundCore

/-!
# Aggregating strict block-sparse epoch bounds

If every epoch size `s` satisfies `s^8 ≤ X`, then the sum of at most `K`
epoch sizes satisfies

    (Σ s)^8 ≤ K^8 X.

Thus linearly many support epochs preserve the strict exponential base and add
only a polynomial factor.
-/

namespace Echo

/-- Maximum of a list. -/
def blockEpochMax : List Nat → Nat
  | [] => 0
  | x :: rest => Nat.max x (blockEpochMax rest)

theorem mem_le_blockEpochMax {x : Nat} : ∀ {xs : List Nat},
    x ∈ xs → x ≤ blockEpochMax xs := by
  intro xs hx
  induction xs with
  | nil => cases hx
  | cons y rest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

/-- Sum is bounded by length times maximum. -/
theorem block_sum_le_length_mul_max : ∀ xs : List Nat,
    xs.sum ≤ xs.length * blockEpochMax xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      have hx : x ≤ blockEpochMax (x :: rest) :=
        Nat.le_max_left _ _
      have hmax : blockEpochMax rest ≤ blockEpochMax (x :: rest) :=
        Nat.le_max_right _ _
      have htail : rest.sum ≤
          rest.length * blockEpochMax (x :: rest) :=
        Nat.le_trans ih (Nat.mul_le_mul_left rest.length hmax)
      simp only [List.sum_cons, List.length_cons]
      omega

/-- Eighth-power monotonicity. -/
theorem blockCoreEighth_mono {x y : Nat} (h : x ≤ y) :
    blockCoreEighth x ≤ blockCoreEighth y := by
  unfold blockCoreEighth
  have h4 := blockCoreFourth_mono h
  exact Nat.mul_le_mul h4 h4

/-- Eighth powers distribute over multiplication. -/
theorem blockCoreEighth_mul (x y : Nat) :
    blockCoreEighth (x*y) =
      blockCoreEighth x * blockCoreEighth y := by
  unfold blockCoreEighth
  rw [blockCoreFourth_mul]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The maximum inherits any uniform eighth-power bound. -/
theorem blockEpochMax_eighth_le
    (xs : List Nat) (X : Nat)
    (h : ∀ x ∈ xs, blockCoreEighth x ≤ X) :
    blockCoreEighth (blockEpochMax xs) ≤ X := by
  induction xs with
  | nil =>
      exact Nat.zero_le _
  | cons x rest ih =>
      have hx := h x List.mem_cons_self
      have hr : ∀ y ∈ rest, blockCoreEighth y ≤ X := by
        intro y hy
        exact h y (List.mem_cons_of_mem _ hy)
      have hi := ih hr
      by_cases hxr : x ≤ blockEpochMax rest
      · rw [blockEpochMax, Nat.max_eq_right hxr]
        exact hi
      · have hrx : blockEpochMax rest ≤ x := by omega
        rw [blockEpochMax, Nat.max_eq_left hrx]
        exact hx

/-- **Aggregate a uniform epoch bound.** -/
theorem block_aggregate_eighth_bound
    (sizes : List Nat) (X : Nat)
    (h : ∀ s ∈ sizes, blockCoreEighth s ≤ X) :
    blockCoreEighth sizes.sum ≤
      blockCoreEighth sizes.length * X := by
  have hsum := block_sum_le_length_mul_max sizes
  have hp := blockCoreEighth_mono hsum
  rw [blockCoreEighth_mul] at hp
  have hmax := blockEpochMax_eighth_le sizes X h
  exact Nat.le_trans hp
    (Nat.mul_le_mul_left (blockCoreEighth sizes.length) hmax)

/-- Replace the exact number of epochs by an upper bound. -/
theorem block_aggregate_eighth_bound_of_length
    (sizes : List Nat) (K X : Nat)
    (hlen : sizes.length ≤ K)
    (h : ∀ s ∈ sizes, blockCoreEighth s ≤ X) :
    blockCoreEighth sizes.sum ≤ blockCoreEighth K * X := by
  have hagg := block_aggregate_eighth_bound sizes X h
  have hk := blockCoreEighth_mono hlen
  exact Nat.le_trans hagg (Nat.mul_le_mul_right X hk)

/-- At most `N+2` pre-tail support pieces plus the absorbing tail. -/
theorem block_global_piece_bound
    (N : Nat) (sizes : List Nat)
    (hlen : sizes.length ≤ N+2)
    (h : ∀ s ∈ sizes,
      blockCoreEighth s ≤ 2^(7*N+18)) :
    blockCoreEighth sizes.sum ≤
      blockCoreEighth (N+2) * 2^(7*N+18) := by
  exact block_aggregate_eighth_bound_of_length sizes (N+2)
    (2^(7*N+18)) hlen h

end Echo
