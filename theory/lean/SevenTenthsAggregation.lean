import TreeCapacitySevenTenths
import BlockEpochAggregation

/-!
# Aggregating the seven-tenths component bound

A uniform bound

    s^10 ≤ X

for each fixed-support piece survives summation over `K` pieces as

    (sum s)^10 ≤ K^10 * X.

Consequently the support-weight, current-entry and physical cascade-prefix
partitions add only the same polynomial factors as before.  Once the canonical
support-component decomposition is supplied, the complete physical bound has
asymptotic form

    O(N^3 * 2^(7*N/10)).
-/

namespace Echo

private theorem treeTenth_mul_aggregation (x y : Nat) :
    treeTenth (x*y) = treeTenth x * treeTenth y := by
  unfold treeTenth treeFifth fourth
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- The maximum of a list inherits a uniform tenth-power bound. -/
theorem blockEpochMax_tenth_le
    (xs : List Nat) (X : Nat)
    (h : ∀ x ∈ xs, treeTenth x ≤ X) :
    treeTenth (blockEpochMax xs) ≤ X := by
  induction xs with
  | nil =>
      exact Nat.zero_le _
  | cons x rest ih =>
      have hx := h x List.mem_cons_self
      have hr : ∀ y ∈ rest, treeTenth y ≤ X := by
        intro y hy
        exact h y (List.mem_cons_of_mem _ hy)
      have hi := ih hr
      by_cases hxr : x ≤ blockEpochMax rest
      · simpa [blockEpochMax, Nat.max_eq_right hxr] using hi
      · have hrx : blockEpochMax rest ≤ x := by omega
        simpa [blockEpochMax, Nat.max_eq_left hrx] using hx

/-- **Aggregate a uniform tenth-power epoch bound.** -/
theorem aggregate_tenth_bound
    (sizes : List Nat) (X : Nat)
    (h : ∀ s ∈ sizes, treeTenth s ≤ X) :
    treeTenth sizes.sum ≤ treeTenth sizes.length * X := by
  have hsum := block_sum_le_length_mul_max sizes
  have hp := treeTenth_mono hsum
  rw [treeTenth_mul_aggregation] at hp
  have hmax := blockEpochMax_tenth_le sizes X h
  exact Nat.le_trans hp
    (Nat.mul_le_mul_left (treeTenth sizes.length) hmax)

/-- Replace the exact number of pieces by an upper bound. -/
theorem aggregate_tenth_bound_of_length
    (sizes : List Nat) (K X : Nat)
    (hlen : sizes.length ≤ K)
    (h : ∀ s ∈ sizes, treeTenth s ≤ X) :
    treeTenth sizes.sum ≤ treeTenth K * X := by
  have hagg := aggregate_tenth_bound sizes X h
  have hk := treeTenth_mono hlen
  exact Nat.le_trans hagg (Nat.mul_le_mul_right X hk)

/-- A convenient global form.  The extra exponent `20` accommodates a
four-state absorbed tail, because `4^10 = 2^20`. -/
theorem sevenTenths_global_piece_bound
    (N : Nat) (sizes : List Nat)
    (hlen : sizes.length ≤ N+2)
    (h : ∀ s ∈ sizes, treeTenth s ≤ 2^(7*N+20)) :
    treeTenth sizes.sum ≤
      treeTenth (N+2) * 2^(7*N+20) := by
  exact aggregate_tenth_bound_of_length sizes (N+2)
    (2^(7*N+20)) hlen h

/-- Multiplying by the current-entry and physical prefix factors changes only
the polynomial prefactor. -/
set_option maxHeartbeats 800000 in
theorem sevenTenths_physical_polynomial_bound
    (N physical abstract : Nat)
    (hphysical : physical ≤
      (2 * (N+1)) * ((2*N) * abstract))
    (habstract : treeTenth abstract ≤
      treeTenth (N+2) * 2^(7*N+20)) :
    treeTenth physical ≤
      treeTenth (2 * (N+1)) *
        (treeTenth (2*N) *
          (treeTenth (N+2) * 2^(7*N+20))) := by
  have hmono := treeTenth_mono hphysical
  rw [treeTenth_mul_aggregation,
    treeTenth_mul_aggregation] at hmono
  exact Nat.le_trans hmono
    (Nat.mul_le_mul_left (treeTenth (2 * (N+1)))
      (Nat.mul_le_mul_left (treeTenth (2*N)) habstract))

end Echo
