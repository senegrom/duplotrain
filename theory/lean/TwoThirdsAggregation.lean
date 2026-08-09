import LoadedTreeGroupsWithFreeTwoThirds
import BlockEpochAggregation

/-!
# Aggregating the two-thirds component bound

A uniform fixed-support estimate

    s^3 <= X

survives summation over at most `K` pieces as

    (sum s)^3 <= K^3 * X.

The support-epoch partition, current-entry fibres and physical cascade-prefix
fibres therefore preserve the exponential base `2^(2/3)` and add only the
same polynomial factors as the earlier strict-base bounds.
-/

namespace Echo

private theorem cube_mul_aggregation (x y : Nat) :
    loadedCube (x*y) = loadedCube x * loadedCube y := by
  unfold loadedCube
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem cube_mono_aggregation {x y : Nat} (h : x ≤ y) :
    loadedCube x ≤ loadedCube y := by
  unfold loadedCube
  exact Nat.mul_le_mul (Nat.mul_le_mul h h) h

/-- A list maximum inherits a uniform cube bound. -/
theorem blockEpochMax_cube_le
    (xs : List Nat) (X : Nat)
    (h : ∀ x ∈ xs, loadedCube x ≤ X) :
    loadedCube (blockEpochMax xs) ≤ X := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      have hx := h x List.mem_cons_self
      have hr : ∀ y ∈ rest, loadedCube y ≤ X := by
        intro y hy
        exact h y (List.mem_cons_of_mem _ hy)
      have hi := ih hr
      by_cases hxr : x ≤ blockEpochMax rest
      · simpa [blockEpochMax, Nat.max_eq_right hxr] using hi
      · have hrx : blockEpochMax rest ≤ x := by omega
        simpa [blockEpochMax, Nat.max_eq_left hrx] using hx

/-- **Aggregate a uniform cube bound.** -/
theorem aggregate_cube_bound
    (sizes : List Nat) (X : Nat)
    (h : ∀ s ∈ sizes, loadedCube s ≤ X) :
    loadedCube sizes.sum ≤ loadedCube sizes.length * X := by
  have hsum := block_sum_le_length_mul_max sizes
  have hp := cube_mono_aggregation hsum
  rw [cube_mul_aggregation] at hp
  have hmax := blockEpochMax_cube_le sizes X h
  exact Nat.le_trans hp
    (Nat.mul_le_mul_left (loadedCube sizes.length) hmax)

/-- Replace the exact number of pieces by an upper bound. -/
theorem aggregate_cube_bound_of_length
    (sizes : List Nat) (K X : Nat)
    (hlen : sizes.length ≤ K)
    (h : ∀ s ∈ sizes, loadedCube s ≤ X) :
    loadedCube sizes.sum ≤ loadedCube K * X := by
  have hagg := aggregate_cube_bound sizes X h
  have hk := cube_mono_aggregation hlen
  exact Nat.le_trans hagg (Nat.mul_le_mul_right X hk)

/-- At most `N+2` support pieces, including a possible four-state absorbed
tail.  The extra six exponent bits accommodate `4^3 = 2^6`. -/
theorem twoThirds_global_piece_bound
    (N : Nat) (sizes : List Nat)
    (hlen : sizes.length ≤ N+2)
    (h : ∀ s ∈ sizes, loadedCube s ≤ 2^(2*N+6)) :
    loadedCube sizes.sum ≤
      loadedCube (N+2) * 2^(2*N+6) := by
  exact aggregate_cube_bound_of_length sizes (N+2)
    (2^(2*N+6)) hlen h

/-- Current-entry and cascade-prefix factors change only the polynomial
prefactor. -/
theorem twoThirds_physical_polynomial_bound
    (N physical abstract : Nat)
    (hphysical : physical ≤
      (2 * (N+1)) * ((2*N) * abstract))
    (habstract : loadedCube abstract ≤
      loadedCube (N+2) * 2^(2*N+6)) :
    loadedCube physical ≤
      loadedCube (2 * (N+1)) *
        (loadedCube (2*N) *
          (loadedCube (N+2) * 2^(2*N+6))) := by
  calc
    loadedCube physical ≤
        loadedCube ((2 * (N+1)) * ((2*N) * abstract)) :=
          cube_mono_aggregation hphysical
    _ = loadedCube (2 * (N+1)) *
          (loadedCube (2*N) * loadedCube abstract) := by
            rw [cube_mul_aggregation
                (2 * (N+1)) ((2*N) * abstract),
              cube_mul_aggregation (2*N) abstract]
    _ ≤ loadedCube (2 * (N+1)) *
          (loadedCube (2*N) *
            (loadedCube (N+2) * 2^(2*N+6))) :=
          Nat.mul_le_mul_left (loadedCube (2 * (N+1)))
            (Nat.mul_le_mul_left (loadedCube (2*N)) habstract)

end Echo
