import TreeCapacitySevenTenths

/-!
# A three-fifths bound from bounded lobe load per tree component

The `7/10` theorem treats every varying lobe-root bit independently of every
ordinary tree marker.  A stronger dynamical statement is suggested by the
edge-reversal geometry: before the Gray trap, one ordinary support-tree
component appears to steer at most two varying lobe roots.

This file isolates the exact arithmetic consequence.  A loaded component is
encoded by `(v,a)`, where

* `v >= 2` is its number of ordinary tree cells;
* `a <= 2` is the number of varying lobe roots charged to it; and
* its code capacity is `2^a * (v-1)`.

The sharp uniform estimate is

    (2^a * (v-1))^5 <= 2^(3*(v+a)).

It is tight at `(v,a)=(3,2)`.  Hence a product of such components, together
with any remaining lobe bits charged to two non-tree cells each, has fifth
power at most `2^(3*C)`.  This is the integer form of the exponential base

    2^(3/5) = 1.515716...

No dynamical load theorem is assumed silently: the final theorem states the
needed profile and cell-budget hypotheses explicitly.
-/

namespace Echo

/-- Capacity of a list of loaded tree components `(tree cells, lobe load)`. -/
def loadedTreeCapacity : List (Nat × Nat) → Nat
  | [] => 1
  | p :: rest =>
      (2^p.2 * (p.1 - 1)) * loadedTreeCapacity rest

/-- Cells consumed by the loaded components, including their charged lobes. -/
def loadedTreeCells : List (Nat × Nat) → Nat
  | [] => 0
  | p :: rest => p.1 + p.2 + loadedTreeCells rest

private theorem loaded_treeFifth_mul (x y : Nat) :
    treeFifth (x*y) = treeFifth x * treeFifth y := by
  unfold treeFifth fourth
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem loaded_treeFifth_two_pow (a : Nat) :
    treeFifth (2^a) = 2^(a+a+a+a+a) := by
  unfold treeFifth fourth
  simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- One tree component carrying at most two varying lobe roots has exponent
at most `3/5` in the combined number of tree and lobe cells. -/
theorem loaded_tree_component_fifth
    {v a : Nat} (hv : 2 ≤ v) (ha : a ≤ 2) :
    treeFifth (2^a * (v-1)) ≤ 2^(3*(v+a)) := by
  obtain ⟨d, rfl⟩ : ∃ d, v = 2+d := ⟨v-2, by omega⟩
  cases d with
  | zero =>
      have haCases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
      rcases haCases with rfl | rfl | rfl <;> decide
  | succ d =>
      cases d with
      | zero =>
          have haCases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
          rcases haCases with rfl | rfl | rfl <;> decide
      | succ d =>
          have hmarker := tree_marker_fifth
            (v := 2 + (d+1+1)) (by omega)
          have hmul :
              treeFifth (2^a) * treeFifth (2 + (d+1+1) - 1) ≤
                2^(a+a+a+a+a) *
                  2^((2 + (d+1+1)) + (2 + (d+1+1))) := by
            exact Nat.mul_le_mul
              (Nat.le_of_eq (loaded_treeFifth_two_pow a)) hmarker
          have hexp :
              (a+a+a+a+a) +
                  ((2 + (d+1+1)) + (2 + (d+1+1))) ≤
                3 * ((2 + (d+1+1)) + a) := by
            omega
          calc
            treeFifth (2^a * (2 + (d+1+1) - 1))
                = treeFifth (2^a) *
                    treeFifth (2 + (d+1+1) - 1) :=
                  loaded_treeFifth_mul _ _
            _ ≤ 2^(a+a+a+a+a) *
                  2^((2 + (d+1+1)) + (2 + (d+1+1))) := hmul
            _ = 2^((a+a+a+a+a) +
                  ((2 + (d+1+1)) + (2 + (d+1+1)))) :=
                  (Nat.pow_add 2 _ _).symm
            _ ≤ 2^(3 * ((2 + (d+1+1)) + a)) :=
                  Nat.pow_le_pow_right (by omega) hexp

/-- Products of loaded components retain the `3/5` exponent. -/
theorem loadedTreeCapacity_fifth :
    ∀ profile : List (Nat × Nat),
      (∀ p ∈ profile, 2 ≤ p.1) →
      (∀ p ∈ profile, p.2 ≤ 2) →
      treeFifth (loadedTreeCapacity profile) ≤
        2^(3 * loadedTreeCells profile) := by
  intro profile
  induction profile with
  | nil =>
      intro _ _
      decide
  | cons p rest ih =>
      rcases p with ⟨v,a⟩
      intro hmin hload
      have hv : 2 ≤ v := hmin (v,a) List.mem_cons_self
      have ha : a ≤ 2 := hload (v,a) List.mem_cons_self
      have hhead := loaded_tree_component_fifth hv ha
      have htail := ih
        (fun q hq => hmin q (List.mem_cons_of_mem _ hq))
        (fun q hq => hload q (List.mem_cons_of_mem _ hq))
      unfold loadedTreeCapacity loadedTreeCells
      calc
        treeFifth ((2^a * (v-1)) * loadedTreeCapacity rest)
            = treeFifth (2^a * (v-1)) *
                treeFifth (loadedTreeCapacity rest) :=
                  loaded_treeFifth_mul _ _
        _ ≤ 2^(3*(v+a)) *
              2^(3 * loadedTreeCells rest) :=
                Nat.mul_le_mul hhead htail
        _ = 2^(3*(v+a) + 3 * loadedTreeCells rest) :=
              (Nat.pow_add 2 _ _).symm
        _ = 2^(3 * (v+a+loadedTreeCells rest)) := by
              congr 1
              omega

/-- Unassigned varying lobe roots cost one bit and are charged to their root
and distinct mouth partner, i.e. two cells per bit. -/
theorem loadedTreeCapacity_with_free_fifth
    (profile : List (Nat × Nat)) (free : Nat)
    (hmin : ∀ p ∈ profile, 2 ≤ p.1)
    (hload : ∀ p ∈ profile, p.2 ≤ 2) :
    treeFifth (2^free * loadedTreeCapacity profile) ≤
      2^(3 * (2*free + loadedTreeCells profile)) := by
  have hp := loadedTreeCapacity_fifth profile hmin hload
  have hpow := loaded_treeFifth_two_pow free
  have hmul :
      treeFifth (2^free) * treeFifth (loadedTreeCapacity profile) ≤
        2^(free+free+free+free+free) *
          2^(3 * loadedTreeCells profile) :=
    Nat.mul_le_mul (Nat.le_of_eq hpow) hp
  have hexp :
      (free+free+free+free+free) +
          3 * loadedTreeCells profile ≤
        3 * (2*free + loadedTreeCells profile) := by
    omega
  calc
    treeFifth (2^free * loadedTreeCapacity profile)
        = treeFifth (2^free) *
            treeFifth (loadedTreeCapacity profile) :=
              loaded_treeFifth_mul _ _
    _ ≤ 2^(free+free+free+free+free) *
          2^(3 * loadedTreeCells profile) := hmul
    _ = 2^((free+free+free+free+free) +
          3 * loadedTreeCells profile) :=
            (Nat.pow_add 2 _ _).symm
    _ ≤ 2^(3 * (2*free + loadedTreeCells profile)) :=
          Nat.pow_le_pow_right (by omega) hexp

/-- **Abstract three-fifths state bound.**

`hcount` is supplied by the existing mixed replay code.  `hcapacity` assigns
its lobe bits to loaded tree components plus `free` star-paired cells.
`hcellBudget` says those charged cells fit inside the represented universe.
The only genuinely new dynamical obligation is constructing a profile whose
per-tree loads are at most two. -/
theorem three_fifths_of_loaded_profile
    (S C free : Nat) (profile : List (Nat × Nat))
    (hcount : S ≤ 2^free * loadedTreeCapacity profile)
    (hmin : ∀ p ∈ profile, 2 ≤ p.1)
    (hload : ∀ p ∈ profile, p.2 ≤ 2)
    (hcellBudget : 2*free + loadedTreeCells profile ≤ C) :
    treeFifth S ≤ 2^(3*C) := by
  have hmono := treeFifth_mono hcount
  have hcap := loadedTreeCapacity_with_free_fifth
    profile free hmin hload
  have hbudget :
      2^(3 * (2*free + loadedTreeCells profile)) ≤ 2^(3*C) :=
    Nat.pow_le_pow_right (by omega)
      (Nat.mul_le_mul_left 3 hcellBudget)
  exact Nat.le_trans hmono (Nat.le_trans hcap hbudget)

end Echo
