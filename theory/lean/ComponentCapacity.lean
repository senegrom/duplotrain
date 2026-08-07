import ThreeQuarterArithmetic

/-!
# Elementary capacity bounds for pseudoforest components

For a fixed occupied support:

* a tree component on `v` cells is determined by its unique full edge, hence
  has capacity `v-1`;
* a loop-free unicyclic component has at most two orientations.

The graph-theoretic coding is developed separately.  This file proves the
numerical estimate shared by both component types:

    capacity² ≤ 2^v.
-/

namespace Echo

/-- The standard elementary inequality `n² ≤ 2^n` from `n=4` onward. -/
private theorem square_four_plus : ∀ d : Nat,
    (4+d)*(4+d) ≤ 2^(4+d) := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      let n := 4+d
      have hn : 3 ≤ n := by omega
      have hlin : 2*n + 1 ≤ n*n := by
        have h1 : 2*n + 1 ≤ 3*n := by omega
        have h2 : 3*n ≤ n*n := Nat.mul_le_mul_right n hn
        exact h1.trans h2
      have hexpand : (n+1)*(n+1) = n*n + (2*n+1) := by
        simp [Nat.add_mul, Nat.mul_add, Nat.two_mul]
        omega
      have hsquare : (n+1)*(n+1) ≤ 2*(n*n) := by
        rw [hexpand]
        have h := Nat.add_le_add_left hlin (n*n)
        simpa [Nat.two_mul] using h
      have hdouble : 2*(n*n) ≤ 2*(2^n) :=
        Nat.mul_le_mul_left 2 ih
      have hp : 2*(2^n) = 2^(n+1) := by
        rw [Nat.pow_add_one]
        exact Nat.mul_comm _ _
      have hnext : (n+1)*(n+1) ≤ 2^(n+1) := by
        rw [← hp]
        exact hsquare.trans hdouble
      simpa [n, Nat.add_assoc] using hnext

/-- A tree component with `v ≥ 2` cells has `v-1` possible full-edge markers,
and the square of this capacity is at most `2^v`. -/
theorem tree_marker_square {v : Nat} (hv : 2 ≤ v) :
    (v-1)*(v-1) ≤ 2^v := by
  obtain ⟨d, rfl⟩ : ∃ d, v = 2+d := ⟨v-2, by omega⟩
  cases d with
  | zero => decide
  | succ d =>
      cases d with
      | zero => decide
      | succ d =>
          cases d with
          | zero => decide
          | succ d =>
              have h := square_four_plus d
              have hp : 2^(4+d) ≤ 2^(5+d) :=
                Nat.pow_le_pow_right (by omega) (by omega)
              simpa [Nat.add_assoc] using h.trans hp

/-- The two possible orientations of a loop-free cycle component obey the
same square-capacity bound. -/
theorem cycle_orientation_square {v : Nat} (hv : 2 ≤ v) :
    2*2 ≤ 2^v := by
  exact two_orientation_square hv

/-- A tree-component size list gives a valid square-root profile. -/
def treeProfile : List Nat → List (Nat × Nat)
  | [] => []
  | v :: vs => (v, v-1) :: treeProfile vs

theorem treeProfile_cells : ∀ vs,
    profileCells (treeProfile vs) = vs.sum := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v rest ih =>
      simp [treeProfile, profileCells, ih]

theorem treeProfile_capacity_square (vs : List Nat)
    (hv : ∀ v ∈ vs, 2 ≤ v) :
    profileCapacity (treeProfile vs) *
      profileCapacity (treeProfile vs) ≤ 2^(vs.sum) := by
  have hprofile := profile_capacity_square (treeProfile vs) (by
    intro p hp
    induction vs with
    | nil => cases hp
    | cons v rest ih =>
        simp only [treeProfile, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact tree_marker_square (hv v List.mem_cons_self)
        · exact ih
            (fun w hw => hv w (List.mem_cons_of_mem _ hw)) hp)
  rw [treeProfile_cells] at hprofile
  exact hprofile

end Echo
