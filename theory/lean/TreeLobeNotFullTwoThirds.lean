import TreeCapacitySevenTenths

/-!
# A two-thirds bound from excluding fully loaded nontrivial components

A tree component with `v` cells has `v-1` marker positions.  Suppose `a` active
lobe roots are charged to distinct cells of that component.  The joint code
capacity is

    2^a * (v-1).

The local reflector dynamics suggests the following much weaker target than
"at most two loads":

* a two-cell component may carry both loads (the two-reflector trap);
* every component with at least three cells has at least one unloaded cell,
  so `a < v`.

Under exactly those hypotheses,

    (2^a * (v-1))^3 <= 2^(2*(v+a)).

The estimate is tight at `(v,a)=(5,4)`.  Multiplication over components and
star-pair charging of any free lobe bits gives the global integer estimate

    states^3 <= 2^(2*cells),

corresponding to exponential base `2^(2/3) = 1.587401...`.
-/

namespace Echo

/-- Third power. -/
def loadedCube (x : Nat) : Nat := x*x*x

private theorem loadedCube_mul (x y : Nat) :
    loadedCube (x*y) = loadedCube x * loadedCube y := by
  unfold loadedCube
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem loadedCube_mono {x y : Nat} (h : x ≤ y) :
    loadedCube x ≤ loadedCube y := by
  unfold loadedCube
  exact Nat.mul_le_mul (Nat.mul_le_mul h h) h

private theorem loadedCube_two_pow (a : Nat) :
    loadedCube (2^a) = 2^(a+a+a) := by
  unfold loadedCube
  simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- `n^3 <= 2^(n+2)` for every `n >= 4`, written without real arithmetic. -/
private theorem marker_cube_four_plus : ∀ d : Nat,
    loadedCube (4+d) ≤ 2^((4+d)+2) := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      let n := 4+d
      have hn : 4 ≤ n := by omega
      have hsmall : 3*n + 1 ≤ n*n := by
        have h1 : 3*n + 1 ≤ 4*n := by omega
        have h2 : 4*n ≤ n*n := Nat.mul_le_mul_right n hn
        exact Nat.le_trans h1 h2
      have htail :
          3*(n*n) + (3*n+1) ≤ n*n*n := by
        have h1 := Nat.add_le_add_left hsmall (3*(n*n))
        have h4 : 4*(n*n) ≤ n*(n*n) :=
          Nat.mul_le_mul_right (n*n) hn
        calc
          3*(n*n) + (3*n+1) ≤ 3*(n*n) + n*n := h1
          _ = 4*(n*n) := by omega
          _ ≤ n*(n*n) := h4
          _ = n*n*n := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have hexpand : loadedCube (n+1) =
          loadedCube n + (3*(n*n) + (3*n+1)) := by
        unfold loadedCube
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm]
        omega
      have hcube : loadedCube (n+1) ≤ 2 * loadedCube n := by
        rw [hexpand]
        have h := Nat.add_le_add_left htail (loadedCube n)
        unfold loadedCube at h ⊢
        simpa [Nat.two_mul, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using h
      have hdouble : 2 * loadedCube n ≤ 2 * 2^(n+2) :=
        Nat.mul_le_mul_left 2 ih
      have hp : 2 * 2^(n+2) = 2^((n+1)+2) := by
        have hidx : (n+1)+2 = (n+2)+1 := by omega
        rw [hidx, Nat.pow_add_one]
        exact Nat.mul_comm _ _
      have hnext : loadedCube (n+1) ≤ 2^((n+1)+2) := by
        rw [← hp]
        exact Nat.le_trans hcube hdouble
      simpa [n, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnext

/-- Marker cube estimate for every tree component with at least two cells. -/
theorem tree_marker_cube {v : Nat} (hv : 2 ≤ v) :
    loadedCube (v-1) ≤ 2^(v+1) := by
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
              have h := marker_cube_four_plus d
              have hleft : 2 + (d+1+1+1) - 1 = 4+d := by omega
              have hright : 2 + (d+1+1+1) + 1 = (4+d)+2 := by omega
              simpa [hleft, hright] using h

/-- Admissible component loading: size two is allowed two loads; larger
components must have at least one unloaded cell. -/
def NotFullyLoaded (v a : Nat) : Prop :=
  (v = 2 ∧ a ≤ 2) ∨ (3 ≤ v ∧ a < v)

/-- One not-fully-loaded component has exponent at most `2/3`. -/
theorem notFullyLoaded_component_cube
    {v a : Nat} (hload : NotFullyLoaded v a) :
    loadedCube (2^a * (v-1)) ≤ 2^(2*(v+a)) := by
  rcases hload with ⟨rfl, ha⟩ | ⟨hv3, hav⟩
  · have haCases : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    rcases haCases with rfl | rfl | rfl <;> decide
  · have hv : 2 ≤ v := by omega
    have hm := tree_marker_cube hv
    have hmul :
        loadedCube (2^a) * loadedCube (v-1) ≤
          2^(a+a+a) * 2^(v+1) :=
      Nat.mul_le_mul (Nat.le_of_eq (loadedCube_two_pow a)) hm
    have hexp : (a+a+a) + (v+1) ≤ 2*(v+a) := by omega
    calc
      loadedCube (2^a * (v-1))
          = loadedCube (2^a) * loadedCube (v-1) :=
              loadedCube_mul _ _
      _ ≤ 2^(a+a+a) * 2^(v+1) := hmul
      _ = 2^((a+a+a)+(v+1)) := (Nat.pow_add 2 _ _).symm
      _ ≤ 2^(2*(v+a)) := Nat.pow_le_pow_right (by omega) hexp

/-- Product capacity and cell count of a loaded-component profile. -/
def notFullLoadedCapacity : List (Nat × Nat) → Nat
  | [] => 1
  | p :: rest =>
      (2^p.2 * (p.1-1)) * notFullLoadedCapacity rest

def notFullLoadedCells : List (Nat × Nat) → Nat
  | [] => 0
  | p :: rest => p.1 + p.2 + notFullLoadedCells rest

/-- Products of admissible components retain the `2/3` exponent. -/
theorem notFullLoadedCapacity_cube :
    ∀ profile : List (Nat × Nat),
      (∀ p ∈ profile, NotFullyLoaded p.1 p.2) →
      loadedCube (notFullLoadedCapacity profile) ≤
        2^(2 * notFullLoadedCells profile) := by
  intro profile
  induction profile with
  | nil =>
      intro _
      decide
  | cons p rest ih =>
      rcases p with ⟨v,a⟩
      intro hall
      have hhead := notFullyLoaded_component_cube
        (hall (v,a) List.mem_cons_self)
      have htail := ih
        (fun q hq => hall q (List.mem_cons_of_mem _ hq))
      unfold notFullLoadedCapacity notFullLoadedCells
      calc
        loadedCube ((2^a * (v-1)) * notFullLoadedCapacity rest)
            = loadedCube (2^a * (v-1)) *
                loadedCube (notFullLoadedCapacity rest) :=
                  loadedCube_mul _ _
        _ ≤ 2^(2*(v+a)) *
              2^(2 * notFullLoadedCells rest) :=
                Nat.mul_le_mul hhead htail
        _ = 2^(2*(v+a) + 2 * notFullLoadedCells rest) :=
              (Nat.pow_add 2 _ _).symm
        _ = 2^(2 * (v+a+notFullLoadedCells rest)) := by
              congr 1
              omega

/-- Free lobe bits charged to two cells each also satisfy the `2/3` budget. -/
theorem notFullLoaded_with_free_cube
    (profile : List (Nat × Nat)) (free : Nat)
    (hall : ∀ p ∈ profile, NotFullyLoaded p.1 p.2) :
    loadedCube (2^free * notFullLoadedCapacity profile) ≤
      2^(2 * (2*free + notFullLoadedCells profile)) := by
  have hp := notFullLoadedCapacity_cube profile hall
  have hmul :
      loadedCube (2^free) * loadedCube (notFullLoadedCapacity profile) ≤
        2^(free+free+free) *
          2^(2 * notFullLoadedCells profile) :=
    Nat.mul_le_mul (Nat.le_of_eq (loadedCube_two_pow free)) hp
  have hexp :
      (free+free+free) + 2 * notFullLoadedCells profile ≤
        2 * (2*free + notFullLoadedCells profile) := by omega
  calc
    loadedCube (2^free * notFullLoadedCapacity profile)
        = loadedCube (2^free) *
            loadedCube (notFullLoadedCapacity profile) :=
              loadedCube_mul _ _
    _ ≤ 2^(free+free+free) *
          2^(2 * notFullLoadedCells profile) := hmul
    _ = 2^((free+free+free) +
          2 * notFullLoadedCells profile) :=
            (Nat.pow_add 2 _ _).symm
    _ ≤ 2^(2 * (2*free + notFullLoadedCells profile)) :=
          Nat.pow_le_pow_right (by omega) hexp

/-- **Abstract two-thirds state bound.** -/
theorem two_thirds_of_not_fully_loaded_profile
    (S C free : Nat) (profile : List (Nat × Nat))
    (hcount : S ≤ 2^free * notFullLoadedCapacity profile)
    (hall : ∀ p ∈ profile, NotFullyLoaded p.1 p.2)
    (hcellBudget : 2*free + notFullLoadedCells profile ≤ C) :
    loadedCube S ≤ 2^(2*C) := by
  have hmono := loadedCube_mono hcount
  have hcap := notFullLoaded_with_free_cube profile free hall
  have hbudget :
      2^(2 * (2*free + notFullLoadedCells profile)) ≤ 2^(2*C) :=
    Nat.pow_le_pow_right (by omega)
      (Nat.mul_le_mul_left 2 hcellBudget)
  exact Nat.le_trans hmono (Nat.le_trans hcap hbudget)

end Echo
