import TreeLobeLoadBound
import MixedEpochBound

/-!
# A dynamics-coupled two-thirds fixed-support bound

The preceding files prove the local fact that an ordinary support-tree
component cannot be fully loaded by persistent varying lobe reflectors.  This
file assembles those local statements into one mixed epoch code.

A `LoadedTreeGroup` consists of

* one ordinary support-tree component; and
* the active lobe-forest components whose mouth partners are charged to that
  tree.

Each group contributes code capacity

    (tree marker positions) * 2^(charged lobe roots)
      = (v-1) * 2^a.

`supportTree_lobe_load_notFullyLoaded` proves dynamically that `(v,a)` is
`NotFullyLoaded`.  Multiplication over groups and the arithmetic theorem in
`TreeLobeNotFullTwoThirds` then give

    states^3 <= 2^(2*cells).

The only global combinatorial input retained here is the cell-budget inequality
saying that the charged tree cells and lobe roots are counted without overlap
inside the represented cell universe.  A canonical component partition will
supply that bookkeeping.
-/

namespace Echo

/-- One ordinary support tree together with the active lobe forests charged to
its cells. -/
structure LoadedTreeGroup
    (m : Machine) (e r0 : Nat → Nat) (I J : Nat) where
  tree : SupportTreeEpoch m e r0 (fun k => I ≤ k ∧ k ≤ J)
  lobes : List (SupportLobeForestEpoch m e r0
    (fun k => I ≤ k ∧ k ≤ J))
  min_cells : 2 ≤ tree.cells.length
  roots_nodup : (lobeForestRoots m e r0 lobes).Nodup
  partners_in_tree : ∀ B ∈ lobes, m.star (B.root m) ∈ tree.cells
  roots_outside_tree : ∀ B ∈ lobes, B.root m ∉ tree.cells
  varying : ∀ B ∈ lobes,
    VariesOnInterval m e r0 I J (B.root m)

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {I J : Nat}

/-- Certified tree blocks of all loaded groups. -/
noncomputable def loadedGroupTreeBlocks
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (groups : List (LoadedTreeGroup m e r0 I J)) :
    List (TreeBlockCert m e r0 (fun k => I ≤ k ∧ k ≤ J)) :=
  groups.map (fun G => G.tree.toTreeBlock m e r0 hrun hr0)

/-- Flattened active-lobe list. -/
def loadedGroupLobes
    (groups : List (LoadedTreeGroup m e r0 I J)) :
    List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)) :=
  groups.flatMap (fun G => G.lobes)

/-- Arithmetic profile `(tree cells, charged lobe roots)`. -/
def loadedGroupProfile
    (groups : List (LoadedTreeGroup m e r0 I J)) :
    List (Nat × Nat) :=
  groups.map (fun G => (G.tree.cells.length, G.lobes.length))

/-- Every profile entry satisfies the dynamically proved non-full-load law. -/
theorem loadedGroupProfile_notFullyLoaded
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (groups : List (LoadedTreeGroup m e r0 I J)) :
    ∀ p ∈ loadedGroupProfile m e r0 groups,
      NotFullyLoaded p.1 p.2 := by
  intro p hp
  unfold loadedGroupProfile at hp
  obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hp
  exact supportTree_lobe_load_notFullyLoaded m e r0 hrun hr0
    G.tree G.lobes G.min_cells G.roots_nodup
    G.partners_in_tree G.roots_outside_tree G.varying

/-- Flattening preserves the total number of lobe coordinates. -/
theorem loadedGroupLobes_length :
    ∀ groups : List (LoadedTreeGroup m e r0 I J),
      (loadedGroupLobes m e r0 groups).length =
        (groups.map (fun G => G.lobes.length)).sum := by
  intro groups
  induction groups with
  | nil => rfl
  | cons G rest ih =>
      unfold loadedGroupLobes
      simp only [List.flatMap_cons, List.length_append,
        List.map_cons, List.sum_cons]
      change G.lobes.length +
          (loadedGroupLobes m e r0 rest).length =
        G.lobes.length +
          (rest.map (fun H => H.lobes.length)).sum
      rw [ih]

/-- The loaded-profile capacity is exactly the ordinary tree-marker capacity
multiplied by one Boolean coordinate for every charged lobe root. -/
theorem loadedGroupProfile_capacity_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) :
    ∀ groups : List (LoadedTreeGroup m e r0 I J),
      notFullLoadedCapacity (loadedGroupProfile m e r0 groups) =
        treeCapacity m e r0
          (loadedGroupTreeBlocks m e r0 hrun hr0 groups) *
        2^((loadedGroupLobes m e r0 groups).length) := by
  intro groups
  induction groups with
  | nil =>
      rfl
  | cons G rest ih =>
      have hedge : G.tree.edges.length = G.tree.cells.length - 1 := by
        omega
      unfold loadedGroupProfile loadedGroupTreeBlocks loadedGroupLobes
      simp only [List.map_cons, List.flatMap_cons,
        notFullLoadedCapacity, treeCapacity, List.length_append]
      change
        (2^G.lobes.length * (G.tree.cells.length - 1)) *
            notFullLoadedCapacity (loadedGroupProfile m e r0 rest) =
          G.tree.edges.length *
            treeCapacity m e r0
              (loadedGroupTreeBlocks m e r0 hrun hr0 rest) *
            2^(G.lobes.length +
              (loadedGroupLobes m e r0 rest).length)
      rw [ih, hedge, Nat.pow_add]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- The profile cell count is the sum of tree cells and charged lobe roots. -/
theorem loadedGroupProfile_cells :
    ∀ groups : List (LoadedTreeGroup m e r0 I J),
      notFullLoadedCells (loadedGroupProfile m e r0 groups) =
        (groups.map (fun G => G.tree.cells.length)).sum +
          (loadedGroupLobes m e r0 groups).length := by
  intro groups
  induction groups with
  | nil => rfl
  | cons G rest ih =>
      unfold loadedGroupProfile loadedGroupLobes
      simp only [List.map_cons, List.flatMap_cons,
        notFullLoadedCells, List.sum_cons, List.length_append]
      change
        G.tree.cells.length + G.lobes.length +
            notFullLoadedCells (loadedGroupProfile m e r0 rest) =
          G.tree.cells.length +
              (rest.map (fun H => H.tree.cells.length)).sum +
            (G.lobes.length +
              (loadedGroupLobes m e r0 rest).length)
      rw [ih]
      omega

/-- **Dynamics-coupled `2/3` epoch bound.**

Unlike the earlier `7/10` theorem, the improved exponent is not obtained from
an assumed numerical load inequality.  Every component's load restriction is
proved from the echo dynamics.  The remaining `hcellBudget` is purely the
finite partition bookkeeping. -/
theorem loaded_groups_epoch_two_thirds
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (groups : List (LoadedTreeGroup m e r0 I J))
    (fixed allCells ks : List Nat)
    (hks : ∀ k ∈ ks, I ≤ k ∧ k ≤ J)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfixed : ∀ i ∈ ks, ∀ j ∈ ks, ∀ c ∈ fixed,
      reg m e r0 i c = reg m e r0 j c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0
          (loadedGroupTreeBlocks m e r0 hrun hr0 groups) ∨
      c ∈ lobeForestCells m e r0
          (loadedGroupLobes m e r0 groups) ∨
      c ∈ fixed)
    (hcellBudget :
      notFullLoadedCells (loadedGroupProfile m e r0 groups) ≤
        allCells.length)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    loadedCube ks.length ≤ 2^(2*allCells.length) := by
  let blocks := loadedGroupTreeBlocks m e r0 hrun hr0 groups
  let lobes := loadedGroupLobes m e r0 groups
  let profile := loadedGroupProfile m e r0 groups
  have hcount := mixed_epoch_count m e r0 hrun hr0
    blocks lobes fixed allCells ks hks hsupport hfixed hcover hnd
  have hcapacity := loadedGroupProfile_capacity_eq
    m e r0 hrun hr0 groups
  have hcountProfile : ks.length ≤ notFullLoadedCapacity profile := by
    change ks.length ≤
      notFullLoadedCapacity (loadedGroupProfile m e r0 groups)
    rw [hcapacity]
    exact hcount
  have hall : ∀ p ∈ profile, NotFullyLoaded p.1 p.2 := by
    dsimp [profile]
    exact loadedGroupProfile_notFullyLoaded m e r0 hrun hr0 groups
  exact two_thirds_of_not_fully_loaded_profile
    ks.length allCells.length 0 profile
    (by simpa using hcountProfile)
    hall
    (by simpa [profile] using hcellBudget)

end Echo
