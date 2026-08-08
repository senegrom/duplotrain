import TreeLobeCode

/-!
# Adding frozen support components to the exact epoch code

A fixed support decomposes into:

* tree components, encoded by their full-edge markers;
* persistent lobe cells, encoded by endpoint bits; and
* components whose register snapshot is constant throughout the epoch.

The third class includes loop-free unicyclic support components: with one
selected endpoint per cell and one edge per cell, no edge is full, so a
support-preserving productive change is impossible without creating a full
edge.  The dynamic freezing theorem is developed separately; here we prove
that a supplied frozen block costs no additional code capacity.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Complete covered cell list. -/
def coveredCells
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes frozen : List Nat) : List Nat :=
  treeCells m e r0 blocks ++ lobeCells m lobes ++ frozen

/-- A block is frozen over the selected epoch. -/
def FrozenOn (frozen : List Nat) : Prop :=
  ∀ i, times i → ∀ j, times j,
    snap m e r0 frozen i = snap m e r0 frozen j

/-- Equal tree/lobe codes replay the complete snapshot when the residual block
is frozen. -/
theorem treeLobeCode_eq_full_snap_eq
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes frozen : List Nat)
    (hfreeze : FrozenOn m e r0 times frozen)
    {i j : Nat}
    (hi : times i) (hj : times j)
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hcode : treeLobeCode m e r0 blocks lobes i =
      treeLobeCode m e r0 blocks lobes j) :
    snap m e r0 (coveredCells m e r0 blocks lobes frozen) j =
      snap m e r0 (coveredCells m e r0 blocks lobes frozen) i := by
  have hvar := treeLobeCode_eq_snap_eq m e r0 hr0 blocks lobes
    hi hj hsupport hcode
  have hfr := hfreeze j hj i hi
  unfold coveredCells snap at hvar hfr ⊢
  simp only [List.map_append]
  rw [hvar, hfr]

private theorem nodup_transfer_full
    {α β : Type} {f : Nat → α} {g : Nat → β} {ks : List Nat}
    (hinj : ∀ i, i ∈ ks → ∀ j, j ∈ ks →
      g i = g j → f i = f j)
    (hnd : (ks.map f).Nodup) :
    (ks.map g).Nodup := by
  induction ks with
  | nil => simp
  | cons k rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      constructor
      · intro hm
        obtain ⟨j, hj, hgj⟩ := List.mem_map.mp hm
        have hfj := hinj k List.mem_cons_self j
          (List.mem_cons_of_mem _ hj) hgj.symm
        exact hnd.1 (List.mem_map.mpr ⟨j, hj, hfj.symm⟩)
      · exact ih
          (fun i hi j hj => hinj i (List.mem_cons_of_mem _ hi)
            j (List.mem_cons_of_mem _ hj)) hnd.2

private theorem nodup_subset_length_full
    {α : Type} [BEq α] [LawfulBEq α]
    {l S : List α}
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ S) :
    l.length ≤ S.length := by
  induction l generalizing S with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ S.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- Distinct complete snapshots still inject into the same tree/lobe code
universe; frozen cells add no multiplicative capacity. -/
theorem tree_lobe_frozen_epoch_count
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes frozen ks : List Nat)
    (hfreeze : FrozenOn m e r0 times frozen)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k ∈ ks, ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hnd : (ks.map (snap m e r0
      (coveredCells m e r0 blocks lobes frozen))).Nodup) :
    ks.length ≤ treeCapacity m e r0 blocks * 2 ^ lobes.length := by
  let code := treeLobeCode m e r0 blocks lobes
  have hcodes : (ks.map code).Nodup :=
    nodup_transfer_full
      (fun i hi j hj hc =>
        (treeLobeCode_eq_full_snap_eq m e r0 hr0 blocks lobes frozen
          hfreeze (hks i hi) (hks j hj)
          (hsupport i hi j hj) hc).symm)
      hnd
  have hsub : ∀ z ∈ ks.map code,
      z ∈ treeLobeUniverse m e r0 blocks lobes := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact treeLobeCode_mem m e r0 blocks lobes k
      (hks k hk) hloop (hocc k hk)
  have hle := nodup_subset_length_full hcodes hsub
  rw [List.length_map, treeLobeUniverse_length] at hle
  exact hle

/-- Strict-base fourth-power estimate with frozen cells included in the total
cell budget. -/
theorem tree_lobe_frozen_fourth_bound
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes frozen ks : List Nat) (C : Nat)
    (hfreeze : FrozenOn m e r0 times frozen)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k ∈ ks, ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hnd : (ks.map (snap m e r0
      (coveredCells m e r0 blocks lobes frozen))).Nodup)
    (hhalf : 2 * lobes.length ≤ C)
    (hcap : treeCapacity m e r0 blocks *
      treeCapacity m e r0 blocks ≤ 2 ^ (C - lobes.length)) :
    fourth ks.length ≤ 2 ^ (3 * C) := by
  have hcount := tree_lobe_frozen_epoch_count m e r0 hr0
    blocks lobes frozen ks hfreeze hks hsupport hloop hocc hnd
  have hfourth := fourth_mono hcount
  exact Nat.le_trans hfourth
    (half_active_fourth_bound C lobes.length
      (treeCapacity m e r0 blocks) hhalf hcap)

/-- Capacity corollary: tree cells may use their intrinsic square-root budget;
all frozen cells are simply spare exponent budget. -/
theorem certified_tree_lobe_frozen_bound
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes frozen ks : List Nat) (C : Nat)
    (hfreeze : FrozenOn m e r0 times frozen)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k ∈ ks, ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hnd : (ks.map (snap m e r0
      (coveredCells m e r0 blocks lobes frozen))).Nodup)
    (hsize : ∀ b ∈ blocks,
      b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ blocks, 2 ≤ b.cells.length)
    (hC : C = treeCellCount m e r0 blocks +
      lobes.length + frozen.length)
    (hhalf : 2 * lobes.length ≤ C) :
    fourth ks.length ≤ 2 ^ (3 * C) := by
  apply tree_lobe_frozen_fourth_bound m e r0 hr0
    blocks lobes frozen ks C hfreeze hks hsupport hloop hocc hnd hhalf
  have htree := treeCapacity_square m e r0 blocks hsize hmin
  have hle : treeCellCount m e r0 blocks ≤ C - lobes.length := by
    omega
  have hpow : 2 ^ (treeCellCount m e r0 blocks) ≤
      2 ^ (C - lobes.length) :=
    Nat.pow_le_pow_right (by omega) hle
  exact Nat.le_trans htree hpow

end Echo
