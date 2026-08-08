import TreeReplay

/-!
# Coding all tree components in a fixed-support epoch

A `TreeBlockCert` packages one support component:

* its cells and physical edge representatives;
* the full edge chosen at every time in an epoch; and
* a finite `RootedCells` certificate showing that all registers point toward
  that full edge.

The vector of full-edge representatives is a complete code for the tree part
of the register snapshot.  Its universe has size equal to the product of the
component edge counts.  If a component on `v` cells has `v-1` edges, the square
of the total code capacity is at most `2^(number of tree cells)`.
-/

namespace Echo

structure TreeBlockCert
    (m : Machine) (e r0 : Nat → Nat) (times : Nat → Prop) where
  cells : List Nat
  edges : List Nat
  fullAt : Nat → Nat
  full_mem : ∀ k, times k → fullAt k ∈ edges
  full_full : ∀ k, times k → Full m e r0 k (fullAt k)
  rooted : ∀ k, times k → RootedCells m e r0 k (fullAt k) cells

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Cells covered by a list of tree blocks. -/
def treeCells (blocks : List (TreeBlockCert m e r0 times)) : List Nat :=
  blocks.flatMap (fun b => b.cells)

/-- Full-edge vector at one time. -/
def treeCode (blocks : List (TreeBlockCert m e r0 times))
    (k : Nat) : List Nat :=
  blocks.map (fun b => b.fullAt k)

/-- Cartesian product of the block edge lists. -/
def treeCodeUniverse :
    List (TreeBlockCert m e r0 times) → List (List Nat)
  | [] => [[]]
  | b :: rest =>
      b.edges.flatMap (fun f =>
        (treeCodeUniverse rest).map (fun tail => f :: tail))

/-- Product of component edge counts. -/
def treeCapacity : List (TreeBlockCert m e r0 times) → Nat
  | [] => 1
  | b :: rest => b.edges.length * treeCapacity rest

private theorem treeRect_length (xs : List Nat)
    (tails : List (List Nat)) :
    (xs.flatMap (fun x => tails.map (fun tail => x :: tail))).length
      = xs.length * tails.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- The Cartesian code universe has the expected product size. -/
theorem treeCodeUniverse_length :
    ∀ blocks : List (TreeBlockCert m e r0 times),
      (treeCodeUniverse m e r0 blocks).length =
        treeCapacity m e r0 blocks := by
  intro blocks
  induction blocks with
  | nil => rfl
  | cons b rest ih =>
      unfold treeCodeUniverse treeCapacity
      rw [treeRect_length, ih]

/-- Every certified code vector belongs to the Cartesian universe. -/
theorem treeCode_mem :
    ∀ (blocks : List (TreeBlockCert m e r0 times)) (k : Nat),
      times k →
      treeCode m e r0 blocks k ∈ treeCodeUniverse m e r0 blocks := by
  intro blocks
  induction blocks with
  | nil =>
      intro k _
      exact List.mem_cons_self
  | cons b rest ih =>
      intro k hk
      unfold treeCode treeCodeUniverse
      apply List.mem_flatMap.mpr
      refine ⟨b.fullAt k, b.full_mem k hk, ?_⟩
      exact List.mem_map.mpr
        ⟨treeCode m e r0 rest k, ih k hk, rfl⟩

/-- Equal full-edge vectors replay the whole tree-part snapshot. -/
theorem treeCode_eq_snap_eq
    (hr0 : ∀ c, m.cellOf (r0 c) = c) :
    ∀ (blocks : List (TreeBlockCert m e r0 times)) {i j : Nat},
      times i → times j →
      (∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s) →
      treeCode m e r0 blocks i = treeCode m e r0 blocks j →
      snap m e r0 (treeCells m e r0 blocks) j =
        snap m e r0 (treeCells m e r0 blocks) i := by
  intro blocks
  induction blocks with
  | nil =>
      intro i j hi hj hs hc
      rfl
  | cons b rest ih =>
      intro i j hi hj hsupport hcode
      have hpair : b.fullAt i = b.fullAt j ∧
          treeCode m e r0 rest i = treeCode m e r0 rest j := by
        change b.fullAt i :: treeCode m e r0 rest i =
          b.fullAt j :: treeCode m e r0 rest j at hcode
        exact List.cons.inj hcode
      have hhead : snap m e r0 b.cells j = snap m e r0 b.cells i := by
        exact rootedCells_sameEdge_replay m e r0 hr0 b.cells
          hsupport (b.full_full i hi) (b.full_full j hj)
          (Or.inl hpair.1.symm) (b.rooted i hi)
      have htail := ih hi hj hsupport hpair.2
      unfold treeCells at htail ⊢
      simp only [List.flatMap_cons]
      unfold snap at hhead htail ⊢
      simp only [List.map_append]
      rw [hhead, htail]

private theorem nodup_transfer_tree
    {f g : Nat → List Nat} {ks : List Nat}
    (hinj : ∀ i, i ∈ ks → ∀ j, j ∈ ks → g i = g j → f i = f j)
    (hnd : (ks.map f).Nodup) : (ks.map g).Nodup := by
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

private theorem nodup_subset_length_lists
    {l S : List (List Nat)}
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

/-- **Finite tree-epoch count.**  Pairwise-distinct tree snapshots inject into
the Cartesian full-edge code universe. -/
theorem tree_epoch_count
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (ks : List Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hnd : (ks.map (snap m e r0 (treeCells m e r0 blocks))).Nodup) :
    ks.length ≤ treeCapacity m e r0 blocks := by
  have hcodes : (ks.map (treeCode m e r0 blocks)).Nodup :=
    nodup_transfer_tree
      (fun i hi j hj hc =>
        (treeCode_eq_snap_eq m e r0 hr0 blocks
          (hks i hi) (hks j hj) (hsupport i hi j hj) hc).symm)
      hnd
  have hsub : ∀ z ∈ ks.map (treeCode m e r0 blocks),
      z ∈ treeCodeUniverse m e r0 blocks := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact treeCode_mem m e r0 blocks k (hks k hk)
  have hle := nodup_subset_length_lists hcodes hsub
  rw [List.length_map, treeCodeUniverse_length] at hle
  exact hle

/-- Total cells in the block list. -/
def treeCellCount : List (TreeBlockCert m e r0 times) → Nat
  | [] => 0
  | b :: rest => b.cells.length + treeCellCount rest

/-- If every block is a nontrivial tree (`edges = cells - 1`), the square of
the total marker capacity is at most `2^(tree cells)`. -/
theorem treeCapacity_square
    (blocks : List (TreeBlockCert m e r0 times))
    (hsize : ∀ b ∈ blocks, b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ blocks, 2 ≤ b.cells.length) :
    treeCapacity m e r0 blocks * treeCapacity m e r0 blocks ≤
      2^(treeCellCount m e r0 blocks) := by
  induction blocks with
  | nil => simp [treeCapacity, treeCellCount]
  | cons b rest ih =>
      have hbsize := hsize b List.mem_cons_self
      have hbmin := hmin b List.mem_cons_self
      have hbedge : b.edges.length = b.cells.length - 1 := by omega
      have hbcap : b.edges.length * b.edges.length ≤
          2^(b.cells.length) := by
        rw [hbedge]
        exact tree_marker_square hbmin
      have htail := ih
        (fun x hx => hsize x (List.mem_cons_of_mem _ hx))
        (fun x hx => hmin x (List.mem_cons_of_mem _ hx))
      unfold treeCapacity treeCellCount
      calc
        (b.edges.length * treeCapacity m e r0 rest) *
            (b.edges.length * treeCapacity m e r0 rest)
            = (b.edges.length*b.edges.length) *
              (treeCapacity m e r0 rest * treeCapacity m e r0 rest) := by
                simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ 2^(b.cells.length) *
              2^(treeCellCount m e r0 rest) :=
                Nat.mul_le_mul hbcap htail
        _ = 2^(b.cells.length + treeCellCount m e r0 rest) :=
              (Nat.pow_add 2 _ _).symm

end Echo
