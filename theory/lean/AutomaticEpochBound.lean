import AutomaticCycleFixed

/-!
# Automatic fixed-support coding from component blocks

This module assembles the local component theorems into the code expected by
`certified_epoch_three_quarter`.

* Every `SupportTreeEpoch` is converted automatically to a `TreeBlockCert`
  using its unique full edge and recency.
* Every `SupportCycleEpoch` is automatically frozen and folded into the fixed
  part of the snapshot.
* Active occupied lobes supply the Boolean coordinates.

The only remaining nonlocal input is a finite decomposition of the support
into these block lists plus residual fixed cells.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Automatically certified tree blocks. -/
noncomputable def automaticTreeBlocks
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (trees : List (SupportTreeEpoch m e r0 times)) :
    List (TreeBlockCert m e r0 times) :=
  trees.map (fun T => T.toTreeBlock m e r0 hrun hr0)

/-- Cells occurring in the tree-block list before conversion. -/
def automaticTreeCells
    (trees : List (SupportTreeEpoch m e r0 times)) : List Nat :=
  trees.flatMap (fun T => T.cells)

/-- Cells occurring in equal-sized frozen components. -/
def automaticCycleCells
    (cycles : List (SupportCycleEpoch m e r0 times)) : List Nat :=
  cycles.flatMap (fun T => T.cells)

/-- Automatic conversion preserves the concatenated tree-cell list. -/
theorem automaticTreeBlocks_cells
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) :
    ∀ trees : List (SupportTreeEpoch m e r0 times),
      treeCells m e r0 (automaticTreeBlocks m e r0 hrun hr0 trees) =
        automaticTreeCells m e r0 trees := by
  intro trees
  induction trees with
  | nil => rfl
  | cons T rest ih =>
      unfold automaticTreeBlocks automaticTreeCells treeCells
      simp only [List.map_cons, List.flatMap_cons]
      change T.cells ++
          treeCells m e r0 (automaticTreeBlocks m e r0 hrun hr0 rest) =
        T.cells ++ automaticTreeCells m e r0 rest
      rw [ih]

/-- Automatic conversion preserves the summed tree-cell count. -/
theorem automaticTreeBlocks_cellCount
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) :
    ∀ trees : List (SupportTreeEpoch m e r0 times),
      treeCellCount m e r0
          (automaticTreeBlocks m e r0 hrun hr0 trees) =
        (automaticTreeCells m e r0 trees).length := by
  intro trees
  induction trees with
  | nil => rfl
  | cons T rest ih =>
      unfold automaticTreeBlocks automaticTreeCells treeCellCount
      simp only [List.map_cons, List.flatMap_cons, List.length_append]
      change T.cells.length +
          treeCellCount m e r0
            (automaticTreeBlocks m e r0 hrun hr0 rest) =
        T.cells.length + (automaticTreeCells m e r0 rest).length
      rw [ih]

/-- Converted blocks retain the tree-size equation. -/
theorem automaticTreeBlocks_size
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (trees : List (SupportTreeEpoch m e r0 times)) :
    ∀ b ∈ automaticTreeBlocks m e r0 hrun hr0 trees,
      b.edges.length + 1 = b.cells.length := by
  intro b hb
  unfold automaticTreeBlocks at hb
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hb
  exact T.tree_size

/-- The product of automatic tree-marker capacities has the square-root
bound once every listed tree block is nontrivial. -/
theorem automaticTreeCapacity_square
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (trees : List (SupportTreeEpoch m e r0 times))
    (hmin : ∀ T ∈ trees, 2 ≤ T.cells.length) :
    treeCapacity m e r0 (automaticTreeBlocks m e r0 hrun hr0 trees) *
      treeCapacity m e r0 (automaticTreeBlocks m e r0 hrun hr0 trees) ≤
      2^((automaticTreeCells m e r0 trees).length) := by
  have h := treeCapacity_square m e r0
    (automaticTreeBlocks m e r0 hrun hr0 trees)
    (automaticTreeBlocks_size m e r0 hrun hr0 trees)
    (by
      intro b hb
      unfold automaticTreeBlocks at hb
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hb
      exact hmin T hT)
  rw [automaticTreeBlocks_cellCount m e r0 hrun hr0 trees] at h
  exact h

/-- All equal-sized non-lobe component cells are fixed across selected times
inside one fixed-support interval. -/
theorem automaticCycleCells_fixed
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cycles : List (SupportCycleEpoch m e r0 times))
    {I J : Nat} (_hIJ : I ≤ J)
    (htimes : ∀ k, I ≤ k → k ≤ J → times k)
    (hsupport : ∀ k, I ≤ k → k < J → ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (ks : List Nat)
    (hwithin : ∀ k ∈ ks, I ≤ k ∧ k ≤ J) :
    ∀ x ∈ ks, ∀ y ∈ ks, ∀ c ∈ automaticCycleCells m e r0 cycles,
      reg m e r0 x c = reg m e r0 y c := by
  intro x hx y hy c hc
  obtain ⟨T, hT, hcT⟩ := List.mem_flatMap.mp hc
  by_cases hxy : x ≤ y
  · have hstable := T.stable m e r0 hrun hr0 hxy
      (fun k hxk hky => htimes k
        (Nat.le_trans (hwithin x hx).1 hxk)
        (Nat.le_trans (Nat.le_of_lt hky) (hwithin y hy).2))
      (fun k hxk hky s => hsupport k
        (Nat.le_trans (hwithin x hx).1 hxk)
        (Nat.lt_of_lt_of_le hky (hwithin y hy).2) s)
      c hcT
    exact hstable.symm
  · have hyx : y ≤ x := by omega
    exact T.stable m e r0 hrun hr0 hyx
      (fun k hyk hkx => htimes k
        (Nat.le_trans (hwithin y hy).1 hyk)
        (Nat.le_trans (Nat.le_of_lt hkx) (hwithin x hx).2))
      (fun k hyk hkx s => hsupport k
        (Nat.le_trans (hwithin y hy).1 hyk)
        (Nat.lt_of_lt_of_le hkx (hwithin x hx).2) s)
      c hcT

/-- **Automatic pre-Gray fixed-support bound from a component decomposition.**

Tree blocks and cycle blocks need no rank, full-edge choice, or state code.
Those objects are manufactured by the preceding theorems. -/
theorem automatic_epoch_three_quarter
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {I J : Nat} (hIJ : I ≤ J)
    (trees : List (SupportTreeEpoch m e r0 times))
    (cycles : List (SupportCycleEpoch m e r0 times))
    (active residual allCells ks : List Nat)
    (slotOf : Nat → Nat)
    (L : Nat)
    (htimes : ∀ k, I ≤ k → k ≤ J → times k)
    (hsupportSteps : ∀ k, I ≤ k → k < J → ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hsupportPairs : ∀ x ∈ ks, ∀ y ∈ ks, ∀ s,
      Occupied m e r0 x s ↔ Occupied m e r0 y s)
    (hwithin : ∀ k ∈ ks, I ≤ k ∧ k ≤ J)
    (hactiveNodup : active.Nodup)
    (hactiveSub : ∀ c ∈ active, c ∈ allCells)
    (hclosed : StarClosed m allCells)
    (hvar : ∀ c ∈ active, VariesOnInterval m e r0 I J c)
    (hslotCell : ∀ c ∈ active, m.cellOf (slotOf c) = c)
    (hslotLobe : ∀ c ∈ active, LobeSlot m (slotOf c))
    (hslotOcc : ∀ c ∈ active, ∀ k,
      I ≤ k → k ≤ J → Occupied m e r0 k (slotOf c))
    (hnoGray : ∀ k, I < k → k ≤ J → ¬ GrayTail m e r0 k)
    (hresidualFixed : ∀ x ∈ ks, ∀ y ∈ ks, ∀ c ∈ residual,
      reg m e r0 x c = reg m e r0 y c)
    (hcover : ∀ c ∈ allCells,
      c ∈ automaticTreeCells m e r0 trees ∨ c ∈ active ∨
      c ∈ automaticCycleCells m e r0 cycles ∨ c ∈ residual)
    (hmin : ∀ T ∈ trees, 2 ≤ T.cells.length)
    (hC : allCells.length = L + (automaticTreeCells m e r0 trees).length)
    (hAL : active.length ≤ L)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    fourth ks.length ≤ 2^(3 * allCells.length) := by
  let blocks := automaticTreeBlocks m e r0 hrun hr0 trees
  let fixed := automaticCycleCells m e r0 cycles ++ residual
  have hfixed : ∀ x ∈ ks, ∀ y ∈ ks, ∀ c ∈ fixed,
      reg m e r0 x c = reg m e r0 y c := by
    intro x hx y hy c hc
    dsimp [fixed] at hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact automaticCycleCells_fixed m e r0 hrun hr0 cycles hIJ
        htimes hsupportSteps ks hwithin x hx y hy c hc
    · exact hresidualFixed x hx y hy c hc
  have hcover' : ∀ c ∈ allCells,
      c ∈ treeCells m e r0 blocks ∨ c ∈ active ∨ c ∈ fixed := by
    intro c hc
    rcases hcover c hc with ht | ha | hcy | hr
    · left
      dsimp [blocks]
      rw [automaticTreeBlocks_cells m e r0 hrun hr0 trees]
      exact ht
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (List.mem_append_left _ hcy))
    · exact Or.inr (Or.inr (List.mem_append_right _ hr))
  have hC' : allCells.length =
      L + treeCellCount m e r0 blocks := by
    dsimp [blocks]
    rw [automaticTreeBlocks_cellCount m e r0 hrun hr0 trees]
    exact hC
  exact certified_epoch_three_quarter m e r0 hrun hr0 hIJ
    blocks active fixed allCells ks slotOf L
    (fun k hk => htimes k (hwithin k hk).1 (hwithin k hk).2)
    hsupportPairs hactiveNodup hactiveSub hclosed hvar
    hslotCell hslotLobe hslotOcc hnoGray hfixed hcover'
    hwithin
    (by
      dsimp [blocks]
      exact automaticTreeBlocks_size m e r0 hrun hr0 trees)
    (by
      intro b hb
      dsimp [blocks] at hb
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hb
      exact hmin T hT)
    hC' hAL hnd

end Echo
