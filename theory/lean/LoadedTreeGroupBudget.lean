import LoadedTreeGroupsTwoThirds

/-!
# Cell-budget bookkeeping for loaded tree groups

The `2/3` epoch theorem needs only one global numerical hypothesis: the tree
cells and charged lobe roots fit inside the represented cell universe.  This
file replaces that number inequality by its natural finite-partition form.

For each group, list

    tree cells ++ charged lobe roots.

If the concatenated list is duplicate-free and every listed cell belongs to
`allCells`, its length is at most `allCells.length`.  Its length is definitionally
exactly the profile cost used by the `2/3` arithmetic.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {I J : Nat}

/-- Tree cells and one root cell for each lobe bit charged to that tree. -/
def loadedGroupChargedCells
    (groups : List (LoadedTreeGroup m e r0 I J)) : List Nat :=
  groups.flatMap fun G =>
    G.tree.cells ++ lobeForestRoots m e r0 G.lobes

/-- Exact charged-cell cardinality. -/
theorem loadedGroupChargedCells_length :
    ∀ groups : List (LoadedTreeGroup m e r0 I J),
      (loadedGroupChargedCells m e r0 groups).length =
        notFullLoadedCells (loadedGroupProfile m e r0 groups) := by
  intro groups
  induction groups with
  | nil => rfl
  | cons G rest ih =>
      unfold loadedGroupChargedCells loadedGroupProfile
      simp only [List.flatMap_cons, List.map_cons,
        List.length_append, notFullLoadedCells]
      have hroots :
          (lobeForestRoots m e r0 G.lobes).length = G.lobes.length := by
        simp [lobeForestRoots]
      rw [hroots, ih]

private theorem charged_nodup_subset_length
    {xs ys : List Nat}
    (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ ys.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun h => hnd.1 (h ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- Duplicate-free charged cells inside `allCells` supply the arithmetic cell
budget automatically. -/
theorem loadedGroup_cellBudget
    (groups : List (LoadedTreeGroup m e r0 I J))
    (allCells : List Nat)
    (hnd : (loadedGroupChargedCells m e r0 groups).Nodup)
    (hsub : ∀ c ∈ loadedGroupChargedCells m e r0 groups,
      c ∈ allCells) :
    notFullLoadedCells (loadedGroupProfile m e r0 groups) ≤
      allCells.length := by
  have hle := charged_nodup_subset_length hnd hsub
  rw [loadedGroupChargedCells_length m e r0 groups] at hle
  exact hle

/-- **Partition-form `2/3` epoch theorem.** -/
theorem loaded_groups_epoch_two_thirds_of_charged_cells
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
    (hchargedNodup :
      (loadedGroupChargedCells m e r0 groups).Nodup)
    (hchargedSub : ∀ c ∈ loadedGroupChargedCells m e r0 groups,
      c ∈ allCells)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    loadedCube ks.length ≤ 2^(2*allCells.length) := by
  exact loaded_groups_epoch_two_thirds m e r0 hrun hr0
    groups fixed allCells ks hks hsupport hfixed hcover
    (loadedGroup_cellBudget m e r0 groups allCells
      hchargedNodup hchargedSub)
    hnd

end Echo
