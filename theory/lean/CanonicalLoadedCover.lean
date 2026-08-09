import CanonicalLoadedAssignment

/-!
# Recovery properties of the canonical loaded assignment

The canonical construction is useful only if it preserves the original finite
component data.  This file proves the two exact recovery statements needed by
the automatic `2/3` epoch theorem:

* the certified tree blocks flatten to the original ordinary-tree cells; and
* assigned lobes together with the free list contain exactly the original
  active lobe components (membership-wise).

The second statement does not yet assert duplicate-freeness; that follows from
the component-disjointness hypotheses of the final finite partition.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {I J : Nat}

/-- Canonical groups contain exactly one copy of each input tree's cell list. -/
theorem canonicalLoaded_treeCells_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (trees : List (SupportTreeEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (lobes : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (hmin : ∀ T ∈ trees, 2 ≤ T.cells.length)
    (hroots : (lobeForestRoots m e r0 lobes).Nodup)
    (houtside : ∀ B ∈ lobes,
      B.root m ∉ automaticTreeCells m e r0 trees)
    (hvar : ∀ B ∈ lobes,
      VariesOnInterval m e r0 I J (B.root m)) :
    treeCells m e r0
        (loadedGroupTreeBlocks m e r0 hrun hr0
          (canonicalLoadedGroups m e r0 trees lobes
            hmin hroots houtside hvar)) =
      automaticTreeCells m e r0 trees := by
  classical
  simp [canonicalLoadedGroups, loadedGroupTreeBlocks,
    treeCells, automaticTreeCells,
    SupportTreeEpoch.toTreeBlock, recencyTreeBlock,
    List.map_map, Function.comp_def]

/-- Assigned-lobe membership has the expected existential description. -/
theorem mem_canonicalLoaded_assigned_iff
    (trees : List (SupportTreeEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (lobes : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (hmin : ∀ T ∈ trees, 2 ≤ T.cells.length)
    (hroots : (lobeForestRoots m e r0 lobes).Nodup)
    (houtside : ∀ B ∈ lobes,
      B.root m ∉ automaticTreeCells m e r0 trees)
    (hvar : ∀ B ∈ lobes,
      VariesOnInterval m e r0 I J (B.root m))
    (B : SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)) :
    B ∈ loadedGroupLobes m e r0
        (canonicalLoadedGroups m e r0 trees lobes
          hmin hroots houtside hvar) ↔
      B ∈ lobes ∧
        m.star (B.root m) ∈ automaticTreeCells m e r0 trees := by
  classical
  simp [loadedGroupLobes, canonicalLoadedGroups,
    lobesAssignedToTree, automaticTreeCells]

/-- Assigned plus free lobes recover the original lobe list exactly at the
level of membership. -/
theorem mem_canonicalLoaded_allLobes_iff
    (trees : List (SupportTreeEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (lobes : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (hmin : ∀ T ∈ trees, 2 ≤ T.cells.length)
    (hroots : (lobeForestRoots m e r0 lobes).Nodup)
    (houtside : ∀ B ∈ lobes,
      B.root m ∉ automaticTreeCells m e r0 trees)
    (hvar : ∀ B ∈ lobes,
      VariesOnInterval m e r0 I J (B.root m))
    (B : SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)) :
    B ∈ loadedGroupsAllLobes m e r0
        (canonicalLoadedGroups m e r0 trees lobes
          hmin hroots houtside hvar)
        (freeLobesOfTrees m e r0 trees lobes) ↔
      B ∈ lobes := by
  classical
  unfold loadedGroupsAllLobes
  rw [List.mem_append]
  rw [mem_canonicalLoaded_assigned_iff m e r0
    trees lobes hmin hroots houtside hvar B,
    mem_freeLobesOfTrees_iff m e r0 trees lobes B]
  constructor
  · rintro (⟨hB, _⟩ | ⟨hB, _⟩) <;> exact hB
  · intro hB
    by_cases hp : m.star (B.root m) ∈
        automaticTreeCells m e r0 trees
    · exact Or.inl ⟨hB, hp⟩
    · exact Or.inr ⟨hB, hp⟩

end Echo
