import AutomaticLoadedTwoThirds

/-!
# Canonical assignment of active lobes to ordinary support trees

Given finite lists of ordinary support-tree components and active lobe-forest
components, assign a lobe to a tree exactly when its mouth-partner cell lies in
that tree.  Lobes whose partner lies in no ordinary tree form the free list.

This file constructs the `LoadedTreeGroup` objects required by the dynamics-
coupled `2/3` theorem.  No arbitrary choices are made: the assignment is by
finite filtering.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {I J : Nat}

/-- Active lobe components whose mouth partner lies in one tree. -/
noncomputable def lobesAssignedToTree
    (T : SupportTreeEpoch m e r0 (fun k => I ≤ k ∧ k ≤ J))
    (lobes : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J))) :
    List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)) := by
  classical
  exact lobes.filter fun B => decide (m.star (B.root m) ∈ T.cells)

/-- Active lobes whose partner lies in no ordinary tree. -/
noncomputable def freeLobesOfTrees
    (trees : List (SupportTreeEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (lobes : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J))) :
    List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)) := by
  classical
  exact lobes.filter fun B =>
    decide (m.star (B.root m) ∉ automaticTreeCells m e r0 trees)

theorem mem_lobesAssignedToTree_iff
    (T : SupportTreeEpoch m e r0 (fun k => I ≤ k ∧ k ≤ J))
    (lobes : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (B : SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)) :
    B ∈ lobesAssignedToTree m e r0 T lobes ↔
      B ∈ lobes ∧ m.star (B.root m) ∈ T.cells := by
  classical
  unfold lobesAssignedToTree
  rw [List.mem_filter]
  constructor
  · rintro ⟨hB, hp⟩
    exact ⟨hB, of_decide_eq_true hp⟩
  · rintro ⟨hB, hp⟩
    exact ⟨hB, decide_eq_true hp⟩

theorem mem_freeLobesOfTrees_iff
    (trees : List (SupportTreeEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (lobes : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (B : SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)) :
    B ∈ freeLobesOfTrees m e r0 trees lobes ↔
      B ∈ lobes ∧
        m.star (B.root m) ∉ automaticTreeCells m e r0 trees := by
  classical
  unfold freeLobesOfTrees
  rw [List.mem_filter]
  constructor
  · rintro ⟨hB, hp⟩
    exact ⟨hB, of_decide_eq_true hp⟩
  · rintro ⟨hB, hp⟩
    exact ⟨hB, decide_eq_true hp⟩

private theorem map_filter_nodup_assignment
    {α β : Type} [BEq β] [LawfulBEq β]
    (f : α → β) (p : α → Bool) {xs : List α}
    (hnd : (xs.map f).Nodup) :
    ((xs.filter p).map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hnd' := List.nodup_cons.mp hnd
      cases hp : p x with
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd'.2
      | true =>
          simp only [List.filter_cons, hp, List.map_cons]
          have hnot : f x ∉ (rest.filter p).map f := by
            intro hmem
            apply hnd'.1
            obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
            exact List.mem_map.mpr
              ⟨y, (List.mem_filter.mp hy).1, hfy⟩
          rw [List.nodup_cons]
          exact ⟨hnot, ih hnd'.2⟩

/-- Filtering a globally root-distinct lobe list preserves root distinctness. -/
theorem assigned_lobe_roots_nodup
    (T : SupportTreeEpoch m e r0 (fun k => I ≤ k ∧ k ≤ J))
    (lobes : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (hroots : (lobeForestRoots m e r0 lobes).Nodup) :
    (lobeForestRoots m e r0
      (lobesAssignedToTree m e r0 T lobes)).Nodup := by
  classical
  unfold lobeForestRoots lobesAssignedToTree
  exact map_filter_nodup_assignment
    (fun B : SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J) => B.root m)
    (fun B => decide (m.star (B.root m) ∈ T.cells)) hroots

/-- A lobe partner belongs to the flattened tree-cell list exactly when it
belongs to at least one listed tree. -/
theorem partner_mem_automaticTreeCells_iff
    (trees : List (SupportTreeEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (c : Nat) :
    c ∈ automaticTreeCells m e r0 trees ↔
      ∃ T, T ∈ trees ∧ c ∈ T.cells := by
  simp [automaticTreeCells]

/-- Every active lobe is either assigned to a listed tree or belongs to the
free list. -/
theorem lobe_assigned_or_free
    (trees : List (SupportTreeEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (lobes : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    {B : SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)}
    (hB : B ∈ lobes) :
    (∃ T, T ∈ trees ∧
      B ∈ lobesAssignedToTree m e r0 T lobes) ∨
      B ∈ freeLobesOfTrees m e r0 trees lobes := by
  classical
  by_cases hp : m.star (B.root m) ∈
      automaticTreeCells m e r0 trees
  · left
    rcases (partner_mem_automaticTreeCells_iff
      m e r0 trees _).mp hp with ⟨T, hT, hc⟩
    exact ⟨T, hT,
      (mem_lobesAssignedToTree_iff m e r0 T lobes B).mpr
        ⟨hB, hc⟩⟩
  · right
    exact (mem_freeLobesOfTrees_iff m e r0 trees lobes B).mpr
      ⟨hB, hp⟩

/-- Canonical loaded groups, one per ordinary support tree. -/
noncomputable def canonicalLoadedGroups
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
    List (LoadedTreeGroup m e r0 I J) := by
  classical
  exact trees.attach.map fun ⟨T, hT⟩ =>
    { tree := T
      lobes := lobesAssignedToTree m e r0 T lobes
      min_cells := hmin T hT
      roots_nodup := assigned_lobe_roots_nodup
        m e r0 T lobes hroots
      partners_in_tree := by
        intro B hB
        exact ((mem_lobesAssignedToTree_iff
          m e r0 T lobes B).mp hB).2
      roots_outside_tree := by
        intro B hB hroot
        have hB0 := ((mem_lobesAssignedToTree_iff
          m e r0 T lobes B).mp hB).1
        have hout := houtside B hB0
        apply hout
        exact (partner_mem_automaticTreeCells_iff
          m e r0 trees (B.root m)).mpr
          ⟨T, hT, hroot⟩
      varying := by
        intro B hB
        exact hvar B
          ((mem_lobesAssignedToTree_iff
            m e r0 T lobes B).mp hB).1 }

end Echo
