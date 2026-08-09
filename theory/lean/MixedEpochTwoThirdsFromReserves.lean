import OneReserveListAssemblyV2
import TreeCapacityTwoThirds

/-!
# The two-thirds epoch theorem from a finite one-reserve frame

This module joins the semantic/combinatorial reserve injection to the mixed
support-component code.  It leaves no arithmetic gap:

* one active lobe root and its mouth partner cost two cells;
* one additional reserve is selected from every variable tree component;
* the resulting inequality is exactly the hypothesis of
  `mixed_epoch_two_thirds`.

The remaining construction problem is canonical rather than numerical: obtain
these root and component lists from the occupied-support decomposition and use
`OneReserveFromNoTail` to supply each reserve.
-/

namespace Echo

/-- **Mixed fixed-support `2/3` bound from explicit reserve data.** -/
theorem mixed_epoch_two_thirds_of_one_reserve_frame
    (m : Machine) (e r0 : Nat → Nat)
    {times : Nat → Prop}
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {I J : Nat} (hIJ : I ≤ J)
    (trees : List (TreeBlockCert m e r0 times))
    (lobes : List (SupportLobeForestEpoch m e r0 times))
    (fixed allCells ks roots : List Nat)
    (L : Nat)
    (hrootLength : roots.length = lobes.length)
    (hrootSep : RootStarSeparatedV2 m roots)
    (hrootsSub : ∀ r ∈ roots,
      r ∈ allCells ∧ m.star r ∈ allCells)
    (hcomponentSub : ∀ B ∈ trees,
      ∀ c ∈ B.cells, c ∈ allCells)
    (hcomponentAwayRoots : ∀ B ∈ trees,
      ∀ c ∈ B.cells, c ∉ roots)
    (hcomponentDisjoint : ComponentListsDisjointV2
      (trees.map fun B => B.cells))
    (hreserve : ∀ B ∈ trees,
      ∃ r, IsComponentReserveV2 m roots B.cells r)
    (htimes : ∀ k, I ≤ k → k ≤ J → times k)
    (hks : ∀ k ∈ ks, times k)
    (hwithin : ∀ k ∈ ks, I ≤ k ∧ k ≤ J)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfixed : ∀ i ∈ ks, ∀ j ∈ ks, ∀ c ∈ fixed,
      reg m e r0 i c = reg m e r0 j c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0 trees ∨
      c ∈ lobeForestCells m e r0 lobes ∨ c ∈ fixed)
    (hsize : ∀ b ∈ trees, b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ trees, 2 ≤ b.cells.length)
    (hC : allCells.length = L + treeCellCount m e r0 trees)
    (hAL : lobes.length ≤ L)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    treeCube ks.length ≤ 2^(2*allCells.length) := by
  have hcomponentSub' :
      ∀ cells ∈ trees.map (fun B => B.cells),
        ∀ c ∈ cells, c ∈ allCells := by
    intro cells hcells c hc
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hcells
    exact hcomponentSub B hB c hc
  have hcomponentAwayRoots' :
      ∀ cells ∈ trees.map (fun B => B.cells),
        ∀ c ∈ cells, c ∉ roots := by
    intro cells hcells c hc
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hcells
    exact hcomponentAwayRoots B hB c hc
  have hreserve' :
      ∀ cells ∈ trees.map (fun B => B.cells),
        ∃ r, IsComponentReserveV2 m roots cells r := by
    intro cells hcells
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hcells
    exact hreserve B hB
  have hcount := one_reserve_component_count_v2 m
    roots allCells (trees.map fun B => B.cells)
    hrootSep hrootsSub hcomponentSub' hcomponentAwayRoots'
    hcomponentDisjoint hreserve'
  have hreserved :
      2*lobes.length + trees.length ≤ allCells.length := by
    rw [← hrootLength]
    simpa only [List.length_map] using hcount
  exact mixed_epoch_two_thirds m e r0 hrun hr0 hIJ
    trees lobes fixed allCells ks L htimes hks hwithin
    hsupport hfixed hcover hsize hmin hC hAL hreserved hnd

end Echo
