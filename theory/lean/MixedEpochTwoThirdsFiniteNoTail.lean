import MixedEpochTwoThirdsFromReserves
import FiniteFullyLobedComponentTrap

/-!
# Interval-local two-thirds epoch bound

This is the canonical pre-tail form of the improved component estimate.  All
reflector and occupancy hypotheses are restricted to the fixed-support
interval `[I,J]`; `FiniteFullyLobedComponentTrap` extracts one reserve from
every visited variable tree component.
-/

namespace Echo

/-- **Mixed fixed-support `2/3` bound before a finite reflector tail.** -/
theorem mixed_epoch_two_thirds_finite_no_tail
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
    (hselectedClosed : ∀ B ∈ trees,
      SelectedClosedOn m e r0 B.cells I J)
    (hvisited : ∀ B ∈ trees,
      ComponentVisitedOn m e B.cells I J)
    (hnoReflectorTail : ∀ B ∈ trees,
      NoFourReturnComponentTailOn m e B.cells I J)
    (hactive : PersistentActiveLobeRootsOn m e r0 roots I J)
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
  have hreserve : ∀ B ∈ trees,
      ∃ r, IsComponentReserveV2 m roots B.cells r := by
    intro B hB
    rcases exists_component_reserve_on
        m e r0 hrun hr0 B.cells roots I J
        (hselectedClosed B hB)
        (hvisited B hB)
        (hnoReflectorTail B hB)
        hactive with
      ⟨r, hrB, hrRoot⟩
    exact ⟨r, hrB, hrRoot⟩
  exact mixed_epoch_two_thirds_of_one_reserve_frame
    m e r0 hrun hr0 hIJ trees lobes fixed allCells ks roots L
    hrootLength hrootSep hrootsSub hcomponentSub
    hcomponentAwayRoots hcomponentDisjoint hreserve
    htimes hks hwithin hsupport hfixed hcover
    hsize hmin hC hAL hnd

end Echo
