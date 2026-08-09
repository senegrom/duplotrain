import TreeCapacityTwoThirds

/-!
# Minimal coordinate frame for the one-reserve bound

This structure isolates the exact finite data required by the improved
component count.  It is intentionally independent of the canonical graph
construction, so downstream arithmetic remains stable while that construction
is refined.
-/

namespace Echo

/-- Active roots, their partner cells, and one reserve per variable component
are represented by one duplicate-free coordinate list inside `allCells`. -/
structure OneReserveCoordinateFrame
    (roots : List Nat) (componentCount : Nat)
    (allCells : List Nat) where
  partners : List Nat
  reserves : List Nat
  partners_length : partners.length = roots.length
  reserves_length : reserves.length = componentCount
  coordinates_nodup : ((roots ++ partners) ++ reserves).Nodup
  coordinates_subset :
    ∀ c ∈ (roots ++ partners) ++ reserves, c ∈ allCells

private theorem frame_subset_length
    {xs ys : List Nat}
    (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ ys.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- The frame gives the strengthened reserve inequality. -/
theorem OneReserveCoordinateFrame.count
    {roots allCells : List Nat} {Q : Nat}
    (frame : OneReserveCoordinateFrame roots Q allCells) :
    2 * roots.length + Q ≤ allCells.length := by
  have hle := frame_subset_length
    frame.coordinates_nodup frame.coordinates_subset
  simp only [List.length_append] at hle
  rw [frame.partners_length, frame.reserves_length] at hle
  omega

/-- **Stable mixed `2/3` endpoint from a coordinate frame.** -/
theorem mixed_epoch_two_thirds_of_coordinate_frame
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
    (frame : OneReserveCoordinateFrame roots trees.length allCells)
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
  have hreserved := frame.count
  rw [hrootLength] at hreserved
  exact mixed_epoch_two_thirds m e r0 hrun hr0 hIJ
    trees lobes fixed allCells ks L htimes hks hwithin
    hsupport hfixed hcover hsize hmin hC hAL hreserved hnd

end Echo
