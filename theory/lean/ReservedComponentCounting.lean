import TreeCapacityTwoThirds

/-!
# Counting active roots, mouth partners and reserved component cells

The dynamical part of the two-thirds proof has a simple finite counting
interface.  For every active lobe root we list

* the active root cell itself, and
* its distinct mouth-partner cell.

For every variable tree component we additionally list one reserved cell not
among either of those two lists.  If all three lists concatenate without
duplicates inside the finite cell universe, then

    2 * #activeRoots + #treeComponents ≤ #cells.

This is precisely the strengthened inequality consumed by
`mixed_epoch_two_thirds`.
-/

namespace Echo

private theorem reserved_nodup_subset_length_nat
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

/-- **Reserved-cell inequality.** -/
theorem reserved_component_inequality
    (active partners reserved cells : List Nat)
    (hpartners : partners.length = active.length)
    (hnd : (active ++ partners ++ reserved).Nodup)
    (hsub : ∀ c ∈ active ++ partners ++ reserved, c ∈ cells) :
    2 * active.length + reserved.length ≤ cells.length := by
  have hle := reserved_nodup_subset_length_nat hnd hsub
  simp only [List.length_append] at hle
  omega

/-- Version indexed by an abstract component list: one reserved cell per
component. -/
theorem reserved_component_inequality_of_index
    {α : Type}
    (active partners reserved cells : List Nat)
    (components : List α)
    (hpartners : partners.length = active.length)
    (hreserved : reserved.length = components.length)
    (hnd : (active ++ partners ++ reserved).Nodup)
    (hsub : ∀ c ∈ active ++ partners ++ reserved, c ∈ cells) :
    2 * active.length + components.length ≤ cells.length := by
  have h := reserved_component_inequality
    active partners reserved cells hpartners hnd hsub
  omega

/-- The exact combinatorial interface needed by the mixed epoch theorem.
The semantic construction should instantiate `active` with the lobe-root
cells, `partners` with their `star` images, and `reserved` with one uncovered
cell from every variable tree component. -/
theorem mixed_epoch_two_thirds_of_reserved_lists
    (m : Machine) (e r0 : Nat → Nat)
    {times : Nat → Prop}
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {I J : Nat} (hIJ : I ≤ J)
    (trees : List (TreeBlockCert m e r0 times))
    (lobes : List (SupportLobeForestEpoch m e r0 times))
    (fixed allCells ks : List Nat)
    (L : Nat)
    (active partners reserved : List Nat)
    (hactive : active.length = lobes.length)
    (hpartners : partners.length = active.length)
    (hreserved : reserved.length = trees.length)
    (hcountNodup : (active ++ partners ++ reserved).Nodup)
    (hcountSub : ∀ c ∈ active ++ partners ++ reserved, c ∈ allCells)
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
  have hreservedCount :
      2 * lobes.length + trees.length ≤ allCells.length := by
    have hbase := reserved_component_inequality_of_index
      active partners reserved allCells trees hpartners hreserved
      hcountNodup hcountSub
    omega
  exact mixed_epoch_two_thirds m e r0 hrun hr0 hIJ
    trees lobes fixed allCells ks L htimes hks hwithin
    hsupport hfixed hcover hsize hmin hC hAL
    hreservedCount hnd

end Echo
