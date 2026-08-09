import LoadedTreeGroupsWithFreeTwoThirds
import AutomaticEpochBound

/-!
# Automatic mixed fixed-support bound with exponent two-thirds

This is the `2/3` analogue of `automatic_epoch_three_quarter`.

* ordinary tree components are supplied as dynamics-coupled loaded groups;
* active lobe-forest components are either charged to those trees or left
  free and star-pair charged;
* equal-sized non-lobe cycle components are frozen automatically; and
* residual cells are supplied as fixed.

The dynamical non-full-load theorem is already built into each loaded group.
The only nonlocal combinatorial datum left is the duplicate-free charged-cell
partition.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {I J : Nat}

/-- **Automatic pre-absorption fixed-support bound with exponent `2/3`.** -/
theorem automatic_loaded_epoch_two_thirds
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hIJ : I ≤ J)
    (groups : List (LoadedTreeGroup m e r0 I J))
    (free : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (cycles : List (SupportCycleEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (residual allCells ks : List Nat)
    (htimes : ∀ k, I ≤ k → k ≤ J →
      (fun q => I ≤ q ∧ q ≤ J) k)
    (hsupportSteps : ∀ k, I ≤ k → k < J → ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hsupportPairs : ∀ x ∈ ks, ∀ y ∈ ks, ∀ s,
      Occupied m e r0 x s ↔ Occupied m e r0 y s)
    (hwithin : ∀ k ∈ ks, I ≤ k ∧ k ≤ J)
    (hresidualFixed : ∀ x ∈ ks, ∀ y ∈ ks, ∀ c ∈ residual,
      reg m e r0 x c = reg m e r0 y c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0
          (loadedGroupTreeBlocks m e r0 hrun hr0 groups) ∨
      c ∈ lobeForestCells m e r0
          (loadedGroupsAllLobes m e r0 groups free) ∨
      c ∈ automaticCycleCells m e r0 cycles ∨
      c ∈ residual)
    (hchargedNodup :
      (loadedGroupsWithFreeChargedCells m e r0 groups free).Nodup)
    (hchargedSub : ∀ c ∈
      loadedGroupsWithFreeChargedCells m e r0 groups free,
      c ∈ allCells)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    loadedCube ks.length ≤ 2^(2*allCells.length) := by
  let fixed := automaticCycleCells m e r0 cycles ++ residual
  have hfixed : ∀ x ∈ ks, ∀ y ∈ ks, ∀ c ∈ fixed,
      reg m e r0 x c = reg m e r0 y c := by
    intro x hx y hy c hc
    dsimp [fixed] at hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact automaticCycleCells_fixed m e r0 hrun hr0
        cycles hIJ htimes hsupportSteps ks hwithin
        x hx y hy c hc
    · exact hresidualFixed x hx y hy c hc
  have hcover' : ∀ c ∈ allCells,
      c ∈ treeCells m e r0
          (loadedGroupTreeBlocks m e r0 hrun hr0 groups) ∨
      c ∈ lobeForestCells m e r0
          (loadedGroupsAllLobes m e r0 groups free) ∨
      c ∈ fixed := by
    intro c hc
    rcases hcover c hc with ht | hl | hcy | hr
    · exact Or.inl ht
    · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr (List.mem_append_left _ hcy))
    · exact Or.inr (Or.inr (List.mem_append_right _ hr))
  exact loaded_groups_with_free_epoch_two_thirds_of_charged_cells
    m e r0 hrun hr0 groups free fixed allCells ks
    hwithin hsupportPairs hfixed hcover'
    hchargedNodup hchargedSub hnd

end Echo
