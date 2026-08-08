import MixedEpochBound

/-!
# Automatically split lobe forests into varying and fixed roots

The mixed bound previously accepted separate lists of varying and fixed lobe
forests.  This file manufactures that partition from the interval itself.
A block is active exactly when its root register varies somewhere in `[I,J]`.

The filter gives all required facts automatically:

* active roots satisfy the variation hypothesis;
* inactive roots have equal registers at every two selected times;
* every original block belongs to one side; and
* the active list is no longer than the original lobe-block list.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Lobe-forest blocks whose root varies on `[I,J]`. -/
noncomputable def varyingLobeForests
    (I J : Nat)
    (blocks : List (SupportLobeForestEpoch m e r0 times)) :
    List (SupportLobeForestEpoch m e r0 times) := by
  classical
  exact blocks.filter (fun B =>
    decide (VariesOnInterval m e r0 I J (B.root m)))

/-- Lobe-forest blocks whose root is constant on `[I,J]`. -/
noncomputable def fixedLobeForests
    (I J : Nat)
    (blocks : List (SupportLobeForestEpoch m e r0 times)) :
    List (SupportLobeForestEpoch m e r0 times) := by
  classical
  exact blocks.filter (fun B =>
    decide (¬ VariesOnInterval m e r0 I J (B.root m)))

theorem mem_varyingLobeForests_iff
    {I J : Nat}
    {blocks : List (SupportLobeForestEpoch m e r0 times)}
    {B : SupportLobeForestEpoch m e r0 times} :
    B ∈ varyingLobeForests m e r0 I J blocks ↔
      B ∈ blocks ∧ VariesOnInterval m e r0 I J (B.root m) := by
  classical
  unfold varyingLobeForests
  rw [List.mem_filter]
  constructor
  · rintro ⟨hB, hv⟩
    exact ⟨hB, of_decide_eq_true hv⟩
  · rintro ⟨hB, hv⟩
    exact ⟨hB, decide_eq_true hv⟩

theorem mem_fixedLobeForests_iff
    {I J : Nat}
    {blocks : List (SupportLobeForestEpoch m e r0 times)}
    {B : SupportLobeForestEpoch m e r0 times} :
    B ∈ fixedLobeForests m e r0 I J blocks ↔
      B ∈ blocks ∧ ¬ VariesOnInterval m e r0 I J (B.root m) := by
  classical
  unfold fixedLobeForests
  rw [List.mem_filter]
  constructor
  · rintro ⟨hB, hv⟩
    exact ⟨hB, of_decide_eq_true hv⟩
  · rintro ⟨hB, hv⟩
    exact ⟨hB, decide_eq_true hv⟩

/-- A non-varying register is equal at any two times in the interval. -/
theorem reg_eq_of_not_varies
    {I J x y c : Nat}
    (hnvar : ¬ VariesOnInterval m e r0 I J c)
    (hx : I ≤ x ∧ x ≤ J)
    (hy : I ≤ y ∧ y ≤ J) :
    reg m e r0 x c = reg m e r0 y c := by
  apply Classical.byContradiction
  intro hne
  apply hnvar
  exact ⟨x, y, hx.1, hx.2, hy.1, hy.2, hne⟩

private theorem map_filter_nodup
    {α β : Type} [DecidableEq β]
    (f : α → β) (p : α → Bool) :
    ∀ {xs : List α}, (xs.map f).Nodup →
      ((xs.filter p).map f).Nodup := by
  intro xs
  induction xs with
  | nil => intro h; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
            exact hnd.1 (List.mem_map.mpr
              ⟨y, (List.mem_filter.mp hy).1, hfy⟩)
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp, if_false]
          exact ih hnd.2

/-- Filtering preserves root-list nodup. -/
theorem varying_roots_nodup
    (I J : Nat)
    (blocks : List (SupportLobeForestEpoch m e r0 times))
    (hnd : (lobeForestRoots m e r0 blocks).Nodup) :
    (lobeForestRoots m e r0
      (varyingLobeForests m e r0 I J blocks)).Nodup := by
  classical
  unfold lobeForestRoots at hnd ⊢
  change (((blocks.filter (fun B : SupportLobeForestEpoch m e r0 times =>
    decide (VariesOnInterval m e r0 I J (B.root m)))).map
      (fun B : SupportLobeForestEpoch m e r0 times => B.root m)).Nodup)
  exact map_filter_nodup
    (fun B : SupportLobeForestEpoch m e r0 times => B.root m)
    (fun B : SupportLobeForestEpoch m e r0 times =>
      decide (VariesOnInterval m e r0 I J (B.root m))) hnd

/-- Active roots remain inside any universe containing all original roots. -/
theorem varying_roots_subset
    (I J : Nat)
    (blocks : List (SupportLobeForestEpoch m e r0 times))
    (allCells : List Nat)
    (hsub : ∀ c ∈ lobeForestRoots m e r0 blocks, c ∈ allCells) :
    ∀ c ∈ lobeForestRoots m e r0
        (varyingLobeForests m e r0 I J blocks),
      c ∈ allCells := by
  intro c hc
  obtain ⟨B, hBv, rfl⟩ := List.mem_map.mp hc
  apply hsub (B.root m)
  apply List.mem_map.mpr
  exact ⟨B, (mem_varyingLobeForests_iff m e r0).mp hBv |>.1, rfl⟩

/-- Every lobe-forest cell belongs to either the varying or the fixed side. -/
theorem lobeForestCells_partition
    (I J : Nat)
    (blocks : List (SupportLobeForestEpoch m e r0 times)) :
    ∀ c ∈ lobeForestCells m e r0 blocks,
      c ∈ lobeForestCells m e r0
        (varyingLobeForests m e r0 I J blocks) ∨
      c ∈ lobeForestCells m e r0
        (fixedLobeForests m e r0 I J blocks) := by
  intro c hc
  obtain ⟨B, hB, hcB⟩ := List.mem_flatMap.mp hc
  by_cases hv : VariesOnInterval m e r0 I J (B.root m)
  · left
    apply List.mem_flatMap.mpr
    exact ⟨B, (mem_varyingLobeForests_iff m e r0).mpr ⟨hB, hv⟩, hcB⟩
  · right
    apply List.mem_flatMap.mpr
    exact ⟨B, (mem_fixedLobeForests_iff m e r0).mpr ⟨hB, hv⟩, hcB⟩

/-- The varying side is no longer than the original block list. -/
theorem varyingLobeForests_length_le
    (I J : Nat)
    (blocks : List (SupportLobeForestEpoch m e r0 times)) :
    (varyingLobeForests m e r0 I J blocks).length ≤ blocks.length := by
  classical
  unfold varyingLobeForests
  exact List.length_filter_le _ _

/-- Root registers of the fixed side are equal at all selected interval times. -/
theorem fixedLobeForests_roots_fixed
    {I J : Nat}
    (blocks : List (SupportLobeForestEpoch m e r0 times))
    (ks : List Nat)
    (hwithin : ∀ k ∈ ks, I ≤ k ∧ k ≤ J) :
    ∀ x ∈ ks, ∀ y ∈ ks,
      ∀ B ∈ fixedLobeForests m e r0 I J blocks,
      reg m e r0 x (B.root m) = reg m e r0 y (B.root m) := by
  intro x hx y hy B hB
  exact reg_eq_of_not_varies m e r0
    ((mem_fixedLobeForests_iff m e r0).mp hB).2
    (hwithin x hx) (hwithin y hy)

/-- **Automatic mixed bound with a single unsplit lobe-component list.** -/
theorem automatic_all_lobes_epoch_three_quarter
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {I J : Nat} (hIJ : I ≤ J)
    (trees : List (SupportTreeEpoch m e r0 times))
    (lobes : List (SupportLobeForestEpoch m e r0 times))
    (cycles : List (SupportCycleEpoch m e r0 times))
    (residual allCells ks : List Nat)
    (L : Nat)
    (htimes : ∀ k, I ≤ k → k ≤ J → times k)
    (hsupportSteps : ∀ k, I ≤ k → k < J → ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hsupportPairs : ∀ x ∈ ks, ∀ y ∈ ks, ∀ s,
      Occupied m e r0 x s ↔ Occupied m e r0 y s)
    (hwithin : ∀ k ∈ ks, I ≤ k ∧ k ≤ J)
    (hrootsNodup : (lobeForestRoots m e r0 lobes).Nodup)
    (hrootsSub : ∀ c ∈ lobeForestRoots m e r0 lobes,
      c ∈ allCells)
    (hclosed : StarClosed m allCells)
    (hnoGray : ∀ k, I < k → k ≤ J → ¬ GrayTail m e r0 k)
    (hresidualFixed : ∀ x ∈ ks, ∀ y ∈ ks, ∀ c ∈ residual,
      reg m e r0 x c = reg m e r0 y c)
    (hcover : ∀ c ∈ allCells,
      c ∈ automaticTreeCells m e r0 trees ∨
      c ∈ lobeForestCells m e r0 lobes ∨
      c ∈ automaticCycleCells m e r0 cycles ∨ c ∈ residual)
    (hmin : ∀ T ∈ trees, 2 ≤ T.cells.length)
    (hC : allCells.length = L +
      (automaticTreeCells m e r0 trees).length)
    (hlobesL : lobes.length ≤ L)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    fourth ks.length ≤ 2^(3*allCells.length) := by
  let active := varyingLobeForests m e r0 I J lobes
  let fixed := fixedLobeForests m e r0 I J lobes
  apply automatic_mixed_epoch_three_quarter m e r0 hrun hr0 hIJ
    trees active fixed cycles residual allCells ks L
    htimes hsupportSteps hsupportPairs hwithin
  · dsimp [active]
    exact varying_roots_nodup m e r0 I J lobes hrootsNodup
  · dsimp [active]
    exact varying_roots_subset m e r0 I J lobes allCells hrootsSub
  · exact hclosed
  · intro B hB
    exact (mem_varyingLobeForests_iff m e r0).mp hB |>.2
  · exact hnoGray
  · dsimp [fixed]
    exact fixedLobeForests_roots_fixed m e r0 lobes ks hwithin
  · exact hresidualFixed
  · intro c hc
    rcases hcover c hc with ht | hl | hcy | hr
    · exact Or.inl ht
    · rcases lobeForestCells_partition m e r0 I J lobes c hl with ha | hf
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl hf))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hcy)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hr)))
  · exact hmin
  · exact hC
  · exact Nat.le_trans (varyingLobeForests_length_le m e r0 I J lobes)
      hlobesL
  · exact hnd

end Echo
