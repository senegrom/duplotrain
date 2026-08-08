import LobeForestActive

/-!
# Fixed-support coding with lobe-rooted attached forests

The complete fixed-support code now has two parts:

1. one full-edge marker for every ordinary tree component; and
2. one Boolean root register for every varying lobe-forest component.

Boundary replay shows that this single lobe bit also determines every tree
attached to the lobe root.  Non-lobe unicyclic components and lobe forests
whose roots do not vary are folded into the fixed part.

Thus the concrete code space has size

    treeCapacity * 2^(number of varying lobe roots),

and mouth-pair independence of those roots yields the same three-quarter
exponent.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Concrete mixed code: ordinary-tree markers and lobe-forest root bits. -/
def mixedEpochCode
    (trees : List (TreeBlockCert m e r0 times))
    (lobes : List (SupportLobeForestEpoch m e r0 times))
    (k : Nat) : List Nat × List Bool :=
  (treeCode m e r0 trees k, lobeForestBits m e r0 lobes k)

/-- Cartesian universe for the mixed code. -/
def mixedEpochUniverse
    (trees : List (TreeBlockCert m e r0 times))
    (A : Nat) : List (List Nat × List Bool) :=
  (treeCodeUniverse m e r0 trees).flatMap fun tc =>
    (boolVectors A).map fun bits => (tc,bits)

private theorem mixedRect_length
    (trees : List (List Nat)) (bits : List (List Bool)) :
    (trees.flatMap (fun tc => bits.map (fun bs => (tc,bs)))).length =
      trees.length * bits.length := by
  induction trees with
  | nil => simp
  | cons t rest ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem mixedEpochUniverse_length
    (trees : List (TreeBlockCert m e r0 times)) (A : Nat) :
    (mixedEpochUniverse m e r0 trees A).length =
      treeCapacity m e r0 trees * 2^A := by
  unfold mixedEpochUniverse
  rw [mixedRect_length, treeCodeUniverse_length, boolVectors_length]

/-- Every mixed code belongs to its finite universe. -/
theorem mixedEpochCode_mem
    (trees : List (TreeBlockCert m e r0 times))
    (lobes : List (SupportLobeForestEpoch m e r0 times))
    {k : Nat} (hk : times k) :
    mixedEpochCode m e r0 trees lobes k ∈
      mixedEpochUniverse m e r0 trees lobes.length := by
  unfold mixedEpochCode mixedEpochUniverse
  apply List.mem_flatMap.mpr
  refine ⟨treeCode m e r0 trees k,
    treeCode_mem m e r0 trees k hk, ?_⟩
  exact List.mem_map.mpr
    ⟨lobeForestBits m e r0 lobes k,
      mem_boolVectors (lobeForestBits_length m e r0 lobes k), rfl⟩

private theorem pointwise_of_map_eq_mixed {α β : Type}
    (f g : α → β) :
    ∀ (xs : List α), xs.map f = xs.map g →
      ∀ x ∈ xs, f x = g x := by
  intro xs
  induction xs with
  | nil => intro h x hx; cases hx
  | cons y rest ih =>
      intro h x hx
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h.1
      · exact ih h.2 x hx

/-- Equal mixed codes replay every covered register. -/
theorem mixedEpochCode_eq_snap_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (trees : List (TreeBlockCert m e r0 times))
    (lobes : List (SupportLobeForestEpoch m e r0 times))
    (fixed allCells : List Nat)
    {i j : Nat} (hi : times i) (hj : times j)
    (hsupport : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfixed : ∀ c ∈ fixed, reg m e r0 i c = reg m e r0 j c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0 trees ∨
      c ∈ lobeForestCells m e r0 lobes ∨ c ∈ fixed)
    (hcode : mixedEpochCode m e r0 trees lobes i =
      mixedEpochCode m e r0 trees lobes j) :
    snap m e r0 allCells i = snap m e r0 allCells j := by
  have htreeCode := congrArg Prod.fst hcode
  have hlobeCode := congrArg Prod.snd hcode
  unfold mixedEpochCode at htreeCode hlobeCode
  have htreeSnap : snap m e r0 (treeCells m e r0 trees) j =
      snap m e r0 (treeCells m e r0 trees) i :=
    treeCode_eq_snap_eq m e r0 hr0 trees hi hj hsupport htreeCode
  have hlobeSnap : snap m e r0 (lobeForestCells m e r0 lobes) i =
      snap m e r0 (lobeForestCells m e r0 lobes) j :=
    lobeForestBits_eq_snap_eq m e r0 hrun hr0 lobes
      hi hj hsupport hlobeCode
  unfold snap at htreeSnap hlobeSnap ⊢
  apply List.map_congr_left
  intro c hc
  rcases hcover c hc with ht | hl | hf
  · exact (pointwise_of_map_eq_mixed (reg m e r0 j) (reg m e r0 i)
      (treeCells m e r0 trees) htreeSnap c ht).symm
  · exact pointwise_of_map_eq_mixed (reg m e r0 i) (reg m e r0 j)
      (lobeForestCells m e r0 lobes) hlobeSnap c hl
  · exact hfixed c hf

private theorem nodup_transfer_mixed
    {f : Nat → List Nat} {g : Nat → List Nat × List Bool} :
    ∀ {ks : List Nat},
      (∀ i, i ∈ ks → ∀ j, j ∈ ks → g i = g j → f i = f j) →
      (ks.map f).Nodup → (ks.map g).Nodup := by
  intro ks
  induction ks with
  | nil => intro h hnd; simp
  | cons k rest ih =>
      intro hinj hnd
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      constructor
      · intro hm
        obtain ⟨j, hj, hgj⟩ := List.mem_map.mp hm
        have hfj := hinj k List.mem_cons_self j
          (List.mem_cons_of_mem _ hj) hgj.symm
        exact hnd.1 (List.mem_map.mpr ⟨j, hj, hfj.symm⟩)
      · exact ih
          (fun i hi j hj => hinj i (List.mem_cons_of_mem _ hi)
            j (List.mem_cons_of_mem _ hj)) hnd.2

private theorem nodup_subset_length_mixed
    {l S : List (List Nat × List Bool)}
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ S) :
    l.length ≤ S.length := by
  induction l generalizing S with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ S.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- Distinct covered snapshots inject into the mixed code universe. -/
theorem mixed_epoch_count
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (trees : List (TreeBlockCert m e r0 times))
    (lobes : List (SupportLobeForestEpoch m e r0 times))
    (fixed allCells ks : List Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfixed : ∀ i ∈ ks, ∀ j ∈ ks, ∀ c ∈ fixed,
      reg m e r0 i c = reg m e r0 j c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0 trees ∨
      c ∈ lobeForestCells m e r0 lobes ∨ c ∈ fixed)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    ks.length ≤ treeCapacity m e r0 trees * 2^(lobes.length) := by
  have hcodes : (ks.map (mixedEpochCode m e r0 trees lobes)).Nodup :=
    nodup_transfer_mixed
      (fun i hi j hj hc =>
        mixedEpochCode_eq_snap_eq m e r0 hrun hr0 trees lobes
          fixed allCells (hks i hi) (hks j hj)
          (hsupport i hi j hj) (hfixed i hi j hj) hcover hc)
      hnd
  have hsub : ∀ z ∈ ks.map (mixedEpochCode m e r0 trees lobes),
      z ∈ mixedEpochUniverse m e r0 trees lobes.length := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact mixedEpochCode_mem m e r0 trees lobes (hks k hk)
  have hle := nodup_subset_length_mixed hcodes hsub
  rw [List.length_map, mixedEpochUniverse_length] at hle
  exact hle

/-- **Certified mixed pre-Gray bound.** -/
theorem mixed_epoch_three_quarter
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {I J : Nat} (hIJ : I ≤ J)
    (trees : List (TreeBlockCert m e r0 times))
    (lobes : List (SupportLobeForestEpoch m e r0 times))
    (fixed allCells ks : List Nat)
    (L : Nat)
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
    (hrootsNodup : (lobeForestRoots m e r0 lobes).Nodup)
    (hrootsSub : ∀ c ∈ lobeForestRoots m e r0 lobes,
      c ∈ allCells)
    (hclosed : StarClosed m allCells)
    (hvar : ∀ B ∈ lobes,
      VariesOnInterval m e r0 I J (B.root m))
    (hnoGray : ∀ k, I < k → k ≤ J → ¬ GrayTail m e r0 k)
    (hsize : ∀ b ∈ trees, b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ trees, 2 ≤ b.cells.length)
    (hC : allCells.length = L + treeCellCount m e r0 trees)
    (hAL : lobes.length ≤ L)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    fourth ks.length ≤ 2^(3*allCells.length) := by
  have hcount := mixed_epoch_count m e r0 hrun hr0 trees lobes
    fixed allCells ks hks hsupport hfixed hcover hnd
  have hhalf : 2 * lobes.length ≤ allCells.length :=
    active_lobe_forests_half m e r0 hrun hr0 hIJ allCells lobes
      hrootsNodup hrootsSub hclosed htimes hvar hnoGray
  have hcap := treeCapacity_square m e r0 trees hsize hmin
  have hfourth : fourth ks.length ≤
      fourth (2^(lobes.length) * treeCapacity m e r0 trees) := by
    apply fourth_mono
    simpa [Nat.mul_comm] using hcount
  exact Nat.le_trans hfourth
    (three_quarter_star_pair_bound allCells.length L
      (treeCellCount m e r0 trees) lobes.length
      (treeCapacity m e r0 trees) hC hAL hhalf hcap)

/-- **Automatic mixed bound from tree, lobe-forest and frozen component
blocks.** -/
theorem automatic_mixed_epoch_three_quarter
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {I J : Nat} (hIJ : I ≤ J)
    (trees : List (SupportTreeEpoch m e r0 times))
    (activeLobes fixedLobes :
      List (SupportLobeForestEpoch m e r0 times))
    (cycles : List (SupportCycleEpoch m e r0 times))
    (residual allCells ks : List Nat)
    (L : Nat)
    (htimes : ∀ k, I ≤ k → k ≤ J → times k)
    (hsupportSteps : ∀ k, I ≤ k → k < J → ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hsupportPairs : ∀ x ∈ ks, ∀ y ∈ ks, ∀ s,
      Occupied m e r0 x s ↔ Occupied m e r0 y s)
    (hwithin : ∀ k ∈ ks, I ≤ k ∧ k ≤ J)
    (hrootsNodup : (lobeForestRoots m e r0 activeLobes).Nodup)
    (hrootsSub : ∀ c ∈ lobeForestRoots m e r0 activeLobes,
      c ∈ allCells)
    (hclosed : StarClosed m allCells)
    (hvar : ∀ B ∈ activeLobes,
      VariesOnInterval m e r0 I J (B.root m))
    (hnoGray : ∀ k, I < k → k ≤ J → ¬ GrayTail m e r0 k)
    (hfixedLobeRoots : ∀ x ∈ ks, ∀ y ∈ ks,
      ∀ B ∈ fixedLobes,
      reg m e r0 x (B.root m) = reg m e r0 y (B.root m))
    (hresidualFixed : ∀ x ∈ ks, ∀ y ∈ ks, ∀ c ∈ residual,
      reg m e r0 x c = reg m e r0 y c)
    (hcover : ∀ c ∈ allCells,
      c ∈ automaticTreeCells m e r0 trees ∨
      c ∈ lobeForestCells m e r0 activeLobes ∨
      c ∈ lobeForestCells m e r0 fixedLobes ∨
      c ∈ automaticCycleCells m e r0 cycles ∨ c ∈ residual)
    (hmin : ∀ T ∈ trees, 2 ≤ T.cells.length)
    (hC : allCells.length = L +
      (automaticTreeCells m e r0 trees).length)
    (hAL : activeLobes.length ≤ L)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    fourth ks.length ≤ 2^(3*allCells.length) := by
  let treeBlocks := automaticTreeBlocks m e r0 hrun hr0 trees
  let fixed := lobeForestCells m e r0 fixedLobes ++
    automaticCycleCells m e r0 cycles ++ residual
  have hfixed : ∀ x ∈ ks, ∀ y ∈ ks, ∀ c ∈ fixed,
      reg m e r0 x c = reg m e r0 y c := by
    intro x hx y hy c hc
    dsimp [fixed] at hc
    simp only [List.mem_append] at hc
    rcases hc with hpre | hr
    · rcases hpre with hlf | hcy
      · obtain ⟨B, hB, hcB⟩ := List.mem_flatMap.mp hlf
        have hsnap := B.root_reg_eq_snap_eq m e r0 hrun hr0
          (htimes x (hwithin x hx).1 (hwithin x hx).2)
          (hsupportPairs x hx y hy)
          (by exact (hfixedLobeRoots x hx y hy B hB).symm)
        unfold snap at hsnap
        exact (pointwise_of_map_eq_mixed (reg m e r0 y) (reg m e r0 x)
          B.cells hsnap c hcB).symm
      · exact automaticCycleCells_fixed m e r0 hrun hr0 cycles hIJ
          htimes hsupportSteps ks hwithin x hx y hy c hcy
    · exact hresidualFixed x hx y hy c hr
  have hcover' : ∀ c ∈ allCells,
      c ∈ treeCells m e r0 treeBlocks ∨
      c ∈ lobeForestCells m e r0 activeLobes ∨ c ∈ fixed := by
    intro c hc
    rcases hcover c hc with ht | ha | hfl | hcy | hr
    · left
      dsimp [treeBlocks]
      rw [automaticTreeBlocks_cells m e r0 hrun hr0 trees]
      exact ht
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr
        (List.mem_append_left _ (List.mem_append_left _ hfl)))
    · exact Or.inr (Or.inr
        (List.mem_append_left _ (List.mem_append_right _ hcy)))
    · exact Or.inr (Or.inr
        (List.mem_append_right _ hr))
  have hC' : allCells.length = L +
      treeCellCount m e r0 treeBlocks := by
    dsimp [treeBlocks]
    rw [automaticTreeBlocks_cellCount m e r0 hrun hr0 trees]
    exact hC
  exact mixed_epoch_three_quarter m e r0 hrun hr0 hIJ
    treeBlocks activeLobes fixed allCells ks L htimes
    (fun k hk => htimes k (hwithin k hk).1 (hwithin k hk).2)
    hwithin hsupportPairs hfixed hcover'
    hrootsNodup hrootsSub hclosed hvar hnoGray
    (by
      dsimp [treeBlocks]
      exact automaticTreeBlocks_size m e r0 hrun hr0 trees)
    (by
      intro b hb
      dsimp [treeBlocks] at hb
      obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hb
      exact hmin T hT)
    hC' hAL hnd

end Echo
