import FullyLoadedTreeImpossible
import TreeLobeNotFullTwoThirds
import AutomaticTreeBlock
import LobeForestBlock

/-!
# Quantitative active-lobe load bound for one support-tree component

Assign a finite list of persistent varying lobe-forest roots to an ordinary
support-tree component by requiring that the mouth partner of each lobe root
lies in the tree.  Distinct lobe roots have distinct partner cells because
`star` is an involution, so their number is at most the tree size.

For a tree of size at least three, equality would load every tree cell.  The
kernel-checked `fully_loaded_tree_impossible` theorem excludes that case.
Thus the pair `(tree size, assigned lobe count)` satisfies `NotFullyLoaded`,
which is exactly the local hypothesis needed by the `2/3` arithmetic.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

private theorem star_injective_load : Function.Injective m.star := by
  intro a b h
  have h' := congrArg m.star h
  simpa only [m.star_invol] using h'

private theorem nodup_map_star
    (xs : List Nat) (hnd : xs.Nodup) :
    (xs.map m.star).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨y, hy, hsy⟩ := List.mem_map.mp hmem
        have hxy : x = y := star_injective_load m hsy.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih hnd.2

private theorem nodup_subset_length_load
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

private theorem nodup_subset_equal_cover
    {xs ys : List Nat}
    (hxnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys)
    (hlen : xs.length = ys.length) :
    ∀ y ∈ ys, y ∈ xs := by
  intro y hy
  apply Classical.byContradiction
  intro hyn
  have hsubErase : ∀ x ∈ xs, x ∈ ys.erase y := by
    intro x hx
    have hxy : x ≠ y := by
      intro h
      apply hyn
      exact h ▸ hx
    exact (List.mem_erase_of_ne hxy).mpr (hsub x hx)
  have hle := nodup_subset_length_load hxnd hsubErase
  have hpos : 0 < ys.length := by
    cases ys with
    | nil => cases hy
    | cons _ _ => simp
  rw [List.length_erase_of_mem hy, hlen] at hle
  omega

variable {I J : Nat}

/-- Mouth-partner cells of a list of lobe-forest components. -/
def lobeForestPartnerCells
    {times : Nat → Prop}
    (lobes : List (SupportLobeForestEpoch m e r0 times)) : List Nat :=
  lobes.map (fun B => m.star (B.root m))

/-- Distinct lobe roots give distinct mouth-partner cells. -/
theorem lobeForestPartnerCells_nodup
    {times : Nat → Prop}
    (lobes : List (SupportLobeForestEpoch m e r0 times))
    (hroots : (lobeForestRoots m e r0 lobes).Nodup) :
    (lobeForestPartnerCells m e r0 lobes).Nodup := by
  have hroots' : (lobes.map (fun B => B.root m)).Nodup := by
    simpa [lobeForestRoots] using hroots
  unfold lobeForestPartnerCells
  exact nodup_map_star m _ hroots'

/-- **One-component load bound.** -/
theorem supportTree_lobe_load_notFullyLoaded
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (T : SupportTreeEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J))
    (lobes : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (hmin : 2 ≤ T.cells.length)
    (hroots : (lobeForestRoots m e r0 lobes).Nodup)
    (hpartners : ∀ B ∈ lobes, m.star (B.root m) ∈ T.cells)
    (houtside : ∀ B ∈ lobes, B.root m ∉ T.cells)
    (hvar : ∀ B ∈ lobes,
      VariesOnInterval m e r0 I J (B.root m)) :
    NotFullyLoaded T.cells.length lobes.length := by
  let partners := lobeForestPartnerCells m e r0 lobes
  have hpartnerNodup : partners.Nodup := by
    dsimp [partners]
    exact lobeForestPartnerCells_nodup m e r0 lobes hroots
  have hpartnerSub : ∀ c ∈ partners, c ∈ T.cells := by
    intro c hc
    dsimp [partners, lobeForestPartnerCells] at hc
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hc
    exact hpartners B hB
  have hle : lobes.length ≤ T.cells.length := by
    have h := nodup_subset_length_load hpartnerNodup hpartnerSub
    simpa [partners, lobeForestPartnerCells] using h
  by_cases htwo : T.cells.length = 2
  · exact Or.inl ⟨htwo, by omega⟩
  · right
    have hthree : 3 ≤ T.cells.length := by omega
    constructor
    · exact hthree
    · apply Nat.lt_of_le_of_ne hle
      intro heq
      have hlen : partners.length = T.cells.length := by
        simpa [partners, lobeForestPartnerCells] using heq
      have hcover : ∀ c ∈ T.cells, c ∈ partners :=
        nodup_subset_equal_cover hpartnerNodup hpartnerSub hlen
      apply fully_loaded_tree_impossible m e r0 hrun hr0
        I J T.cells T.cells_nodup hthree
      · intro k hkI hkJ c hc
        exact T.selected_target_mem m e r0 ⟨hkI, hkJ⟩ hc
      · intro k hkI hkJ c hc
        exact T.selected_nonlobe m e r0 ⟨hkI, hkJ⟩ hc
      · intro c hc
        have hcPartner := hcover c hc
        dsimp [partners, lobeForestPartnerCells] at hcPartner
        obtain ⟨B, hB, hstar⟩ := List.mem_map.mp hcPartner
        have hroot : B.root m = m.star c := by
          have h := congrArg m.star hstar
          rw [m.star_invol] at h
          exact h
        refine ⟨B.rootSlot, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [SupportLobeForestEpoch.root] using hroot
        · exact B.root_lobe
        · intro k hkI hkJ
          exact B.root_occupied m e r0 ⟨hkI, hkJ⟩
        · simpa [SupportLobeForestEpoch.root] using hvar B hB
        · simpa [SupportLobeForestEpoch.root] using houtside B hB

end Echo
