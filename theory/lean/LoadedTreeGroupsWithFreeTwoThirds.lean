import LoadedTreeGroupBudget

/-!
# The two-thirds bound with unassigned active lobe components

Some active lobe-forest roots may have mouth partners in frozen or residual
components rather than in an ordinary tree.  Treat these as `free` lobe bits.
The existing star-pair argument charges two represented cells to each such bit.

The grouped tree/lobe profile still receives the dynamical `NotFullyLoaded`
bound, while every free bit costs two cells.  The arithmetic theorem was
already formulated for exactly this combination, so the resulting exponent
remains `2/3`.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {I J : Nat}

/-- All active lobe forests: group-charged first, then free. -/
def loadedGroupsAllLobes
    (groups : List (LoadedTreeGroup m e r0 I J))
    (free : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J))) :
    List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)) :=
  loadedGroupLobes m e r0 groups ++ free

/-- Exact capacity identity after adding the free Boolean coordinates. -/
theorem loadedGroupsAllLobes_capacity_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (groups : List (LoadedTreeGroup m e r0 I J))
    (free : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J))) :
    treeCapacity m e r0
        (loadedGroupTreeBlocks m e r0 hrun hr0 groups) *
      2^((loadedGroupsAllLobes m e r0 groups free).length) =
    2^free.length *
      notFullLoadedCapacity (loadedGroupProfile m e r0 groups) := by
  have hgroup := loadedGroupProfile_capacity_eq
    m e r0 hrun hr0 groups
  unfold loadedGroupsAllLobes
  rw [List.length_append, Nat.pow_add]
  rw [hgroup]
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- **General mixed fixed-support `2/3` bound.** -/
theorem loaded_groups_with_free_epoch_two_thirds
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (groups : List (LoadedTreeGroup m e r0 I J))
    (free : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (fixed allCells ks : List Nat)
    (hks : ∀ k ∈ ks, I ≤ k ∧ k ≤ J)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfixed : ∀ i ∈ ks, ∀ j ∈ ks, ∀ c ∈ fixed,
      reg m e r0 i c = reg m e r0 j c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0
          (loadedGroupTreeBlocks m e r0 hrun hr0 groups) ∨
      c ∈ lobeForestCells m e r0
          (loadedGroupsAllLobes m e r0 groups free) ∨
      c ∈ fixed)
    (hcellBudget :
      2*free.length +
          notFullLoadedCells (loadedGroupProfile m e r0 groups) ≤
        allCells.length)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    loadedCube ks.length ≤ 2^(2*allCells.length) := by
  let blocks := loadedGroupTreeBlocks m e r0 hrun hr0 groups
  let lobes := loadedGroupsAllLobes m e r0 groups free
  let profile := loadedGroupProfile m e r0 groups
  have hcount := mixed_epoch_count m e r0 hrun hr0
    blocks lobes fixed allCells ks hks hsupport hfixed hcover hnd
  have hcapacity := loadedGroupsAllLobes_capacity_eq
    m e r0 hrun hr0 groups free
  have hcountProfile :
      ks.length ≤ 2^free.length * notFullLoadedCapacity profile := by
    calc
      ks.length ≤ treeCapacity m e r0 blocks * 2^lobes.length := hcount
      _ = 2^free.length *
          notFullLoadedCapacity (loadedGroupProfile m e r0 groups) := by
            dsimp [blocks, lobes]
            exact hcapacity
      _ = 2^free.length * notFullLoadedCapacity profile := by rfl
  have hall : ∀ p ∈ profile, NotFullyLoaded p.1 p.2 := by
    dsimp [profile]
    exact loadedGroupProfile_notFullyLoaded m e r0 hrun hr0 groups
  exact two_thirds_of_not_fully_loaded_profile
    ks.length allCells.length free.length profile
    hcountProfile hall
    (by simpa [profile] using hcellBudget)

/-- Root and mouth-partner cell for each free lobe bit. -/
def freeLobeChargedCells
    (free : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J))) : List Nat :=
  lobeForestRoots m e r0 free ++
    (lobeForestRoots m e r0 free).map m.star

/-- Combined charged-cell list for grouped and free coordinates. -/
def loadedGroupsWithFreeChargedCells
    (groups : List (LoadedTreeGroup m e r0 I J))
    (free : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J))) : List Nat :=
  loadedGroupChargedCells m e r0 groups ++
    freeLobeChargedCells m e r0 free

/-- Exact combined cell cost. -/
theorem loadedGroupsWithFreeChargedCells_length
    (groups : List (LoadedTreeGroup m e r0 I J))
    (free : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J))) :
    (loadedGroupsWithFreeChargedCells m e r0 groups free).length =
      2*free.length +
        notFullLoadedCells (loadedGroupProfile m e r0 groups) := by
  unfold loadedGroupsWithFreeChargedCells freeLobeChargedCells
  rw [List.length_append, loadedGroupChargedCells_length]
  have hroots :
      (lobeForestRoots m e r0 free).length = free.length := by
    simp [lobeForestRoots]
  rw [List.length_append, List.length_map, hroots]
  omega

private theorem allCharged_nodup_subset_length
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

/-- The partition-form corollary with free lobe components. -/
theorem loaded_groups_with_free_epoch_two_thirds_of_charged_cells
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (groups : List (LoadedTreeGroup m e r0 I J))
    (free : List (SupportLobeForestEpoch m e r0
      (fun k => I ≤ k ∧ k ≤ J)))
    (fixed allCells ks : List Nat)
    (hks : ∀ k ∈ ks, I ≤ k ∧ k ≤ J)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfixed : ∀ i ∈ ks, ∀ j ∈ ks, ∀ c ∈ fixed,
      reg m e r0 i c = reg m e r0 j c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0
          (loadedGroupTreeBlocks m e r0 hrun hr0 groups) ∨
      c ∈ lobeForestCells m e r0
          (loadedGroupsAllLobes m e r0 groups free) ∨
      c ∈ fixed)
    (hchargedNodup :
      (loadedGroupsWithFreeChargedCells m e r0 groups free).Nodup)
    (hchargedSub : ∀ c ∈
      loadedGroupsWithFreeChargedCells m e r0 groups free,
      c ∈ allCells)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    loadedCube ks.length ≤ 2^(2*allCells.length) := by
  have hlen := allCharged_nodup_subset_length
    hchargedNodup hchargedSub
  rw [loadedGroupsWithFreeChargedCells_length] at hlen
  exact loaded_groups_with_free_epoch_two_thirds
    m e r0 hrun hr0 groups free fixed allCells ks
    hks hsupport hfixed hcover hlen hnd

end Echo
