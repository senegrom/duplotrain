import LobeBits
import RootRank

/-!
# A concrete fixed-support code from certified components and lobe bits

This module removes the abstract `codes` hypothesis from
`FixedSupportBound.lean`.  A state is encoded directly by

1. the full-edge marker of every certified tree component; and
2. one Boolean for every active occupied-lobe cell.

Cells outside those two lists may be declared fixed.  Equality of the combined
code then replays the complete register snapshot on any covered cell universe.
The code space has exactly

    treeCapacity * 2^(active.length)

members.  Combining this count with `active_lobes_half` and
`treeCapacity_square` gives the certified fixed-support fourth-power bound

    states^4 ≤ 2^(3 * cells.length)

before the Gray tail.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Tree-marker vector paired with active-lobe bits. -/
def certifiedEpochCode
    (blocks : List (TreeBlockCert m e r0 times))
    (active : List Nat) (slotOf : Nat → Nat) (k : Nat) :
    List Nat × List Bool :=
  (treeCode m e r0 blocks k, lobeBits m e r0 slotOf active k)

/-- Cartesian universe of all certified tree markers and lobe-bit vectors. -/
def certifiedEpochUniverse
    (blocks : List (TreeBlockCert m e r0 times)) (A : Nat) :
    List (List Nat × List Bool) :=
  (treeCodeUniverse m e r0 blocks).flatMap fun tc =>
    (boolVectors A).map fun bits => (tc, bits)

private theorem certifiedRect_length
    (trees : List (List Nat)) (bits : List (List Bool)) :
    (trees.flatMap (fun tc => bits.map (fun bs => (tc,bs)))).length =
      trees.length * bits.length := by
  induction trees with
  | nil => simp
  | cons t rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- Size of the concrete code universe. -/
theorem certifiedEpochUniverse_length
    (blocks : List (TreeBlockCert m e r0 times)) (A : Nat) :
    (certifiedEpochUniverse m e r0 blocks A).length =
      treeCapacity m e r0 blocks * 2^A := by
  unfold certifiedEpochUniverse
  rw [certifiedRect_length, treeCodeUniverse_length, boolVectors_length]

/-- Every certified state code belongs to the concrete universe. -/
theorem certifiedEpochCode_mem
    (blocks : List (TreeBlockCert m e r0 times))
    (active : List Nat) (slotOf : Nat → Nat) {k : Nat}
    (hk : times k) :
    certifiedEpochCode m e r0 blocks active slotOf k ∈
      certifiedEpochUniverse m e r0 blocks active.length := by
  unfold certifiedEpochCode certifiedEpochUniverse
  apply List.mem_flatMap.mpr
  refine ⟨treeCode m e r0 blocks k,
    treeCode_mem m e r0 blocks k hk, ?_⟩
  exact List.mem_map.mpr
    ⟨lobeBits m e r0 slotOf active k,
      mem_boolVectors (lobeBits_length m e r0 slotOf active k), rfl⟩

private theorem pointwise_of_map_eq {α β : Type}
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

/-- Equality of the concrete code replays every covered register. -/
theorem certifiedEpochCode_eq_snap_eq
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (active fixed allCells : List Nat)
    (slotOf : Nat → Nat)
    {i j : Nat}
    (hi : times i) (hj : times j)
    (hsupport : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hslotCell : ∀ c ∈ active, m.cellOf (slotOf c) = c)
    (hslotLobe : ∀ c ∈ active, LobeSlot m (slotOf c))
    (hiOcc : ∀ c ∈ active, Occupied m e r0 i (slotOf c))
    (hjOcc : ∀ c ∈ active, Occupied m e r0 j (slotOf c))
    (hfixed : ∀ c ∈ fixed, reg m e r0 i c = reg m e r0 j c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0 blocks ∨ c ∈ active ∨ c ∈ fixed)
    (hcode : certifiedEpochCode m e r0 blocks active slotOf i =
      certifiedEpochCode m e r0 blocks active slotOf j) :
    snap m e r0 allCells i = snap m e r0 allCells j := by
  have htreeCode := congrArg Prod.fst hcode
  have hlobeCode := congrArg Prod.snd hcode
  unfold certifiedEpochCode at htreeCode hlobeCode
  have htreeSnap : snap m e r0 (treeCells m e r0 blocks) j =
      snap m e r0 (treeCells m e r0 blocks) i :=
    treeCode_eq_snap_eq m e r0 hr0 blocks hi hj hsupport htreeCode
  have hlobeSnap : snap m e r0 active i = snap m e r0 active j :=
    lobeBits_eq_snap_eq m e r0 slotOf active
      hslotCell hslotLobe hiOcc hjOcc hlobeCode
  unfold snap at htreeSnap hlobeSnap ⊢
  apply List.map_congr_left
  intro c hc
  rcases hcover c hc with htree | hlobe | hfixedMem
  · exact (pointwise_of_map_eq (reg m e r0 j) (reg m e r0 i)
      (treeCells m e r0 blocks) htreeSnap c htree).symm
  · exact pointwise_of_map_eq (reg m e r0 i) (reg m e r0 j)
      active hlobeSnap c hlobe
  · exact hfixed c hfixedMem

private theorem nodup_transfer_certified
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

private theorem nodup_subset_length_certified
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

/-- Pairwise-distinct covered snapshots inject into the concrete certified
code universe. -/
theorem certified_epoch_count
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (active fixed allCells ks : List Nat)
    (slotOf : Nat → Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hslotCell : ∀ c ∈ active, m.cellOf (slotOf c) = c)
    (hslotLobe : ∀ c ∈ active, LobeSlot m (slotOf c))
    (hslotOcc : ∀ k ∈ ks, ∀ c ∈ active,
      Occupied m e r0 k (slotOf c))
    (hfixed : ∀ i ∈ ks, ∀ j ∈ ks, ∀ c ∈ fixed,
      reg m e r0 i c = reg m e r0 j c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0 blocks ∨ c ∈ active ∨ c ∈ fixed)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    ks.length ≤ treeCapacity m e r0 blocks * 2^(active.length) := by
  have hcodes : (ks.map
      (certifiedEpochCode m e r0 blocks active slotOf)).Nodup :=
    nodup_transfer_certified
      (fun i hi j hj hc =>
        certifiedEpochCode_eq_snap_eq m e r0 hr0 blocks active fixed
          allCells slotOf (hks i hi) (hks j hj)
          (hsupport i hi j hj) hslotCell hslotLobe
          (hslotOcc i hi) (hslotOcc j hj)
          (hfixed i hi j hj) hcover hc)
      hnd
  have hsub : ∀ z ∈ ks.map
      (certifiedEpochCode m e r0 blocks active slotOf),
      z ∈ certifiedEpochUniverse m e r0 blocks active.length := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact certifiedEpochCode_mem m e r0 blocks active slotOf (hks k hk)
  have hle := nodup_subset_length_certified hcodes hsub
  rw [List.length_map, certifiedEpochUniverse_length] at hle
  exact hle

/-- **Certified pre-Gray fixed-support bound with no abstract code input.** -/
theorem certified_epoch_three_quarter
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j : Nat} (hij : i ≤ j)
    (blocks : List (TreeBlockCert m e r0 times))
    (active fixed allCells ks : List Nat)
    (slotOf : Nat → Nat)
    (L : Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ x ∈ ks, ∀ y ∈ ks, ∀ s,
      Occupied m e r0 x s ↔ Occupied m e r0 y s)
    (hactiveNodup : active.Nodup)
    (hactiveSub : ∀ c ∈ active, c ∈ allCells)
    (hclosed : StarClosed m allCells)
    (hvar : ∀ c ∈ active, VariesOnInterval m e r0 i j c)
    (hslotCell : ∀ c ∈ active, m.cellOf (slotOf c) = c)
    (hslotLobe : ∀ c ∈ active, LobeSlot m (slotOf c))
    (hslotOccInterval : ∀ c ∈ active, ∀ k,
      i ≤ k → k ≤ j → Occupied m e r0 k (slotOf c))
    (hnoGray : ∀ k, i < k → k ≤ j → ¬ GrayTail m e r0 k)
    (hfixed : ∀ x ∈ ks, ∀ y ∈ ks, ∀ c ∈ fixed,
      reg m e r0 x c = reg m e r0 y c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0 blocks ∨ c ∈ active ∨ c ∈ fixed)
    (hwithin : ∀ k ∈ ks, i ≤ k ∧ k ≤ j)
    (hsize : ∀ b ∈ blocks, b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ blocks, 2 ≤ b.cells.length)
    (hC : allCells.length = L + treeCellCount m e r0 blocks)
    (hAL : active.length ≤ L)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    fourth ks.length ≤ 2^(3 * allCells.length) := by
  have hcount := certified_epoch_count m e r0 hr0 blocks active fixed
    allCells ks slotOf hks hsupport hslotCell hslotLobe
    (fun k hk c hc => hslotOccInterval c hc k
      (hwithin k hk).1 (hwithin k hk).2)
    hfixed hcover hnd
  have hhalf : 2 * active.length ≤ allCells.length :=
    active_lobes_half m e r0 hrun hr0 hij allCells active
      hactiveNodup hactiveSub hclosed hvar
      (fun c hc => ⟨slotOf c, hslotCell c hc, hslotLobe c hc,
        hslotOccInterval c hc⟩)
      hnoGray
  have hcap := treeCapacity_square m e r0 blocks hsize hmin
  have hfourth : fourth ks.length ≤
      fourth (2^(active.length) * treeCapacity m e r0 blocks) := by
    apply fourth_mono
    simpa [Nat.mul_comm] using hcount
  exact Nat.le_trans hfourth
    (three_quarter_star_pair_bound allCells.length L
      (treeCellCount m e r0 blocks) active.length
      (treeCapacity m e r0 blocks)
      hC hAL hhalf hcap)

end Echo
