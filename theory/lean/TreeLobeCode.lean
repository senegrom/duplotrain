import ReachReplay

/-!
# Exact fixed-support code: tree markers plus lobe endpoints

For a fixed support epoch:

* every nontrivial tree component is encoded by its unique full edge;
* every persistent lobe cell is encoded by the endpoint currently stored in
  its register.

The first part is injective by `TreeReplay` together with ordinary support
reachability (`ReachReplay`).  The second part has at most two choices per
lobe.  This file constructs the Cartesian code universe, proves exact replay
from equal codes, and derives the `2^(3C/4)` fourth-power bound from
star-pair half-density.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Cells represented by lobe slots. -/
def lobeCells (lobes : List Nat) : List Nat :=
  lobes.map m.cellOf

/-- Exact register values in the listed lobe cells. -/
def lobeCode (lobes : List Nat) (k : Nat) : List Nat :=
  lobes.map (fun a => reg m e r0 k (m.cellOf a))

/-- All endpoint choices for a list of lobe representatives. -/
def lobeUniverse : List Nat → List (List Nat)
  | [] => [[]]
  | a :: rest =>
      (lobeUniverse rest).map (fun tail => a :: tail) ++
      (lobeUniverse rest).map (fun tail => m.bar a :: tail)

/-- The lobe universe has `2^A` entries, counting multiplicity. -/
theorem lobeUniverse_length : ∀ lobes : List Nat,
    (lobeUniverse m lobes).length = 2 ^ lobes.length := by
  intro lobes
  induction lobes with
  | nil => rfl
  | cons a rest ih =>
      simp [lobeUniverse, ih, Nat.pow_succ]
      omega

/-- An occupied lobe register stores one of the two represented endpoints. -/
theorem lobeCode_mem :
    ∀ (lobes : List Nat) (k : Nat),
      (∀ a ∈ lobes, m.cellOf (m.bar a) = m.cellOf a) →
      (∀ a ∈ lobes, Occupied m e r0 k a) →
      lobeCode m e r0 lobes k ∈ lobeUniverse m lobes := by
  intro lobes
  induction lobes with
  | nil =>
      intro k _ _
      exact List.mem_cons_self
  | cons a rest ih =>
      intro k hloop hocc
      have haLoop := hloop a List.mem_cons_self
      have haOcc := hocc a List.mem_cons_self
      have htailLoop : ∀ b ∈ rest,
          m.cellOf (m.bar b) = m.cellOf b := by
        intro b hb
        exact hloop b (List.mem_cons_of_mem _ hb)
      have htailOcc : ∀ b ∈ rest, Occupied m e r0 k b := by
        intro b hb
        exact hocc b (List.mem_cons_of_mem _ hb)
      have htail := ih k htailLoop htailOcc
      have hreg := reg_eq_endpoint_of_occupied_lobe m e r0
        rfl haLoop haOcc
      unfold lobeCode lobeUniverse
      rcases hreg with hreg | hreg
      · apply List.mem_append_left
        exact List.mem_map.mpr
          ⟨lobeCode m e r0 rest k, htail, by rw [hreg]⟩
      · apply List.mem_append_right
        exact List.mem_map.mpr
          ⟨lobeCode m e r0 rest k, htail, by rw [hreg]⟩

/-- Combined tree-marker and lobe-endpoint code. -/
def treeLobeCode
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes : List Nat) (k : Nat) : List Nat × List Nat :=
  (treeCode m e r0 blocks k, lobeCode m e r0 lobes k)

/-- Cartesian universe for the combined code. -/
def treeLobeUniverse
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes : List Nat) : List (List Nat × List Nat) :=
  (treeCodeUniverse m e r0 blocks).flatMap fun tc =>
    (lobeUniverse m lobes).map fun lc => (tc, lc)

private theorem treeLobeRect_length
    (xs : List (List Nat)) (ys : List (List Nat)) :
    (xs.flatMap (fun x => ys.map (fun y => (x, y)))).length =
      xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- Size of the combined Cartesian universe. -/
theorem treeLobeUniverse_length
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes : List Nat) :
    (treeLobeUniverse m e r0 blocks lobes).length =
      treeCapacity m e r0 blocks * 2 ^ lobes.length := by
  unfold treeLobeUniverse
  rw [treeLobeRect_length, treeCodeUniverse_length,
    lobeUniverse_length]

/-- Every valid epoch code lies in the Cartesian universe. -/
theorem treeLobeCode_mem
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes : List Nat) (k : Nat)
    (hk : times k)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ a ∈ lobes, Occupied m e r0 k a) :
    treeLobeCode m e r0 blocks lobes k ∈
      treeLobeUniverse m e r0 blocks lobes := by
  unfold treeLobeCode treeLobeUniverse
  apply List.mem_flatMap.mpr
  refine ⟨treeCode m e r0 blocks k,
    treeCode_mem m e r0 blocks k hk, ?_⟩
  exact List.mem_map.mpr
    ⟨lobeCode m e r0 lobes k,
      lobeCode_mem m e r0 lobes k hloop hocc, rfl⟩

/-- Equality of the exact lobe code is equality of the lobe-cell snapshot. -/
theorem lobeCode_eq_snap_eq
    (lobes : List Nat) {i j : Nat}
    (h : lobeCode m e r0 lobes i = lobeCode m e r0 lobes j) :
    snap m e r0 (lobeCells m lobes) j =
      snap m e r0 (lobeCells m lobes) i := by
  simpa [snap, lobeCode, lobeCells, List.map_map] using h.symm

/-- **Exact replay from equal combined codes.** -/
theorem treeLobeCode_eq_snap_eq
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes : List Nat) {i j : Nat}
    (hi : times i) (hj : times j)
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hcode : treeLobeCode m e r0 blocks lobes i =
      treeLobeCode m e r0 blocks lobes j) :
    snap m e r0
        (treeCells m e r0 blocks ++ lobeCells m lobes) j =
      snap m e r0
        (treeCells m e r0 blocks ++ lobeCells m lobes) i := by
  have htreeCode := congrArg Prod.fst hcode
  have hlobeCode := congrArg Prod.snd hcode
  have htree := treeCode_eq_snap_eq m e r0 hr0 blocks
    hi hj hsupport htreeCode
  have hlobe := lobeCode_eq_snap_eq m e r0 lobes hlobeCode
  unfold snap at htree hlobe ⊢
  simp only [List.map_append]
  rw [htree, hlobe]

private theorem nodup_transfer_combined
    {α β : Type} {f : Nat → α} {g : Nat → β} {ks : List Nat}
    (hinj : ∀ i, i ∈ ks → ∀ j, j ∈ ks →
      g i = g j → f i = f j)
    (hnd : (ks.map f).Nodup) :
    (ks.map g).Nodup := by
  induction ks with
  | nil => simp
  | cons k rest ih =>
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

private theorem nodup_subset_length_combined
    {α : Type} [BEq α] [LawfulBEq α]
    {l S : List α}
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

/-- **Finite exact epoch count.**  Distinct covered register snapshots inject
into the combined code universe. -/
theorem tree_lobe_epoch_count
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes ks : List Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k ∈ ks, ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hnd : (ks.map (snap m e r0
      (treeCells m e r0 blocks ++ lobeCells m lobes))).Nodup) :
    ks.length ≤ treeCapacity m e r0 blocks * 2 ^ lobes.length := by
  let code := treeLobeCode m e r0 blocks lobes
  have hcodes : (ks.map code).Nodup :=
    nodup_transfer_combined
      (fun i hi j hj hc =>
        (treeLobeCode_eq_snap_eq m e r0 hr0 blocks lobes
          (hks i hi) (hks j hj) (hsupport i hi j hj) hc).symm)
      hnd
  have hsub : ∀ z ∈ ks.map code,
      z ∈ treeLobeUniverse m e r0 blocks lobes := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact treeLobeCode_mem m e r0 blocks lobes k
      (hks k hk) hloop (hocc k hk)
  have hle := nodup_subset_length_combined hcodes hsub
  rw [List.length_map, treeLobeUniverse_length] at hle
  exact hle

/-- Fixed-epoch strict-base bound from the exact code count and abstract
capacity/half-density inequalities. -/
theorem tree_lobe_epoch_fourth_bound
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes ks : List Nat) (C : Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k ∈ ks, ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hnd : (ks.map (snap m e r0
      (treeCells m e r0 blocks ++ lobeCells m lobes))).Nodup)
    (hhalf : 2 * lobes.length ≤ C)
    (hcap : treeCapacity m e r0 blocks *
      treeCapacity m e r0 blocks ≤ 2 ^ (C - lobes.length)) :
    fourth ks.length ≤ 2 ^ (3 * C) := by
  have hcount := tree_lobe_epoch_count m e r0 hr0 blocks lobes ks
    hks hsupport hloop hocc hnd
  have hfourth := fourth_mono hcount
  exact Nat.le_trans hfourth
    (half_active_fourth_bound C lobes.length
      (treeCapacity m e r0 blocks) hhalf hcap)

/-- Concrete capacity corollary for nontrivial tree blocks. -/
theorem certified_tree_lobe_epoch_bound
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (blocks : List (TreeBlockCert m e r0 times))
    (lobes ks : List Nat) (C : Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k ∈ ks, ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hnd : (ks.map (snap m e r0
      (treeCells m e r0 blocks ++ lobeCells m lobes))).Nodup)
    (hsize : ∀ b ∈ blocks,
      b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ blocks, 2 ≤ b.cells.length)
    (hC : C = treeCellCount m e r0 blocks + lobes.length)
    (hhalf : 2 * lobes.length ≤ C) :
    fourth ks.length ≤ 2 ^ (3 * C) := by
  apply tree_lobe_epoch_fourth_bound m e r0 hr0 blocks lobes ks C
    hks hsupport hloop hocc hnd hhalf
  have hcap := treeCapacity_square m e r0 blocks hsize hmin
  have hsub : C - lobes.length = treeCellCount m e r0 blocks := by
    omega
  simpa [hsub] using hcap

end Echo
