import SparseArithmeticCore

/-!
# Component-free exact code: full edges plus lobe endpoints

For a fixed-support epoch, encode a state by

1. the full/non-full indicator on a chosen edge list, separated by a zero
   after every full edge; and
2. the exact endpoint selected in each active lobe cell.

If every full indicator has `F` true bits on `E` edges and `E+F=M`, the first
part lies in the sparse universe of length `M`.  The second part has `2^A`
choices.  A supplied replay property then gives an exact state count and the
integer `7/8`-exponent bound.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Full-edge indicator on a chosen edge-representative list. -/
noncomputable def fullBits (edges : List Nat) (k : Nat) : List Bool :=
  edges.map (fun s => decide (Full m e r0 k s))

/-- Full-edge indicator length. -/
theorem fullBits_length (edges : List Nat) (k : Nat) :
    (fullBits m e r0 edges k).length = edges.length := by
  simp [fullBits]

/-- Complete component-free code. -/
noncomputable def sparseFullLobeCode
    (edges lobes : List Nat) (k : Nat) : List Bool × List Nat :=
  (separateTrue (fullBits m e r0 edges k),
    lobeCode m e r0 lobes k)

/-- Cartesian code universe. -/
def sparseFullLobeUniverse
    (M : Nat) (lobes : List Nat) :
    List (List Bool × List Nat) :=
  (sparseVectors M).flatMap fun bits =>
    (lobeUniverse m lobes).map fun lc => (bits, lc)

private theorem sparseLobeRect_length
    (xs : List (List Bool)) (ys : List (List Nat)) :
    (xs.flatMap (fun x => ys.map (fun y => (x, y)))).length =
      xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- Universe size. -/
theorem sparseFullLobeUniverse_length
    (M : Nat) (lobes : List Nat) :
    (sparseFullLobeUniverse m M lobes).length =
      sparseCount M * 2 ^ lobes.length := by
  unfold sparseFullLobeUniverse sparseCount
  rw [sparseLobeRect_length, lobeUniverse_length]

/-- The abstract replay property isolated from the finite counting. -/
def FullLobeDetermines
    (edges lobes cells : List Nat) : Prop :=
  ∀ i, times i → ∀ j, times j,
    (∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s) →
    fullBits m e r0 edges i = fullBits m e r0 edges j →
    lobeCode m e r0 lobes i = lobeCode m e r0 lobes j →
    snap m e r0 cells i = snap m e r0 cells j

/-- Every valid code belongs to the finite universe. -/
theorem sparseFullLobeCode_mem
    (edges lobes : List Nat) (M F : Nat) (k : Nat)
    (hEF : edges.length + F = M)
    (hfull : trueCount (fullBits m e r0 edges k) = F)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ a ∈ lobes, Occupied m e r0 k a) :
    sparseFullLobeCode m e r0 edges lobes k ∈
      sparseFullLobeUniverse m M lobes := by
  unfold sparseFullLobeCode sparseFullLobeUniverse
  apply List.mem_flatMap.mpr
  have hlen : (separateTrue (fullBits m e r0 edges k)).length = M := by
    rw [separateTrue_length, fullBits_length, hfull, hEF]
  refine ⟨separateTrue (fullBits m e r0 edges k), ?_, ?_⟩
  · rw [← hlen]
    exact separateTrue_mem_sparse _
  · exact List.mem_map.mpr
      ⟨lobeCode m e r0 lobes k,
        lobeCode_mem m e r0 lobes k hloop hocc, rfl⟩

/-- Equal separated codes replay the snapshot under `FullLobeDetermines`. -/
theorem sparseFullLobeCode_eq_snap_eq
    (edges lobes cells : List Nat)
    (hdet : FullLobeDetermines m e r0 times edges lobes cells)
    {i j : Nat} (hi : times i) (hj : times j)
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hcode : sparseFullLobeCode m e r0 edges lobes i =
      sparseFullLobeCode m e r0 edges lobes j) :
    snap m e r0 cells i = snap m e r0 cells j := by
  have hsep := congrArg Prod.fst hcode
  have hlobe := congrArg Prod.snd hcode
  have hfull : fullBits m e r0 edges i =
      fullBits m e r0 edges j :=
    separateTrue_injective hsep
  exact hdet i hi j hj hsupport hfull hlobe

private theorem nodup_transfer_sparse
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

private theorem nodup_subset_length_sparse
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

/-- Exact component-free epoch count. -/
theorem sparse_full_lobe_epoch_count
    (edges lobes cells ks : List Nat) (M F : Nat)
    (hdet : FullLobeDetermines m e r0 times edges lobes cells)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      trueCount (fullBits m e r0 edges k) = F)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k ∈ ks, ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ sparseCount M * 2 ^ lobes.length := by
  let code := sparseFullLobeCode m e r0 edges lobes
  have hcodes : (ks.map code).Nodup :=
    nodup_transfer_sparse
      (fun i hi j hj hc =>
        sparseFullLobeCode_eq_snap_eq m e r0 edges lobes cells
          hdet (hks i hi) (hks j hj)
          (hsupport i hi j hj) hc)
      hnd
  have hsub : ∀ z ∈ ks.map code,
      z ∈ sparseFullLobeUniverse m M lobes := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact sparseFullLobeCode_mem m e r0 edges lobes M F k
      hEF (hfull k hk) hloop (hocc k hk)
  have hle := nodup_subset_length_sparse hcodes hsub
  rw [List.length_map, sparseFullLobeUniverse_length] at hle
  exact hle

/-- **Component-free strict-base estimate.** -/
theorem sparse_full_lobe_eighth_bound
    (edges lobes cells ks : List Nat) (C M F : Nat)
    (hdet : FullLobeDetermines m e r0 times edges lobes cells)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      trueCount (fullBits m e r0 edges k) = F)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k ∈ ks, ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hnd : (ks.map (snap m e r0 cells)).Nodup)
    (hC : C = lobes.length + M)
    (hhalf : lobes.length ≤ M) :
    sparseEighth ks.length ≤ 2^(7*C + 8) := by
  have hcount := sparse_full_lobe_epoch_count m e r0
    edges lobes cells ks M F hdet hks hsupport hEF hfull
    hloop hocc hnd
  apply sparse_encoded_eighth_bound_core C lobes.length M ks.length
    hC hhalf
  simpa [Nat.mul_comm] using hcount

end Echo
