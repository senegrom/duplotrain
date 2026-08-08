import BlockSparseFixedCount
import EndpointAccountingStandalone
import ProfileCodeBound

/-!
# Abstract fixed-support bound with four-bit sparse blocks

A machine snapshot is encoded by

1. the separated full-edge indicator on a fixed edge list; and
2. an auxiliary Boolean vector, later instantiated by active-lobe bits.

If equal codes replay equal snapshots, then fixed endpoint accounting
`E+F=M`, auxiliary length `A`, and half-density `A≤M` imply

    (# distinct snapshots)^8 ≤ 2^(7(A+M)+18).
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The two true-count definitions agree. -/
theorem blockTrueCount_eq_endpointTrueCount : ∀ bits : List Bool,
    blockTrueCount bits = endpointTrueCount bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [blockTrueCount, endpointTrueCount, ih]

/-- Full-edge plus auxiliary-bit code. -/
open Classical in
noncomputable def blockAbstractCode
    (edges : List Nat) (aux : Nat → List Bool) (k : Nat) :
    List Bool × List Bool :=
  (blockSeparate (endpointFullBits m e r0 edges k), aux k)

/-- Finite Cartesian universe for a projected count `M` and `A` auxiliary
bits. -/
def blockAbstractUniverse (M A : Nat) :
    List (List Bool × List Bool) :=
  (blockSparseUniverse M).flatMap fun full =>
    (boolVectors A).map fun bits => (full, bits)

private theorem blockAbstractRect_length
    (xs ys : List (List Bool)) :
    (xs.flatMap (fun x => ys.map (fun y => (x,y)))).length =
      xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- Universe cardinality. -/
theorem blockAbstractUniverse_length (M A : Nat) :
    (blockAbstractUniverse M A).length =
      (blockSparseUniverse M).length * 2^A := by
  unfold blockAbstractUniverse
  rw [blockAbstractRect_length, boolVectors_length]

/-- Every valid bounded code belongs to the Cartesian universe. -/
theorem blockAbstractCode_mem
    (edges : List Nat) (aux : Nat → List Bool)
    (M A F k : Nat)
    (hEF : edges.length + F = M)
    (hfull : blockTrueCount
      (endpointFullBits m e r0 edges k) = F)
    (haux : (aux k).length = A) :
    blockAbstractCode m e r0 edges aux k ∈
      blockAbstractUniverse M A := by
  unfold blockAbstractCode blockAbstractUniverse
  apply List.mem_flatMap.mpr
  have hlen :
      (blockSeparate (endpointFullBits m e r0 edges k)).length = M := by
    rw [blockSeparate_length, endpointFullBits_length,
      hfull, hEF]
  refine ⟨blockSeparate (endpointFullBits m e r0 edges k), ?_, ?_⟩
  · rw [← hlen]
    exact noAdjacent_mem_blockSparseUniverse _
      (blockSeparate_noAdjacent _)
  · exact List.mem_map.mpr
      ⟨aux k, mem_boolVectors haux, rfl⟩

private theorem blockAbstract_nodup_transfer
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

private theorem blockAbstract_nodup_subset_length
    {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α}
    (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hsub' : ∀ z ∈ rest, z ∈ ys.erase x := by
        intro z hz
        have hzy := hsub z (List.mem_cons_of_mem _ hz)
        have hzx : z ≠ x := fun h => hnd.1 (h ▸ hz)
        exact (List.mem_erase_of_ne hzx).mpr hzy
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- Exact finite count once equal codes replay equal snapshots. -/
theorem block_abstract_epoch_count
    (cells edges ks : List Nat)
    (aux : Nat → List Bool)
    (M A F : Nat)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      blockTrueCount (endpointFullBits m e r0 edges k) = F)
    (haux : ∀ k ∈ ks, (aux k).length = A)
    (hreplay : ∀ i ∈ ks, ∀ j ∈ ks,
      blockAbstractCode m e r0 edges aux i =
        blockAbstractCode m e r0 edges aux j →
      snap m e r0 cells i = snap m e r0 cells j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ (blockSparseUniverse M).length * 2^A := by
  let code := blockAbstractCode m e r0 edges aux
  have hcodes : (ks.map code).Nodup :=
    blockAbstract_nodup_transfer
      (fun i hi j hj hc => hreplay i hi j hj hc)
      hnd
  have hsub : ∀ z ∈ ks.map code,
      z ∈ blockAbstractUniverse M A := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact blockAbstractCode_mem m e r0 edges aux M A F k
      hEF (hfull k hk) (haux k hk)
  have hle := blockAbstract_nodup_subset_length hcodes hsub
  rw [List.length_map, blockAbstractUniverse_length] at hle
  exact hle

/-- **Strict abstract epoch bound.** -/
theorem block_abstract_epoch_eighth_bound
    (cells edges ks : List Nat)
    (aux : Nat → List Bool)
    (C M A F : Nat)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      blockTrueCount (endpointFullBits m e r0 edges k) = F)
    (haux : ∀ k ∈ ks, (aux k).length = A)
    (hreplay : ∀ i ∈ ks, ∀ j ∈ ks,
      blockAbstractCode m e r0 edges aux i =
        blockAbstractCode m e r0 edges aux j →
      snap m e r0 cells i = snap m e r0 cells j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup)
    (hC : C = A + M)
    (hhalf : A ≤ M) :
    blockEighth ks.length ≤ 2^(7*C+18) := by
  have hcount := block_abstract_epoch_count m e r0
    cells edges ks aux M A F hEF hfull haux hreplay hnd
  apply blockSparse_eighth_bound C A M ks.length hC hhalf
  simpa [Nat.mul_comm] using hcount

end Echo
