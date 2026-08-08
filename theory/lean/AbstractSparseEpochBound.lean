import SparseCombinatoricsCore
import EndpointAccountingStandalone
import ProfileCodeBound

/-!
# Abstract fixed-support sparse-code bound

This module cleanly separates finite counting from graph extraction.  A state
is encoded by

* the full-edge indicator on `E` represented support edges, containing exactly
  `F` true entries; and
* an arbitrary Boolean vector of length `A`.

If equal codes replay the represented register snapshot, then endpoint
accounting `E+F=M`, half-density `A≤M`, and the standalone sparse theorem imply

    (# distinct snapshots)^8 ≤ 2^(7(A+M)+8).

No component enumeration remains in this counting theorem.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The two Boolean-count functions used by the standalone modules agree. -/
theorem sparseTrueCount_eq_endpointTrueCount : ∀ bits : List Bool,
    sparseTrueCount bits = endpointTrueCount bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [sparseTrueCount, endpointTrueCount, ih]

/-- Full-edge plus auxiliary-bit code. -/
open Classical in
noncomputable def abstractSparseCode
    (edges : List Nat) (bits : Nat → List Bool) (k : Nat) :
    List Bool × List Bool :=
  (sparseSeparateCore (endpointFullBits m e r0 edges k), bits k)

/-- Finite universe for the code. -/
def abstractSparseUniverse (M A : Nat) :
    List (List Bool × List Bool) :=
  (sparseVectorsCore M).flatMap fun full =>
    (boolVectors A).map fun aux => (full, aux)

private theorem abstractSparseRect_length
    (xs ys : List (List Bool)) :
    (xs.flatMap (fun x => ys.map (fun y => (x,y)))).length =
      xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- Code-universe size. -/
theorem abstractSparseUniverse_length (M A : Nat) :
    (abstractSparseUniverse M A).length =
      sparseCountCore M * 2^A := by
  unfold abstractSparseUniverse sparseCountCore
  rw [abstractSparseRect_length, boolVectors_length]

/-- Valid bounded codes lie in the finite universe. -/
theorem abstractSparseCode_mem
    (edges : List Nat) (bits : Nat → List Bool)
    (M A F k : Nat)
    (hEF : edges.length + F = M)
    (hfull : sparseTrueCount
      (endpointFullBits m e r0 edges k) = F)
    (hbits : (bits k).length = A) :
    abstractSparseCode m e r0 edges bits k ∈
      abstractSparseUniverse M A := by
  unfold abstractSparseCode abstractSparseUniverse
  apply List.mem_flatMap.mpr
  have hlen :
      (sparseSeparateCore
        (endpointFullBits m e r0 edges k)).length = M := by
    rw [sparseSeparateCore_length, endpointFullBits_length,
      hfull, hEF]
  refine ⟨sparseSeparateCore
      (endpointFullBits m e r0 edges k), ?_, ?_⟩
  · rw [← hlen]
    exact sparseSeparateCore_mem _
  · exact List.mem_map.mpr
      ⟨bits k, mem_boolVectors hbits, rfl⟩

private theorem abstract_nodup_transfer
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

private theorem abstract_nodup_subset_length
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
theorem abstract_sparse_epoch_count
    (cells edges ks : List Nat)
    (bits : Nat → List Bool)
    (M A F : Nat)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      sparseTrueCount (endpointFullBits m e r0 edges k) = F)
    (hbits : ∀ k ∈ ks, (bits k).length = A)
    (hreplay : ∀ i ∈ ks, ∀ j ∈ ks,
      abstractSparseCode m e r0 edges bits i =
        abstractSparseCode m e r0 edges bits j →
      snap m e r0 cells i = snap m e r0 cells j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ sparseCountCore M * 2^A := by
  let code := abstractSparseCode m e r0 edges bits
  have hcodes : (ks.map code).Nodup :=
    abstract_nodup_transfer
      (fun i hi j hj hc => hreplay i hi j hj hc)
      hnd
  have hsub : ∀ z ∈ ks.map code,
      z ∈ abstractSparseUniverse M A := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact abstractSparseCode_mem m e r0 edges bits M A F k
      hEF (hfull k hk) (hbits k hk)
  have hle := abstract_nodup_subset_length hcodes hsub
  rw [List.length_map, abstractSparseUniverse_length] at hle
  exact hle

/-- **Strict-base fixed-support theorem.** -/
theorem abstract_sparse_epoch_eighth_bound
    (cells edges ks : List Nat)
    (bits : Nat → List Bool)
    (C M A F : Nat)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      sparseTrueCount (endpointFullBits m e r0 edges k) = F)
    (hbits : ∀ k ∈ ks, (bits k).length = A)
    (hreplay : ∀ i ∈ ks, ∀ j ∈ ks,
      abstractSparseCode m e r0 edges bits i =
        abstractSparseCode m e r0 edges bits j →
      snap m e r0 cells i = snap m e r0 cells j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup)
    (hC : C = A + M)
    (hhalf : A ≤ M) :
    sparseCoreEighth ks.length ≤ 2^(7*C + 8) := by
  have hcount := abstract_sparse_epoch_count m e r0
    cells edges ks bits M A F hEF hfull hbits hreplay hnd
  apply sparseCore_eighth_bound C A M ks.length hC hhalf
  simpa [Nat.mul_comm] using hcount

end Echo
