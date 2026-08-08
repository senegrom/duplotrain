import BlockSparseFixedCountCore
import EndpointAccountingStandalone

/-!
# Self-contained abstract block-sparse epoch bound

The code consists of a separated full-edge indicator and an auxiliary Boolean
vector.  Equal codes are assumed to replay equal represented snapshots.  The
finite Cartesian count and the strict `7/8` arithmetic are proved here without
depending on the earlier profile-code modules.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- All Boolean vectors of a fixed length. -/
def blockAuxVectors : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 =>
      (blockAuxVectors n).map (fun v => false :: v) ++
      (blockAuxVectors n).map (fun v => true :: v)

theorem blockAuxVectors_length : ∀ A,
    (blockAuxVectors A).length = 2^A := by
  intro A
  induction A with
  | zero => rfl
  | succ n ih =>
      simp [blockAuxVectors, ih, Nat.pow_succ]
      omega

theorem mem_blockAuxVectors : ∀ {A : Nat} {v : List Bool},
    v.length = A → v ∈ blockAuxVectors A := by
  intro A
  induction A with
  | zero =>
      intro v hv
      have hnil : v = [] := by
        cases v with
        | nil => rfl
        | cons b rest =>
            simp only [List.length_cons] at hv
            omega
      rw [hnil]
      exact List.mem_cons_self
  | succ n ih =>
      intro v hv
      cases v with
      | nil =>
          simp only [List.length_nil] at hv
          omega
      | cons b rest =>
          have hr : rest.length = n := by
            simp only [List.length_cons] at hv
            omega
          cases b with
          | false =>
              unfold blockAuxVectors
              exact List.mem_append_left _
                (List.mem_map.mpr ⟨rest, ih hr, rfl⟩)
          | true =>
              unfold blockAuxVectors
              exact List.mem_append_right _
                (List.mem_map.mpr ⟨rest, ih hr, rfl⟩)

/-- The endpoint and block true counts agree. -/
theorem blockCoreTrueCount_eq_endpoint : ∀ bits : List Bool,
    blockCoreTrueCount bits = endpointTrueCount bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [blockCoreTrueCount, endpointTrueCount, ih]

/-- Full-edge plus auxiliary-bit code. -/
noncomputable def blockCoreAbstractCode
    (m : Machine) (e r0 : Nat → Nat)
    (edges : List Nat) (aux : Nat → List Bool) (k : Nat) :
    List Bool × List Bool :=
  (blockCoreSeparate (endpointFullBits m e r0 edges k), aux k)

/-- Finite Cartesian code universe. -/
def blockCoreAbstractUniverse (M A : Nat) :
    List (List Bool × List Bool) :=
  (blockUniverseCore M).flatMap fun full =>
    (blockAuxVectors A).map fun bits => (full, bits)

private theorem blockCoreAbstract_rect_length
    (xs ys : List (List Bool)) :
    (xs.flatMap (fun x => ys.map (fun y => (x,y)))).length =
      xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- Universe cardinality. -/
theorem blockCoreAbstractUniverse_length (M A : Nat) :
    (blockCoreAbstractUniverse M A).length =
      (blockUniverseCore M).length * 2^A := by
  unfold blockCoreAbstractUniverse
  rw [blockCoreAbstract_rect_length, blockAuxVectors_length]

/-- Every bounded code belongs to the Cartesian universe. -/
theorem blockCoreAbstractCode_mem
    (edges : List Nat) (aux : Nat → List Bool)
    (M A F k : Nat)
    (hEF : edges.length + F = M)
    (hfull : blockCoreTrueCount
      (endpointFullBits m e r0 edges k) = F)
    (haux : (aux k).length = A) :
    blockCoreAbstractCode m e r0 edges aux k ∈
      blockCoreAbstractUniverse M A := by
  unfold blockCoreAbstractCode blockCoreAbstractUniverse
  apply List.mem_flatMap.mpr
  have hlen :
      (blockCoreSeparate
        (endpointFullBits m e r0 edges k)).length = M := by
    rw [blockCoreSeparate_length, endpointFullBits_length,
      hfull, hEF]
  refine ⟨blockCoreSeparate
      (endpointFullBits m e r0 edges k), ?_, ?_⟩
  · rw [← hlen]
    exact blockNoAdjacent_mem_universe _
      (blockCoreSeparate_noAdjacent _)
  · exact List.mem_map.mpr
      ⟨aux k, mem_blockAuxVectors haux, rfl⟩

private theorem blockCoreAbstract_nodup_transfer
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

private theorem blockCoreAbstract_nodup_subset_length
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
theorem blockCore_abstract_epoch_count
    (cells edges ks : List Nat)
    (aux : Nat → List Bool)
    (M A F : Nat)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      blockCoreTrueCount (endpointFullBits m e r0 edges k) = F)
    (haux : ∀ k ∈ ks, (aux k).length = A)
    (hreplay : ∀ i ∈ ks, ∀ j ∈ ks,
      blockCoreAbstractCode m e r0 edges aux i =
        blockCoreAbstractCode m e r0 edges aux j →
      snap m e r0 cells i = snap m e r0 cells j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ (blockUniverseCore M).length * 2^A := by
  let code := blockCoreAbstractCode m e r0 edges aux
  have hcodes : (ks.map code).Nodup :=
    blockCoreAbstract_nodup_transfer
      (fun i hi j hj hc => hreplay i hi j hj hc)
      hnd
  have hsub : ∀ z ∈ ks.map code,
      z ∈ blockCoreAbstractUniverse M A := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact blockCoreAbstractCode_mem m e r0 edges aux M A F k
      hEF (hfull k hk) (haux k hk)
  have hle := blockCoreAbstract_nodup_subset_length hcodes hsub
  rw [List.length_map, blockCoreAbstractUniverse_length] at hle
  exact hle

/-- **Strict abstract block-sparse epoch bound.** -/
theorem blockCore_abstract_epoch_eighth_bound
    (cells edges ks : List Nat)
    (aux : Nat → List Bool)
    (C M A F : Nat)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      blockCoreTrueCount (endpointFullBits m e r0 edges k) = F)
    (haux : ∀ k ∈ ks, (aux k).length = A)
    (hreplay : ∀ i ∈ ks, ∀ j ∈ ks,
      blockCoreAbstractCode m e r0 edges aux i =
        blockCoreAbstractCode m e r0 edges aux j →
      snap m e r0 cells i = snap m e r0 cells j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup)
    (hC : C = A + M)
    (hhalf : A ≤ M) :
    blockCoreEighth ks.length ≤ 2^(7*C+18) := by
  have hcount := blockCore_abstract_epoch_count m e r0
    cells edges ks aux M A F hEF hfull haux hreplay hnd
  apply blockCore_eighth_bound C A M ks.length hC hhalf
  simpa [Nat.mul_comm] using hcount

end Echo
