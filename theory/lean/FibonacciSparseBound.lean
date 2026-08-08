import BlockAbstractEpochBoundCore

/-!
# Fibonacci-exact sparse-code capacity

`BlockSparseBoundCore` deliberately forgets the boundary condition between
four-bit blocks.  That gives eight choices per four coordinates and hence the
`3/4` sparse-coordinate exponent used by the first strict-base proof.

Here we retain the boundary state.  A no-adjacent Boolean word of length
`n+2` either starts with `false` followed by a word of length `n+1`, or starts
with `true,false` followed by a word of length `n`.  Thus its exact finite
universe satisfies the Fibonacci recurrence

    U(0)=1, U(1)=2, U(n+2)=U(n+1)+U(n).

The full abstract code still has an independent `A`-bit auxiliary coordinate,
so one epoch has at most `2^A * U(M)` states.  Under the already-proved
half-density condition `A ≤ M`, this is maximised by balancing the two
coordinates.  We package that exact integer bound as

    B(C) = 2^(C/2) * U((C+1)/2).

Asymptotically `U(M)=F_(M+2)=Theta(phi^M)`, so

    B(C) = O((sqrt (2*phi))^C)

with base about `1.79891`, improving the previous `2^(7C/8)` base
`1.83401`.  No reals or logarithms are used in the Lean theorem itself.
-/

namespace Echo

/-- Exact recursive universe of no-adjacent Boolean words. -/
def fibSparseUniverse : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false], [true]]
  | n+2 =>
      (fibSparseUniverse (n+1)).map (fun bits => false :: bits) ++
      (fibSparseUniverse n).map (fun bits => true :: false :: bits)

/-- Its cardinality.  This is `F_(n+2)` with the convention `F_0=0,F_1=1`. -/
def fibSparseCount (n : Nat) : Nat :=
  (fibSparseUniverse n).length

@[simp] theorem fibSparseCount_zero : fibSparseCount 0 = 1 := rfl
@[simp] theorem fibSparseCount_one : fibSparseCount 1 = 2 := rfl

/-- Fibonacci recurrence for the exact sparse universe. -/
theorem fibSparseCount_rec (n : Nat) :
    fibSparseCount (n+2) =
      fibSparseCount (n+1) + fibSparseCount n := by
  simp [fibSparseCount, fibSparseUniverse]

/-- Every no-adjacent word belongs to the exact recursive universe. -/
theorem blockNoAdjacent_mem_fibSparseUniverse :
    ∀ bits : List Bool,
      BlockNoAdjacent bits →
      bits ∈ fibSparseUniverse bits.length
  | [], _ => by
      simp [fibSparseUniverse]
  | [a], _ => by
      cases a <;> simp [fibSparseUniverse]
  | false :: b :: rest, h => by
      have ht : BlockNoAdjacent (b :: rest) := h.2
      have hi := blockNoAdjacent_mem_fibSparseUniverse (b :: rest) ht
      have hmap : false :: b :: rest ∈
          (fibSparseUniverse (rest.length + 1)).map
            (fun bits => false :: bits) := by
        apply List.mem_map.mpr
        refine ⟨b :: rest, ?_, rfl⟩
        simpa [List.length_cons] using hi
      have hout : false :: b :: rest ∈
          fibSparseUniverse (rest.length + 2) := by
        unfold fibSparseUniverse
        exact List.mem_append_left _ hmap
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hout
  | true :: false :: rest, h => by
      have ht : BlockNoAdjacent rest := BlockNoAdjacent.tail h.2
      have hi := blockNoAdjacent_mem_fibSparseUniverse rest ht
      have hmap : true :: false :: rest ∈
          (fibSparseUniverse rest.length).map
            (fun bits => true :: false :: bits) := by
        exact List.mem_map.mpr ⟨rest, hi, rfl⟩
      have hout : true :: false :: rest ∈
          fibSparseUniverse (rest.length + 2) := by
        unfold fibSparseUniverse
        exact List.mem_append_right _ hmap
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hout
  | true :: true :: rest, h => by
      exact False.elim (h.1 ⟨rfl, rfl⟩)

private theorem fibSparse_nodup_subset_length
    {xs ys : List (List Bool)}
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
      simp only [List.length_cons]
      omega

/-- Exact Fibonacci capacity for duplicate-free no-adjacent words. -/
theorem fibSparse_code_count
    (M : Nat) (codes : List (List Bool))
    (hnd : codes.Nodup)
    (hlen : ∀ bits ∈ codes, bits.length = M)
    (hsparse : ∀ bits ∈ codes, BlockNoAdjacent bits) :
    codes.length ≤ fibSparseCount M := by
  unfold fibSparseCount
  apply fibSparse_nodup_subset_length hnd
  intro bits hb
  rw [← hlen bits hb]
  exact blockNoAdjacent_mem_fibSparseUniverse bits (hsparse bits hb)

/-- The exact sparse count is monotone by one coordinate. -/
theorem fibSparseCount_le_succ : ∀ n : Nat,
    fibSparseCount n ≤ fibSparseCount (n+1)
  | 0 => by decide
  | n+1 => by
      rw [show n + 1 + 1 = n + 2 by omega,
        fibSparseCount_rec n]
      omega

/-- One extra sparse coordinate costs at most a factor two. -/
theorem fibSparseCount_succ_le_two : ∀ n : Nat,
    fibSparseCount (n+1) ≤ 2 * fibSparseCount n
  | 0 => by decide
  | n+1 => by
      rw [show n + 1 + 1 = n + 2 by omega,
        fibSparseCount_rec n]
      have hmono := fibSparseCount_le_succ n
      omega

/-- Balanced exact capacity for a `C=A+M` code under `A ≤ M`. -/
def fibBalancedCapacity (C : Nat) : Nat :=
  2^(C/2) * fibSparseCount ((C+1)/2)

/-- Moving one coordinate from the larger Fibonacci side to the auxiliary
Boolean side never decreases capacity.  Iterating gives the balanced maximum. -/
theorem fibSparse_capacity_balance : ∀ (A d : Nat),
    2^A * fibSparseCount (A+d) ≤
      2^(A + d/2) * fibSparseCount (A + (d+1)/2)
  | A, 0 => by simp
  | A, 1 => by simp
  | A, d+2 => by
      have hgrow := fibSparseCount_succ_le_two (A + d + 1)
      have hshift :
          2^A * fibSparseCount (A + (d+2)) ≤
            2^(A+1) * fibSparseCount ((A+1) + d) := by
        calc
          2^A * fibSparseCount (A + (d+2))
              ≤ 2^A * (2 * fibSparseCount (A+d+1)) := by
                apply Nat.mul_le_mul_left
                simpa [Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hgrow
          _ = 2^(A+1) * fibSparseCount ((A+1)+d) := by
                rw [Nat.pow_succ]
                simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have ih := fibSparse_capacity_balance (A+1) d
      have hexp : (A+1) + d/2 = A + (d+2)/2 := by omega
      have harg : (A+1) + (d+1)/2 = A + ((d+2)+1)/2 := by omega
      calc
        2^A * fibSparseCount (A + (d+2))
            ≤ 2^(A+1) * fibSparseCount ((A+1)+d) := hshift
        _ ≤ 2^((A+1) + d/2) *
              fibSparseCount ((A+1) + (d+1)/2) := ih
        _ = 2^(A + (d+2)/2) *
              fibSparseCount (A + ((d+2)+1)/2) := by
                rw [hexp, harg]

/-- Uniform exact bound in the total coordinate count. -/
theorem fibSparse_capacity_le_balanced
    (C A M : Nat)
    (hC : C = A + M)
    (hAM : A ≤ M) :
    2^A * fibSparseCount M ≤ fibBalancedCapacity C := by
  let d := M - A
  have hM : A + d = M := by
    dsimp [d]
    omega
  have hC' : C = 2*A + d := by
    rw [hC, ← hM]
    omega
  have hdiv : C/2 = A + d/2 := by
    omega
  have hdiv' : (C+1)/2 = A + (d+1)/2 := by
    omega
  have hb := fibSparse_capacity_balance A d
  rw [hM] at hb
  unfold fibBalancedCapacity
  rw [hdiv, hdiv']
  exact hb

/-- Fibonacci-exact Cartesian universe for the full sparse-plus-auxiliary
code used by the epoch replay theorem. -/
def fibBlockCoreAbstractUniverse (M A : Nat) :
    List (List Bool × List Bool) :=
  (fibSparseUniverse M).flatMap fun full =>
    (blockAuxVectors A).map fun bits => (full, bits)

private theorem fibBlockCoreAbstract_rect_length
    (xs ys : List (List Bool)) :
    (xs.flatMap (fun x => ys.map (fun y => (x,y)))).length =
      xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- Exact Cartesian cardinality. -/
theorem fibBlockCoreAbstractUniverse_length (M A : Nat) :
    (fibBlockCoreAbstractUniverse M A).length =
      fibSparseCount M * 2^A := by
  unfold fibBlockCoreAbstractUniverse fibSparseCount
  rw [fibBlockCoreAbstract_rect_length, blockAuxVectors_length]

/-- Every abstract code lies in the Fibonacci-exact universe. -/
theorem fibBlockCoreAbstractCode_mem
    (m : Machine) (e r0 : Nat → Nat)
    (edges : List Nat) (aux : Nat → List Bool)
    (M A F k : Nat)
    (hEF : edges.length + F = M)
    (hfull : blockCoreTrueCount
      (endpointFullBits m e r0 edges k) = F)
    (haux : (aux k).length = A) :
    blockCoreAbstractCode m e r0 edges aux k ∈
      fibBlockCoreAbstractUniverse M A := by
  unfold blockCoreAbstractCode fibBlockCoreAbstractUniverse
  apply List.mem_flatMap.mpr
  have hlen :
      (blockCoreSeparate
        (endpointFullBits m e r0 edges k)).length = M := by
    rw [blockCoreSeparate_length, endpointFullBits_length,
      hfull, hEF]
  refine ⟨blockCoreSeparate
      (endpointFullBits m e r0 edges k), ?_, ?_⟩
  · rw [← hlen]
    exact blockNoAdjacent_mem_fibSparseUniverse _
      (blockCoreSeparate_noAdjacent _)
  · exact List.mem_map.mpr
      ⟨aux k, mem_blockAuxVectors haux, rfl⟩

private theorem fibBlockCoreAbstract_nodup_transfer
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

private theorem fibBlockCoreAbstract_nodup_subset_length
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
      simp only [List.length_cons]
      omega

/-- Exact epoch count before the final balancing step. -/
theorem blockCore_abstract_epoch_fibonacci_count
    (m : Machine) (e r0 : Nat → Nat)
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
    ks.length ≤ fibSparseCount M * 2^A := by
  let code := blockCoreAbstractCode m e r0 edges aux
  have hcodes : (ks.map code).Nodup :=
    fibBlockCoreAbstract_nodup_transfer
      (fun i hi j hj hc => hreplay i hi j hj hc)
      hnd
  have hsub : ∀ z ∈ ks.map code,
      z ∈ fibBlockCoreAbstractUniverse M A := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    exact fibBlockCoreAbstractCode_mem m e r0 edges aux M A F k
      hEF (hfull k hk) (haux k hk)
  have hle := fibBlockCoreAbstract_nodup_subset_length hcodes hsub
  rw [List.length_map, fibBlockCoreAbstractUniverse_length] at hle
  exact hle

/-- **Improved one-epoch bound.**  This is the exact integer replacement for
`blockCore_abstract_epoch_eighth_bound`. -/
theorem blockCore_abstract_epoch_fibonacci_bound
    (m : Machine) (e r0 : Nat → Nat)
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
    ks.length ≤ fibBalancedCapacity C := by
  have hcount := blockCore_abstract_epoch_fibonacci_count
    m e r0 cells edges ks aux M A F hEF hfull haux hreplay hnd
  have hbal := fibSparse_capacity_le_balanced C A M hC hhalf
  exact Nat.le_trans hcount (by
    simpa [Nat.mul_comm] using hbal)

end Echo
