import ThreeQuarterArithmetic

/-!
# Sparse full-edge indicators by four-bit blocks

A Boolean string with no adjacent `true` values has only eight possible
four-bit prefixes.  Splitting into blocks of four therefore gives a finite
universe whose size multiplies by exactly eight every four coordinates.

This yields the simple bound

    sparseUniverse(n)^4 ≤ 2^(3n+9).

If a complete state additionally carries `A` Boolean lobe bits and `A ≤ M`,
then any code family of size at most `2^A * sparseUniverse(M)` satisfies

    size^8 ≤ 2^(7(A+M)+18).

Thus, up to a constant factor, the state count is at most `2^(7N/8)`.
-/

namespace Echo

/-- No adjacent pair is simultaneously true. -/
def NoAdjacent : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      ¬ (a = true ∧ b = true) ∧ NoAdjacent (b :: rest)

/-- Tails of no-adjacent strings remain no-adjacent. -/
theorem NoAdjacent.tail {a : Bool} {rest : List Bool}
    (h : NoAdjacent (a :: rest)) : NoAdjacent rest := by
  cases rest with
  | nil => trivial
  | cons b tail =>
      cases tail with
      | nil => trivial
      | cons c tail => exact h.2

/-- The eight no-adjacent patterns of length four. -/
def sparsePatterns4 : List (List Bool) :=
  [[false, false, false, false],
   [false, false, false, true],
   [false, false, true, false],
   [false, true, false, false],
   [false, true, false, true],
   [true, false, false, false],
   [true, false, false, true],
   [true, false, true, false]]

theorem sparsePatterns4_length : sparsePatterns4.length = 8 := rfl

/-- Every no-adjacent four-bit block is one of the eight patterns. -/
theorem mem_sparsePatterns4
    (a b c d : Bool)
    (h : NoAdjacent [a,b,c,d]) :
    [a,b,c,d] ∈ sparsePatterns4 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [NoAdjacent, sparsePatterns4] at h ⊢

/-- An over-approximating universe, grouped into four-bit blocks. -/
def blockSparseUniverse : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false], [true]]
  | 2 => [[false,false], [false,true],
          [true,false], [true,true]]
  | 3 => [[false,false,false], [false,false,true],
          [false,true,false], [false,true,true],
          [true,false,false], [true,false,true],
          [true,true,false], [true,true,true]]
  | n+4 =>
      sparsePatterns4.flatMap fun p =>
        (blockSparseUniverse n).map fun tail => p ++ tail

/-- Every no-adjacent string belongs to the block universe of its length. -/
theorem noAdjacent_mem_blockSparseUniverse :
    ∀ bits : List Bool,
      NoAdjacent bits →
      bits ∈ blockSparseUniverse bits.length
  | [], _ => List.mem_cons_self
  | [a], _ => by
      cases a <;> simp [blockSparseUniverse]
  | [a,b], _ => by
      cases a <;> cases b <;> simp [blockSparseUniverse]
  | [a,b,c], _ => by
      cases a <;> cases b <;> cases c <;>
        simp [blockSparseUniverse]
  | a :: b :: c :: d :: rest, h => by
      have hp : [a,b,c,d] ∈ sparsePatterns4 :=
        mem_sparsePatterns4 a b c d h
      have ht : NoAdjacent rest :=
        h.tail.tail.tail.tail
      have hi := noAdjacent_mem_blockSparseUniverse rest ht
      change [a,b,c,d] ++ rest ∈
        blockSparseUniverse (rest.length + 4)
      unfold blockSparseUniverse
      apply List.mem_flatMap.mpr
      refine ⟨[a,b,c,d], hp, ?_⟩
      exact List.mem_map.mpr ⟨rest, hi, rfl⟩

private theorem blockRect_length
    (xs ys : List (List Bool)) :
    (xs.flatMap (fun x => ys.map (fun y => x ++ y))).length =
      xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- Four new coordinates multiply the universe by exactly eight. -/
theorem blockSparseUniverse_add_four (n : Nat) :
    (blockSparseUniverse (n+4)).length =
      8 * (blockSparseUniverse n).length := by
  rw [show n+4 = n+4 by rfl]
  unfold blockSparseUniverse
  rw [blockRect_length, sparsePatterns4_length]

private theorem block_nodup_subset_length
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
      have hpos : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- Duplicate-free no-adjacent strings of length `M` fit in the block
universe. -/
theorem blockSparse_code_count
    (M : Nat) (codes : List (List Bool))
    (hnd : codes.Nodup)
    (hlen : ∀ bits ∈ codes, bits.length = M)
    (hsparse : ∀ bits ∈ codes, NoAdjacent bits) :
    codes.length ≤ (blockSparseUniverse M).length := by
  apply block_nodup_subset_length hnd
  intro bits hb
  rw [← hlen bits hb]
  exact noAdjacent_mem_blockSparseUniverse bits (hsparse bits hb)

/-- Fourth-power monotonicity. -/
theorem blockFourth_mono {x y : Nat} (h : x ≤ y) :
    fourth x ≤ fourth y := by
  unfold fourth
  have hs : x*x ≤ y*y := Nat.mul_le_mul h h
  exact Nat.mul_le_mul hs hs

/-- Fourth powers distribute over multiplication. -/
theorem blockFourth_mul (x y : Nat) :
    fourth (x*y) = fourth x * fourth y := by
  simp [fourth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Fourth power of a power of two. -/
theorem blockFourth_two_pow (A : Nat) :
    fourth (2^A) = 2^(4*A) := by
  unfold fourth
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega

/-- The four-bit block universe has three-bit-per-four-bit growth. -/
theorem blockSparseUniverse_fourth_bound : ∀ n : Nat,
    fourth (blockSparseUniverse n).length ≤ 2^(3*n+9)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | n+4 => by
      have ih := blockSparseUniverse_fourth_bound n
      have hlen := blockSparseUniverse_add_four n
      rw [hlen]
      calc
        fourth (8 * (blockSparseUniverse n).length)
            = 4096 * fourth (blockSparseUniverse n).length := by
              simp [blockFourth_mul, fourth,
                Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ 4096 * 2^(3*n+9) :=
          Nat.mul_le_mul_left 4096 ih
        _ = 2^(3*(n+4)+9) := by
          rw [show 3*(n+4)+9 = (3*n+9)+12 by omega,
            Nat.pow_add]
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Eighth power used for the final rational exponent. -/
def blockEighth (x : Nat) : Nat := fourth x * fourth x

/-- **Strict block-code arithmetic.** -/
theorem blockSparse_eighth_bound
    (C A M S : Nat)
    (hC : C = A + M)
    (hAM : A ≤ M)
    (hcount : S ≤ 2^A * (blockSparseUniverse M).length) :
    blockEighth S ≤ 2^(7*C+18) := by
  have hs4 := blockFourth_mono hcount
  have hu := blockSparseUniverse_fourth_bound M
  have h4 : fourth S ≤ 2^(4*A+3*M+9) := by
    calc
      fourth S ≤ fourth (2^A * (blockSparseUniverse M).length) := hs4
      _ = 2^(4*A) * fourth (blockSparseUniverse M).length := by
        rw [blockFourth_mul, blockFourth_two_pow]
      _ ≤ 2^(4*A) * 2^(3*M+9) :=
        Nat.mul_le_mul_left _ hu
      _ = 2^(4*A+3*M+9) := by
        rw [← Nat.pow_add]
        congr 1
        omega
  unfold blockEighth
  have hsq := Nat.mul_le_mul h4 h4
  have hpow :
      2^(4*A+3*M+9) * 2^(4*A+3*M+9) =
        2^(2*(4*A+3*M+9)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hpow] at hsq
  have hexp : 2*(4*A+3*M+9) ≤ 7*C+18 := by
    omega
  exact Nat.le_trans hsq
    (Nat.pow_le_pow_right (by omega) hexp)

end Echo
