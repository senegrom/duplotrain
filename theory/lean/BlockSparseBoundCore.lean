import ThreeQuarterArithmetic

/-!
# Four-bit sparse blocks: corrected core theorem

Every no-adjacent Boolean string is contained in a block universe with eight
choices per four coordinates.  The explicit prefix certificate below closes
the subtle distinction between no-adjacency of the whole string and of its
first four bits.
-/

namespace Echo

/-- No adjacent pair is simultaneously true. -/
def BlockNoAdjacent : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      ¬ (a = true ∧ b = true) ∧ BlockNoAdjacent (b :: rest)

/-- Tail closure. -/
theorem BlockNoAdjacent.tail {a : Bool} {rest : List Bool}
    (h : BlockNoAdjacent (a :: rest)) : BlockNoAdjacent rest := by
  cases rest with
  | nil => trivial
  | cons b tail =>
      cases tail with
      | nil => trivial
      | cons c tail => exact h.2

/-- Eight possible no-adjacent four-bit blocks. -/
def blockPatterns4 : List (List Bool) :=
  [[false, false, false, false],
   [false, false, false, true],
   [false, false, true, false],
   [false, true, false, false],
   [false, true, false, true],
   [true, false, false, false],
   [true, false, false, true],
   [true, false, true, false]]

theorem blockPatterns4_length : blockPatterns4.length = 8 := rfl

theorem mem_blockPatterns4
    (a b c d : Bool)
    (h : BlockNoAdjacent [a,b,c,d]) :
    [a,b,c,d] ∈ blockPatterns4 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [BlockNoAdjacent, blockPatterns4] at h ⊢

/-- Four-bit block universe, deliberately ignoring cross-block restrictions. -/
def blockUniverseCore : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false], [true]]
  | 2 => [[false,false], [false,true],
          [true,false], [true,true]]
  | 3 => [[false,false,false], [false,false,true],
          [false,true,false], [false,true,true],
          [true,false,false], [true,false,true],
          [true,true,false], [true,true,true]]
  | n+4 =>
      blockPatterns4.flatMap fun p =>
        (blockUniverseCore n).map fun tail => p ++ tail

/-- Every no-adjacent string belongs to the block universe of its length. -/
theorem blockNoAdjacent_mem_universe :
    ∀ bits : List Bool,
      BlockNoAdjacent bits → bits ∈ blockUniverseCore bits.length
  | [], _ => List.mem_cons_self
  | [a], _ => by
      cases a <;> simp [blockUniverseCore]
  | [a,b], _ => by
      cases a <;> cases b <;> simp [blockUniverseCore]
  | [a,b,c], _ => by
      cases a <;> cases b <;> cases c <;>
        simp [blockUniverseCore]
  | a :: b :: c :: d :: rest, h => by
      have hpNo : BlockNoAdjacent [a,b,c,d] := by
        simp only [BlockNoAdjacent]
        exact ⟨h.1, ⟨h.2.1, ⟨h.2.2.1, trivial⟩⟩⟩
      have hp : [a,b,c,d] ∈ blockPatterns4 :=
        mem_blockPatterns4 a b c d hpNo
      have ht : BlockNoAdjacent rest :=
        h.tail.tail.tail.tail
      have hi := blockNoAdjacent_mem_universe rest ht
      have hmem : [a,b,c,d] ++ rest ∈
          blockUniverseCore (rest.length + 4) := by
        change [a,b,c,d] ++ rest ∈
          blockPatterns4.flatMap (fun p =>
            (blockUniverseCore rest.length).map
              (fun tail => p ++ tail))
        apply List.mem_flatMap.mpr
        refine ⟨[a,b,c,d], hp, ?_⟩
        exact List.mem_map.mpr ⟨rest, hi, rfl⟩
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hmem

private theorem blockCore_rect_length
    (xs ys : List (List Bool)) :
    (xs.flatMap (fun x => ys.map (fun y => x ++ y))).length =
      xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- Exactly eightfold growth every four coordinates. -/
theorem blockUniverseCore_add_four (n : Nat) :
    (blockUniverseCore (n+4)).length =
      8 * (blockUniverseCore n).length := by
  simp only [blockUniverseCore]
  rw [blockCore_rect_length, blockPatterns4_length]

private theorem blockCore_nodup_subset_length
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

/-- Count duplicate-free no-adjacent strings of fixed length. -/
theorem blockCore_code_count
    (M : Nat) (codes : List (List Bool))
    (hnd : codes.Nodup)
    (hlen : ∀ bits ∈ codes, bits.length = M)
    (hsparse : ∀ bits ∈ codes, BlockNoAdjacent bits) :
    codes.length ≤ (blockUniverseCore M).length := by
  apply blockCore_nodup_subset_length hnd
  intro bits hb
  rw [← hlen bits hb]
  exact blockNoAdjacent_mem_universe bits (hsparse bits hb)

/-- Fourth-power monotonicity. -/
theorem blockCoreFourth_mono {x y : Nat} (h : x ≤ y) :
    fourth x ≤ fourth y := by
  unfold fourth
  have hs : x*x ≤ y*y := Nat.mul_le_mul h h
  exact Nat.mul_le_mul hs hs

/-- Fourth powers distribute over products. -/
theorem blockCoreFourth_mul (x y : Nat) :
    fourth (x*y) = fourth x * fourth y := by
  simp [fourth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Fourth power of a power of two. -/
theorem blockCoreFourth_two_pow (A : Nat) :
    fourth (2^A) = 2^(4*A) := by
  unfold fourth
  calc
    (2^A * 2^A) * (2^A * 2^A)
        = 2^(A+A) * 2^(A+A) := by
            exact congrArg₂ (fun x y : Nat => x * y)
              (Nat.pow_add 2 A A).symm
              (Nat.pow_add 2 A A).symm
    _ = 2^((A+A)+(A+A)) :=
      (Nat.pow_add 2 (A+A) (A+A)).symm
    _ = 2^(4*A) := by
      congr 1 <;> omega

/-- Three bits of capacity per four coordinates, with a base-case constant. -/
theorem blockUniverseCore_fourth_bound : ∀ n : Nat,
    fourth (blockUniverseCore n).length ≤ 2^(3*n+9)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | n+4 => by
      have ih := blockUniverseCore_fourth_bound n
      rw [blockUniverseCore_add_four]
      calc
        fourth (8 * (blockUniverseCore n).length)
            = 4096 * fourth (blockUniverseCore n).length := by
              simp [fourth,
                Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ 4096 * 2^(3*n+9) :=
          Nat.mul_le_mul_left 4096 ih
        _ = 2^(3*(n+4)+9) := by
          have h4096 : 4096 = 2^12 := by decide
          rw [h4096, ← Nat.pow_add]
          congr 1 <;> omega

/-- Eighth power for the final rational exponent. -/
def blockCoreEighth (x : Nat) : Nat := fourth x * fourth x

/-- Strict arithmetic for an `A`-bit auxiliary fibre over an `M`-coordinate
block-sparse code. -/
theorem blockCore_eighth_bound
    (C A M S : Nat)
    (hC : C = A + M)
    (hAM : A ≤ M)
    (hcount : S ≤ 2^A * (blockUniverseCore M).length) :
    blockCoreEighth S ≤ 2^(7*C+18) := by
  have hs4 := blockCoreFourth_mono hcount
  have hu := blockUniverseCore_fourth_bound M
  have h4 : fourth S ≤ 2^(4*A+3*M+9) := by
    calc
      fourth S ≤ fourth (2^A * (blockUniverseCore M).length) := hs4
      _ = 2^(4*A) * fourth (blockUniverseCore M).length := by
        rw [blockCoreFourth_mul, blockCoreFourth_two_pow]
      _ ≤ 2^(4*A) * 2^(3*M+9) :=
        Nat.mul_le_mul_left _ hu
      _ = 2^(4*A+3*M+9) := by
        rw [← Nat.pow_add]
        congr 1 <;> omega
  unfold blockCoreEighth
  have hsq := Nat.mul_le_mul h4 h4
  have hpow :
      2^(4*A+3*M+9) * 2^(4*A+3*M+9) =
        2^(2*(4*A+3*M+9)) := by
    rw [← Nat.pow_add]
    congr 1 <;> omega
  rw [hpow] at hsq
  have hexp : 2*(4*A+3*M+9) ≤ 7*C+18 := by
    omega
  exact Nat.le_trans hsq
    (Nat.pow_le_pow_right (by omega) hexp)

end Echo
