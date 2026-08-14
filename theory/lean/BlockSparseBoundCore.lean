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

end Echo
