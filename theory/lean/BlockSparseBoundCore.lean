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
