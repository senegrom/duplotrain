import HiddenDichotomy

/-!
# Arithmetic for a strict-base exponential bound

The fixed-support strategy separates cells into

* `L` loop/lobe cells, of which at most `A` vary before absorption; and
* `M` non-loop cells, whose component-orientation capacity `P` satisfies
  `P² ≤ 2^M`.

The total capacity is then `2^A * P`.  This file proves the integer form of the
three-quarter exponent estimate

    (2^A * P)^4 ≤ 2^(3*(L+M)).

The estimate follows either from `A ≤ min L M`, or from the weaker and more
natural condition that active lobes occupy at most one endpoint of every mouth
pair: `2*A ≤ L+M`.

No roots, logarithms, reals, Mathlib, or asymptotic notation are needed.
-/

namespace Echo

/-- Fourth power written as a balanced product, convenient for monotone
multiplication. -/
def fourth (x : Nat) : Nat := (x * x) * (x * x)

private theorem fourth_mul (x y : Nat) :
    fourth (x*y) = fourth x * fourth y := by
  unfold fourth
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem fourth_two_pow (A : Nat) :
    fourth (2^A) = 2^(A+A+A+A) := by
  unfold fourth
  simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- The fourth-power form of the `3/4` exponent bound. -/
theorem three_quarter_fourth_bound
    (C L M A P : Nat)
    (hC : C = L + M)
    (hAL : A ≤ L) (hAM : A ≤ M)
    (hP : P * P ≤ 2^M) :
    fourth (2^A * P) ≤ 2^(3*C) := by
  have hP4 : fourth P ≤ 2^(M+M) := by
    unfold fourth
    calc
      (P*P)*(P*P) ≤ (2^M)*(2^M) := Nat.mul_le_mul hP hP
      _ = 2^(M+M) := (Nat.pow_add 2 M M).symm
  have hmul : fourth (2^A) * fourth P ≤
      2^(A+A+A+A) * 2^(M+M) := by
    exact Nat.mul_le_mul (Nat.le_of_eq (fourth_two_pow A)) hP4
  have hexp : (A+A+A+A) + (M+M) ≤ 3*C := by
    omega
  calc
    fourth (2^A * P) = fourth (2^A) * fourth P := fourth_mul _ _
    _ ≤ 2^(A+A+A+A) * 2^(M+M) := hmul
    _ = 2^((A+A+A+A)+(M+M)) := (Nat.pow_add 2 _ _).symm
    _ ≤ 2^(3*C) := Nat.pow_le_pow_right (by omega) hexp

def profileCells : List (Nat × Nat) → Nat
  | [] => 0
  | p :: ps => p.1 + profileCells ps

def profileCapacity : List (Nat × Nat) → Nat
  | [] => 1
  | p :: ps => p.2 * profileCapacity ps

end Echo
