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

/-- The same `3/4` estimate from the weaker and more natural star-pair
condition.  It is enough that active lobe bits occupy at most one cell from
each mouth-partner pair, expressed arithmetically as `2*A ≤ C`; no injection
from active lobes specifically into non-lobe cells is required. -/
theorem three_quarter_star_pair_bound
    (C L M A P : Nat)
    (hC : C = L + M)
    (hAL : A ≤ L) (hhalf : 2*A ≤ C)
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

/-- A convenient corollary when every loop cell is charged injectively to a
non-loop star partner, so all `L` loop bits are potentially variable. -/
theorem three_quarter_all_loops
    (C L M P : Nat)
    (hC : C = L + M) (hLM : L ≤ M)
    (hP : P * P ≤ 2^M) :
    fourth (2^L * P) ≤ 2^(3*C) := by
  exact three_quarter_fourth_bound C L M L P hC (Nat.le_refl _) hLM hP

/-- A component profile records `(number of cells, orientation capacity)` for
loop-free support components. -/
def profileCells : List (Nat × Nat) → Nat
  | [] => 0
  | p :: ps => p.1 + profileCells ps

def profileCapacity : List (Nat × Nat) → Nat
  | [] => 1
  | p :: ps => p.2 * profileCapacity ps

/-- Per-component square-root bounds multiply: if every component capacity
`s` satisfies `s² ≤ 2^v`, then the whole profile capacity satisfies
`P² ≤ 2^(sum v)`. -/
theorem profile_capacity_square :
    ∀ parts : List (Nat × Nat),
    (∀ p ∈ parts, p.2 * p.2 ≤ 2^p.1) →
    profileCapacity parts * profileCapacity parts ≤
      2^(profileCells parts) := by
  intro parts
  induction parts with
  | nil =>
      intro _
      simp [profileCapacity, profileCells]
  | cons p ps ih =>
      intro h
      have hp := h p List.mem_cons_self
      have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      unfold profileCapacity profileCells
      calc
        (p.2 * profileCapacity ps) * (p.2 * profileCapacity ps)
            = (p.2*p.2) *
              (profileCapacity ps * profileCapacity ps) := by
                simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ ≤ (2^p.1) * (2^(profileCells ps)) := Nat.mul_le_mul hp ht
        _ = 2^(p.1 + profileCells ps) := (Nat.pow_add 2 _ _).symm

/-- A two-orientation non-loop cycle component has square capacity at most
`2^v` as soon as it has at least two cells. -/
theorem two_orientation_square {v : Nat} (hv : 2 ≤ v) :
    2*2 ≤ 2^v := by
  have h := Nat.pow_le_pow_right (by omega : 0 < 2) hv
  simpa using h

end Echo
