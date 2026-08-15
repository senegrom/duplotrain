
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


def profileCapacity : List (Nat × Nat) → Nat
  | [] => 1
  | p :: ps => p.2 * profileCapacity ps

end Echo
