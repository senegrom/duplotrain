import FibonacciSparseBound

/-!
# Monotonicity of the balanced Fibonacci capacity
-/

namespace Echo

/-- The exact sparse count is monotone over arbitrary coordinate extension. -/
theorem fibSparseCount_mono {a b : Nat} (hab : a ≤ b) :
    fibSparseCount a ≤ fibSparseCount b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d :=
    ⟨b - a, by omega⟩
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      have hstep := fibSparseCount_le_succ (a + d)
      exact Nat.le_trans ih (by
        simpa [Nat.add_assoc] using hstep)

/-- Adding one total coordinate cannot decrease the balanced capacity. -/
theorem fibBalancedCapacity_le_succ (C : Nat) :
    fibBalancedCapacity C ≤ fibBalancedCapacity (C+1) := by
  unfold fibBalancedCapacity
  have hexp : C/2 ≤ (C+1)/2 := by omega
  have hidx : (C+1)/2 ≤ (C+2)/2 := by omega
  have hp := Nat.pow_le_pow_right (by omega : 0 < 2) hexp
  have hf := fibSparseCount_mono hidx
  have hm := Nat.mul_le_mul hp hf
  simpa [Nat.add_assoc] using hm

/-- Balanced capacity is monotone in the total number of cells. -/
theorem fibBalancedCapacity_mono {a b : Nat} (hab : a ≤ b) :
    fibBalancedCapacity a ≤ fibBalancedCapacity b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d :=
    ⟨b - a, by omega⟩
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      have hstep := fibBalancedCapacity_le_succ (a + d)
      exact Nat.le_trans ih (by
        simpa [Nat.add_assoc] using hstep)

end Echo
