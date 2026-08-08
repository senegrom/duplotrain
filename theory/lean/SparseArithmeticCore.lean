import SparseFullCode

/-!
# Minimal arithmetic for the sparse full-edge code

This version uses only the tactics already available in the project.  It proves

    sparseCount(n)^4 ≤ 16 · 2^(3n)

and therefore, for `A ≤ M`,

    (2^A · sparseCount(M))^8 ≤ 2^(7(A+M)+8).
-/

namespace Echo

/-- Fourth powers distribute over multiplication. -/
theorem sparse_fourth_mul (x y : Nat) :
    fourth (x*y) = fourth x * fourth y := by
  simp [fourth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Fourth power of a power of two. -/
theorem sparse_fourth_two_pow (A : Nat) :
    fourth (2^A) = 2^(4*A) := by
  simp [fourth, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm]

/-- Sparse Fibonacci growth in fourth-power form. -/
theorem sparseCount_fourth_bound_core : ∀ n : Nat,
    fourth (sparseCount n) ≤ 16 * 2^(3*n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => decide
      | succ n =>
          cases n with
          | zero => decide
          | succ n =>
              cases n with
              | zero => decide
              | succ n =>
                  cases n with
                  | zero => decide
                  | succ d =>
                      have hstep := sparseCount_add_four (d+1)
                      have hmono := fourth_mono hstep
                      have hprev := ih (d+1) (by omega)
                      calc
                        fourth (sparseCount (Nat.succ (Nat.succ
                          (Nat.succ (Nat.succ (Nat.succ d))))))
                            = fourth (sparseCount ((d+1)+4)) := by omega
                        _ ≤ fourth (8 * sparseCount (d+1)) := hmono
                        _ = 4096 * fourth (sparseCount (d+1)) := by
                          simp [sparse_fourth_mul, fourth,
                            Nat.mul_assoc, Nat.mul_comm,
                            Nat.mul_left_comm]
                        _ ≤ 4096 * (16 * 2^(3*(d+1))) :=
                          Nat.mul_le_mul_left 4096 hprev
                        _ = 16 * 2^(3*((d+1)+4)) := by
                          rw [show 3*((d+1)+4) = 3*(d+1)+12 by omega,
                            Nat.pow_add]
                          simp [Nat.mul_assoc, Nat.mul_comm,
                            Nat.mul_left_comm]
                        _ = 16 * 2^(3*(Nat.succ (Nat.succ
                          (Nat.succ (Nat.succ (Nat.succ d)))))) := by
                          omega

/-- Eighth power, used to state the `7/8` exponent integrally. -/
def sparseEighth (x : Nat) : Nat := fourth x * fourth x

/-- Main sparse-code arithmetic. -/
theorem sparse_encoded_eighth_bound_core
    (C A M S : Nat)
    (hC : C = A + M)
    (hAM : A ≤ M)
    (hcount : S ≤ 2^A * sparseCount M) :
    sparseEighth S ≤ 2^(7*C + 8) := by
  have hs4 := fourth_mono hcount
  have hsc := sparseCount_fourth_bound_core M
  have h4 : fourth S ≤ 2^(4*A + 3*M + 4) := by
    calc
      fourth S ≤ fourth (2^A * sparseCount M) := hs4
      _ = 2^(4*A) * fourth (sparseCount M) := by
        rw [sparse_fourth_mul, sparse_fourth_two_pow]
      _ ≤ 2^(4*A) * (16 * 2^(3*M)) :=
        Nat.mul_le_mul_left _ hsc
      _ = 2^(4*A + 3*M + 4) := by
        rw [show 4*A + 3*M + 4 = 4*A + (3*M + 4) by omega,
          Nat.pow_add, Nat.pow_add]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  unfold sparseEighth
  have hsq := Nat.mul_le_mul h4 h4
  have hpow :
      2^(4*A + 3*M + 4) * 2^(4*A + 3*M + 4) =
        2^(2*(4*A + 3*M + 4)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hpow] at hsq
  have hexp : 2*(4*A + 3*M + 4) ≤ 7*C + 8 := by
    omega
  exact Nat.le_trans hsq
    (Nat.pow_le_pow_right (by omega) hexp)

/-- Direct fixed-cardinality code-list form. -/
theorem sparse_code_list_eighth_bound_core
    (C A E F : Nat)
    (codes : List (List Bool))
    (hnd : codes.Nodup)
    (hlen : ∀ bits ∈ codes, bits.length = E)
    (htrue : ∀ bits ∈ codes, trueCount bits = F)
    (hC : C = A + (E+F))
    (hhalf : A ≤ E+F) :
    sparseEighth (2^A * codes.length) ≤ 2^(7*C + 8) := by
  have hc := fixed_full_code_count E F codes hnd hlen htrue
  apply sparse_encoded_eighth_bound_core C A (E+F)
    (2^A * codes.length) hC hhalf
  exact Nat.mul_le_mul_left (2^A) hc

end Echo
