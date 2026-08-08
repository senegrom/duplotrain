import SparseFullCode

/-!
# Arithmetic for the component-free sparse-code bound

The sparse-vector recurrence satisfies

    a(n+4) ≤ 8 a(n).

Consequently

    a(n)^4 ≤ 16 · 2^(3n).

If a complete state has at most `2^A · a(M)` codes, with star-pair density
`A ≤ M`, then its eighth power is at most `2^(7(A+M)+8)`.  Up to the harmless
factor 2, this is the strict-base estimate

    state count ≲ 2^(7N/8) ≈ 1.834^N.
-/

namespace Echo

/-- Fourth powers distribute over multiplication. -/
theorem fourth_mul (x y : Nat) :
    fourth (x*y) = fourth x * fourth y := by
  simp [fourth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Fourth power of a power of two. -/
theorem fourth_two_pow (A : Nat) :
    fourth (2^A) = 2^(4*A) := by
  simp [fourth, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm]

/-- Sparse Fibonacci growth in fourth-power form. -/
theorem sparseCount_fourth_bound : ∀ n : Nat,
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
                          simp [fourth_mul, fourth]
                        _ ≤ 4096 * (16 * 2^(3*(d+1))) :=
                          Nat.mul_le_mul_left 4096 hprev
                        _ = 16 * 2^(3*((d+1)+4)) := by
                          rw [show 3*((d+1)+4) = 3*(d+1)+12 by omega,
                            Nat.pow_add]
                          norm_num
                          simp [Nat.mul_assoc, Nat.mul_comm,
                            Nat.mul_left_comm]
                        _ = 16 * 2^(3*(Nat.succ (Nat.succ
                          (Nat.succ (Nat.succ (Nat.succ d)))))) := by
                          omega

/-- Eighth power, used to avoid rational exponents. -/
def eighth (x : Nat) : Nat := fourth x * fourth x

/-- Main sparse-code arithmetic. -/
theorem sparse_encoded_eighth_bound
    (C A M S : Nat)
    (hC : C = A + M)
    (hAM : A ≤ M)
    (hcount : S ≤ 2^A * sparseCount M) :
    eighth S ≤ 2^(7*C + 8) := by
  have hs4 := fourth_mono hcount
  have hsc := sparseCount_fourth_bound M
  have h4 : fourth S ≤ 2^(4*A + 3*M + 4) := by
    calc
      fourth S ≤ fourth (2^A * sparseCount M) := hs4
      _ = 2^(4*A) * fourth (sparseCount M) := by
        rw [fourth_mul, fourth_two_pow]
      _ ≤ 2^(4*A) * (16 * 2^(3*M)) :=
        Nat.mul_le_mul_left _ hsc
      _ = 2^(4*A + 3*M + 4) := by
        rw [show 4*A + 3*M + 4 = 4*A + (4 + 3*M) by omega,
          Nat.pow_add]
        norm_num
        simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
  unfold eighth
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

/-- Direct code-list form. -/
theorem sparse_code_list_eighth_bound
    (C A E F : Nat)
    (codes : List (List Bool))
    (hnd : codes.Nodup)
    (hlen : ∀ bits ∈ codes, bits.length = E)
    (htrue : ∀ bits ∈ codes, trueCount bits = F)
    (hC : C = A + (E+F))
    (hhalf : A ≤ E+F) :
    eighth (2^A * codes.length) ≤ 2^(7*C + 8) := by
  have hc := fixed_full_code_count E F codes hnd hlen htrue
  apply sparse_encoded_eighth_bound C A (E+F)
    (2^A * codes.length) hC hhalf
  exact Nat.mul_le_mul_left (2^A) hc

end Echo
