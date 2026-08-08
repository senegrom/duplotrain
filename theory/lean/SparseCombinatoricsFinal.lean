import ThreeQuarterArithmetic

/-!
# Final standalone sparse-code theorem

This version avoids rewrite-order dependence in the Fibonacci arithmetic.  The
three recurrence equations for `n+2`, `n+3`, and `n+4` are passed explicitly to
`omega`, yielding `a(n+4) ≤ 8a(n)`.
-/

namespace Echo

/-- Number of selected bits. -/
def finalSparseTrueCount : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + finalSparseTrueCount rest

/-- Insert a zero after every selected bit. -/
def finalSparseSeparate : List Bool → List Bool
  | [] => []
  | false :: rest => false :: finalSparseSeparate rest
  | true :: rest => true :: false :: finalSparseSeparate rest

/-- Decoder on separated strings. -/
def finalSparseUnseparate : List Bool → List Bool
  | [] => []
  | false :: rest => false :: finalSparseUnseparate rest
  | true :: [] => [true]
  | true :: _ :: rest => true :: finalSparseUnseparate rest

theorem finalSparseUnseparate_separate : ∀ bits : List Bool,
    finalSparseUnseparate (finalSparseSeparate bits) = bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [finalSparseSeparate, finalSparseUnseparate, ih]

theorem finalSparseSeparate_injective {a b : List Bool}
    (h : finalSparseSeparate a = finalSparseSeparate b) : a = b := by
  have hd := congrArg finalSparseUnseparate h
  simpa [finalSparseUnseparate_separate] using hd

theorem finalSparseSeparate_length : ∀ bits : List Bool,
    (finalSparseSeparate bits).length =
      bits.length + finalSparseTrueCount bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [finalSparseSeparate, finalSparseTrueCount, ih] <;> omega

/-- Canonical strings with no adjacent selected bits. -/
def finalSparseVectors : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false], [true]]
  | n+2 =>
      (finalSparseVectors (n+1)).map (fun v => false :: v) ++
      (finalSparseVectors n).map (fun v => true :: false :: v)

/-- Every separated vector belongs to its canonical universe. -/
theorem finalSparseSeparate_mem : ∀ bits : List Bool,
    finalSparseSeparate bits ∈
      finalSparseVectors (finalSparseSeparate bits).length := by
  intro bits
  induction bits with
  | nil => exact List.mem_cons_self
  | cons b rest ih =>
      cases b with
      | false =>
          cases htail : finalSparseSeparate rest with
          | nil =>
              simp [finalSparseSeparate, finalSparseVectors, htail]
          | cons x xs =>
              have hi : x :: xs ∈ finalSparseVectors (x :: xs).length := by
                simpa [htail] using ih
              simp only [finalSparseSeparate, List.length_cons]
              change false :: x :: xs ∈ finalSparseVectors (xs.length + 2)
              unfold finalSparseVectors
              apply List.mem_append_left
              exact List.mem_map.mpr
                ⟨x :: xs, by simpa using hi, rfl⟩
      | true =>
          have hi := ih
          simp only [finalSparseSeparate, List.length_cons]
          change true :: false :: finalSparseSeparate rest ∈
            finalSparseVectors ((finalSparseSeparate rest).length + 2)
          unfold finalSparseVectors
          apply List.mem_append_right
          exact List.mem_map.mpr
            ⟨finalSparseSeparate rest, hi, rfl⟩

/-- Sparse-string count. -/
def finalSparseCount (n : Nat) : Nat := (finalSparseVectors n).length

theorem finalSparseCount_add_two (n : Nat) :
    finalSparseCount (n+2) =
      finalSparseCount (n+1) + finalSparseCount n := by
  simp [finalSparseCount, finalSparseVectors]

theorem finalSparseCount_le_succ : ∀ n : Nat,
    finalSparseCount n ≤ finalSparseCount (n+1) := by
  intro n
  cases n with
  | zero => decide
  | succ d =>
      have h := finalSparseCount_add_two d
      omega

theorem finalSparseCount_succ_le_two (n : Nat) :
    finalSparseCount (n+1) ≤ 2 * finalSparseCount n := by
  cases n with
  | zero => decide
  | succ d =>
      have hrec := finalSparseCount_add_two d
      have hmono := finalSparseCount_le_succ d
      omega

/-- Four new coordinates multiply capacity by at most eight. -/
theorem finalSparseCount_add_four (n : Nat) :
    finalSparseCount (n+4) ≤ 8 * finalSparseCount n := by
  have h2 := finalSparseCount_add_two n
  have h3 := finalSparseCount_add_two (n+1)
  have h4 := finalSparseCount_add_two (n+2)
  have hs := finalSparseCount_succ_le_two n
  omega

private theorem final_nodup_subset_length
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

/-- Separation preserves duplicate-freeness. -/
theorem finalSparseSeparate_map_nodup {codes : List (List Bool)}
    (hnd : codes.Nodup) :
    (codes.map finalSparseSeparate).Nodup := by
  induction codes with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, heq⟩ := List.mem_map.mp hm
        have hxy : x = y := finalSparseSeparate_injective heq.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih hnd.2

/-- Fixed-cardinality full-edge indicators have Fibonacci-size capacity. -/
theorem final_fixed_code_count
    (E F : Nat) (codes : List (List Bool))
    (hnd : codes.Nodup)
    (hlen : ∀ bits ∈ codes, bits.length = E)
    (htrue : ∀ bits ∈ codes, finalSparseTrueCount bits = F) :
    codes.length ≤ finalSparseCount (E+F) := by
  have hsep := finalSparseSeparate_map_nodup hnd
  have hsub : ∀ z ∈ codes.map finalSparseSeparate,
      z ∈ finalSparseVectors (E+F) := by
    intro z hz
    obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hz
    have hlenSep : (finalSparseSeparate bits).length = E+F := by
      rw [finalSparseSeparate_length, hlen bits hb, htrue bits hb]
    rw [← hlenSep]
    exact finalSparseSeparate_mem bits
  have hle := final_nodup_subset_length hsep hsub
  simpa [finalSparseCount] using hle

/-- Fourth-power monotonicity. -/
theorem finalFourth_mono {x y : Nat} (h : x ≤ y) :
    fourth x ≤ fourth y := by
  unfold fourth
  have hs : x*x ≤ y*y := Nat.mul_le_mul h h
  exact Nat.mul_le_mul hs hs

/-- Fourth powers distribute over products. -/
theorem finalFourth_mul (x y : Nat) :
    fourth (x*y) = fourth x * fourth y := by
  simp [fourth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Fourth power of `2^A`. -/
theorem finalFourth_two_pow (A : Nat) :
    fourth (2^A) = 2^(4*A) := by
  unfold fourth
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega

/-- Fibonacci growth in fourth-power form. -/
theorem finalSparseCount_fourth_bound : ∀ n : Nat,
    fourth (finalSparseCount n) ≤ 16 * 2^(3*n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => decide
      | succ n₁ =>
          cases n₁ with
          | zero => decide
          | succ n₂ =>
              cases n₂ with
              | zero => decide
              | succ n₃ =>
                  cases n₃ with
                  | zero => decide
                  | succ d =>
                      have hstep := finalSparseCount_add_four d
                      have hmono := finalFourth_mono hstep
                      have hprev := ih d (by omega)
                      calc
                        fourth (finalSparseCount
                          (Nat.succ (Nat.succ (Nat.succ
                            (Nat.succ d)))))
                            = fourth (finalSparseCount (d+4)) := by omega
                        _ ≤ fourth (8 * finalSparseCount d) := hmono
                        _ = 4096 * fourth (finalSparseCount d) := by
                          simp [finalFourth_mul, fourth,
                            Nat.mul_assoc, Nat.mul_comm,
                            Nat.mul_left_comm]
                        _ ≤ 4096 * (16 * 2^(3*d)) :=
                          Nat.mul_le_mul_left 4096 hprev
                        _ = 16 * 2^(3*(d+4)) := by
                          rw [show 3*(d+4) = 3*d+12 by omega,
                            Nat.pow_add]
                          simp [Nat.mul_assoc, Nat.mul_comm,
                            Nat.mul_left_comm]

/-- Eighth power for the final strict-base statement. -/
def finalEighth (x : Nat) : Nat := fourth x * fourth x

/-- **Strict sparse-code arithmetic.** -/
theorem finalSparse_eighth_bound
    (C A M S : Nat)
    (hC : C = A + M)
    (hAM : A ≤ M)
    (hcount : S ≤ 2^A * finalSparseCount M) :
    finalEighth S ≤ 2^(7*C + 8) := by
  have hs4 := finalFourth_mono hcount
  have hsc := finalSparseCount_fourth_bound M
  have h4 : fourth S ≤ 2^(4*A + 3*M + 4) := by
    calc
      fourth S ≤ fourth (2^A * finalSparseCount M) := hs4
      _ = 2^(4*A) * fourth (finalSparseCount M) := by
        rw [finalFourth_mul, finalFourth_two_pow]
      _ ≤ 2^(4*A) * (16 * 2^(3*M)) :=
        Nat.mul_le_mul_left _ hsc
      _ = 2^(4*A + 3*M + 4) := by
        rw [show 4*A + 3*M + 4 = 4*A + (3*M+4) by omega,
          Nat.pow_add, Nat.pow_add]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  unfold finalEighth
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

end Echo
