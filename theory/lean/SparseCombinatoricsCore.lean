import ThreeQuarterArithmetic

/-!
# Standalone sparse-code combinatorics, corrected

An `E`-bit indicator with `F` selected entries injects into a Boolean string of
length `E+F` with no adjacent `true` values by inserting `false` after each
`true`.  The sparse-string counts satisfy the Fibonacci recurrence and the
four-step estimate

    a(n+4) ≤ 8 a(n).

Consequently

    a(n)^4 ≤ 16 * 2^(3n).

If `A ≤ M`, a code family of size at most `2^A * a(M)` therefore obeys

    size^8 ≤ 2^(7(A+M)+8).

This is the integer form of a strict `2^(7N/8)`-type bound.
-/

namespace Echo

/-- Number of selected bits. -/
def sparseTrueCount : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + sparseTrueCount rest

/-- Insert one separator after each selected bit. -/
def sparseSeparateCore : List Bool → List Bool
  | [] => []
  | false :: rest => false :: sparseSeparateCore rest
  | true :: rest => true :: false :: sparseSeparateCore rest

/-- Decoder on the image of `sparseSeparateCore`. -/
def sparseUnseparateCore : List Bool → List Bool
  | [] => []
  | false :: rest => false :: sparseUnseparateCore rest
  | true :: [] => [true]
  | true :: _ :: rest => true :: sparseUnseparateCore rest

theorem sparseUnseparateCore_separate : ∀ bits : List Bool,
    sparseUnseparateCore (sparseSeparateCore bits) = bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [sparseSeparateCore, sparseUnseparateCore, ih]

theorem sparseSeparateCore_injective {a b : List Bool}
    (h : sparseSeparateCore a = sparseSeparateCore b) : a = b := by
  have hd := congrArg sparseUnseparateCore h
  simpa [sparseUnseparateCore_separate] using hd

theorem sparseSeparateCore_length : ∀ bits : List Bool,
    (sparseSeparateCore bits).length =
      bits.length + sparseTrueCount bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [sparseSeparateCore, sparseTrueCount, ih] <;> omega

/-- Canonical sparse Boolean strings of a given length. -/
def sparseVectorsCore : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false], [true]]
  | n+2 =>
      (sparseVectorsCore (n+1)).map (fun v => false :: v) ++
      (sparseVectorsCore n).map (fun v => true :: false :: v)

/-- Every separated vector belongs to the canonical universe of its length. -/
theorem sparseSeparateCore_mem : ∀ bits : List Bool,
    sparseSeparateCore bits ∈
      sparseVectorsCore (sparseSeparateCore bits).length := by
  intro bits
  induction bits with
  | nil => exact List.mem_cons_self
  | cons b rest ih =>
      cases b with
      | false =>
          let tail := sparseSeparateCore rest
          cases htail : tail with
          | nil =>
              simp [sparseSeparateCore, sparseVectorsCore, tail, htail]
          | cons x xs =>
              have hi : x :: xs ∈ sparseVectorsCore (x :: xs).length := by
                simpa [tail, htail] using ih
              simp only [sparseSeparateCore, List.length_cons]
              change false :: x :: xs ∈ sparseVectorsCore (xs.length + 2)
              unfold sparseVectorsCore
              apply List.mem_append_left
              exact List.mem_map.mpr
                ⟨x :: xs, by simpa using hi, rfl⟩
      | true =>
          let tail := sparseSeparateCore rest
          have hi : tail ∈ sparseVectorsCore tail.length := by
            simpa [tail] using ih
          simp only [sparseSeparateCore, List.length_cons]
          change true :: false :: tail ∈
            sparseVectorsCore (tail.length + 2)
          unfold sparseVectorsCore
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨tail, hi, rfl⟩

/-- Sparse-string count. -/
def sparseCountCore (n : Nat) : Nat := (sparseVectorsCore n).length

theorem sparseCountCore_zero : sparseCountCore 0 = 1 := rfl

theorem sparseCountCore_one : sparseCountCore 1 = 2 := rfl

theorem sparseCountCore_add_two (n : Nat) :
    sparseCountCore (n+2) =
      sparseCountCore (n+1) + sparseCountCore n := by
  simp [sparseCountCore, sparseVectorsCore]

/-- Sparse counts are monotone. -/
theorem sparseCountCore_le_succ : ∀ n : Nat,
    sparseCountCore n ≤ sparseCountCore (n+1) := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
      rw [show n+1+1 = n+2 by omega, sparseCountCore_add_two]
      omega

/-- One-step ratio bound. -/
theorem sparseCountCore_succ_le_two (n : Nat) :
    sparseCountCore (n+1) ≤ 2 * sparseCountCore n := by
  cases n with
  | zero => decide
  | succ d =>
      rw [show d+1+1 = d+2 by omega, sparseCountCore_add_two]
      have h := sparseCountCore_le_succ d
      omega

/-- Four positions multiply capacity by at most eight. -/
theorem sparseCountCore_add_four (n : Nat) :
    sparseCountCore (n+4) ≤ 8 * sparseCountCore n := by
  have hs := sparseCountCore_succ_le_two n
  rw [show n+4 = (n+2)+2 by omega, sparseCountCore_add_two,
      show n+3 = (n+1)+2 by omega, sparseCountCore_add_two,
      sparseCountCore_add_two]
  omega

private theorem sparseCore_nodup_subset_length
    {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α}
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

/-- Injectivity preserves duplicate-freeness under separation. -/
theorem sparseSeparateCore_map_nodup {codes : List (List Bool)}
    (hnd : codes.Nodup) :
    (codes.map sparseSeparateCore).Nodup := by
  induction codes with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, heq⟩ := List.mem_map.mp hm
        have hxy : x = y := sparseSeparateCore_injective heq.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih hnd.2

/-- Fixed-cardinality indicator families have sparse/Fibonacci capacity. -/
theorem sparseCore_fixed_code_count
    (E F : Nat) (codes : List (List Bool))
    (hnd : codes.Nodup)
    (hlen : ∀ bits ∈ codes, bits.length = E)
    (htrue : ∀ bits ∈ codes, sparseTrueCount bits = F) :
    codes.length ≤ sparseCountCore (E+F) := by
  have hsep := sparseSeparateCore_map_nodup hnd
  have hsub : ∀ z ∈ codes.map sparseSeparateCore,
      z ∈ sparseVectorsCore (E+F) := by
    intro z hz
    obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hz
    have hlenSep : (sparseSeparateCore bits).length = E+F := by
      rw [sparseSeparateCore_length, hlen bits hb, htrue bits hb]
    rw [← hlenSep]
    exact sparseSeparateCore_mem bits
  have hle := sparseCore_nodup_subset_length hsep hsub
  simpa [sparseCountCore] using hle

/-- Monotonicity of the fourth-power helper. -/
theorem sparseCore_fourth_mono {x y : Nat} (h : x ≤ y) :
    fourth x ≤ fourth y := by
  unfold fourth
  have hs : x*x ≤ y*y := Nat.mul_le_mul h h
  exact Nat.mul_le_mul hs hs

/-- Fourth powers distribute over multiplication. -/
theorem sparseCore_fourth_mul (x y : Nat) :
    fourth (x*y) = fourth x * fourth y := by
  simp [fourth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- Fourth power of a power of two. -/
theorem sparseCore_fourth_two_pow (A : Nat) :
    fourth (2^A) = 2^(4*A) := by
  unfold fourth
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega

/-- Explicit sparse/Fibonacci growth estimate. -/
theorem sparseCountCore_fourth_bound : ∀ n : Nat,
    fourth (sparseCountCore n) ≤ 16 * 2^(3*n) := by
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
                      have hstep := sparseCountCore_add_four d
                      have hmono := sparseCore_fourth_mono hstep
                      have hprev := ih d (by omega)
                      calc
                        fourth (sparseCountCore
                          (Nat.succ (Nat.succ (Nat.succ
                            (Nat.succ d)))))
                            = fourth (sparseCountCore (d+4)) := by omega
                        _ ≤ fourth (8 * sparseCountCore d) := hmono
                        _ = 4096 * fourth (sparseCountCore d) := by
                          simp [sparseCore_fourth_mul, fourth,
                            Nat.mul_assoc, Nat.mul_comm,
                            Nat.mul_left_comm]
                        _ ≤ 4096 * (16 * 2^(3*d)) :=
                          Nat.mul_le_mul_left 4096 hprev
                        _ = 16 * 2^(3*(d+4)) := by
                          rw [show 3*(d+4) = 3*d+12 by omega,
                            Nat.pow_add]
                          simp [Nat.mul_assoc, Nat.mul_comm,
                            Nat.mul_left_comm]

/-- Eighth power, avoiding rational exponents. -/
def sparseCoreEighth (x : Nat) : Nat := fourth x * fourth x

/-- **Strict-base sparse-code arithmetic.** -/
theorem sparseCore_eighth_bound
    (C A M S : Nat)
    (hC : C = A + M)
    (hAM : A ≤ M)
    (hcount : S ≤ 2^A * sparseCountCore M) :
    sparseCoreEighth S ≤ 2^(7*C + 8) := by
  have hs4 := sparseCore_fourth_mono hcount
  have hsc := sparseCountCore_fourth_bound M
  have h4 : fourth S ≤ 2^(4*A + 3*M + 4) := by
    calc
      fourth S ≤ fourth (2^A * sparseCountCore M) := hs4
      _ = 2^(4*A) * fourth (sparseCountCore M) := by
        rw [sparseCore_fourth_mul, sparseCore_fourth_two_pow]
      _ ≤ 2^(4*A) * (16 * 2^(3*M)) :=
        Nat.mul_le_mul_left _ hsc
      _ = 2^(4*A + 3*M + 4) := by
        rw [show 4*A + 3*M + 4 = 4*A + (3*M+4) by omega,
          Nat.pow_add, Nat.pow_add]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  unfold sparseCoreEighth
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
