import ThreeQuarterArithmetic

/-!
# Standalone sparse-code combinatorics

This file depends only on the already established arithmetic layer.  It proves:

1. an `E`-bit vector with `F` selected bits injects into a sparse vector of
   length `E+F` by inserting `false` after every `true`;
2. sparse vectors satisfy the Fibonacci recurrence and
   `sparseCount(n+4) ≤ 8*sparseCount(n)`;
3. `sparseCount(n)^4 ≤ 16*2^(3n)`; and
4. if `A ≤ M`, any code family of size at most
   `2^A*sparseCount(M)` obeys the strict-base integer estimate
   `size^8 ≤ 2^(7(A+M)+8)`.
-/

namespace Echo

/-- Number of true entries. -/
def sparseBitCount : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + sparseBitCount rest

/-- Insert a separator after every true entry. -/
def sparseSeparate : List Bool → List Bool
  | [] => []
  | false :: rest => false :: sparseSeparate rest
  | true :: rest => true :: false :: sparseSeparate rest

/-- Decoder on the image of `sparseSeparate`. -/
def sparseUnseparate : List Bool → List Bool
  | [] => []
  | false :: rest => false :: sparseUnseparate rest
  | true :: [] => [true]
  | true :: _ :: rest => true :: sparseUnseparate rest

theorem sparseUnseparate_separate : ∀ bits : List Bool,
    sparseUnseparate (sparseSeparate bits) = bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;> simp [sparseSeparate, sparseUnseparate, ih]

theorem sparseSeparate_injective {a b : List Bool}
    (h : sparseSeparate a = sparseSeparate b) : a = b := by
  have hd := congrArg sparseUnseparate h
  simpa [sparseUnseparate_separate] using hd

theorem sparseSeparate_length : ∀ bits : List Bool,
    (sparseSeparate bits).length =
      bits.length + sparseBitCount bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [sparseSeparate, sparseBitCount, ih] <;> omega

/-- Sparse Boolean vectors by their canonical first block. -/
def standaloneSparseVectors : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false], [true]]
  | n+2 =>
      (standaloneSparseVectors (n+1)).map
        (fun v => false :: v) ++
      (standaloneSparseVectors n).map
        (fun v => true :: false :: v)

/-- Every separated vector belongs to its canonical sparse universe. -/
theorem sparseSeparate_mem : ∀ bits : List Bool,
    sparseSeparate bits ∈
      standaloneSparseVectors (sparseSeparate bits).length := by
  intro bits
  induction bits with
  | nil => exact List.mem_cons_self
  | cons b rest ih =>
      cases b with
      | false =>
          let tail := sparseSeparate rest
          cases tail with
          | nil =>
              simp [sparseSeparate, standaloneSparseVectors]
          | cons x xs =>
              have hi : x :: xs ∈
                  standaloneSparseVectors (x :: xs).length := by
                simpa [tail] using ih
              simp only [sparseSeparate, List.length_cons]
              change false :: x :: xs ∈
                standaloneSparseVectors (xs.length + 2)
              unfold standaloneSparseVectors
              apply List.mem_append_left
              exact List.mem_map.mpr
                ⟨x :: xs, by simpa using hi, rfl⟩
      | true =>
          let tail := sparseSeparate rest
          have hi : tail ∈ standaloneSparseVectors tail.length := by
            simpa [tail] using ih
          simp only [sparseSeparate, List.length_cons]
          change true :: false :: tail ∈
            standaloneSparseVectors (tail.length + 2)
          unfold standaloneSparseVectors
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨tail, hi, rfl⟩

/-- Sparse-vector count. -/
def standaloneSparseCount (n : Nat) : Nat :=
  (standaloneSparseVectors n).length

theorem standaloneSparseCount_zero :
    standaloneSparseCount 0 = 1 := rfl

theorem standaloneSparseCount_one :
    standaloneSparseCount 1 = 2 := rfl

theorem standaloneSparseCount_add_two (n : Nat) :
    standaloneSparseCount (n+2) =
      standaloneSparseCount (n+1) + standaloneSparseCount n := by
  simp [standaloneSparseCount, standaloneSparseVectors]

theorem standaloneSparseCount_le_succ : ∀ n : Nat,
    standaloneSparseCount n ≤ standaloneSparseCount (n+1) := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
      rw [show n+1+1 = n+2 by omega,
        standaloneSparseCount_add_two]
      omega

theorem standaloneSparseCount_add_four (n : Nat) :
    standaloneSparseCount (n+4) ≤
      8 * standaloneSparseCount n := by
  have h1 := standaloneSparseCount_le_succ n
  have h2 := standaloneSparseCount_le_succ (n+1)
  have h3 := standaloneSparseCount_le_succ (n+2)
  rw [show n+4 = (n+2)+2 by omega,
      standaloneSparseCount_add_two,
      show n+3 = (n+1)+2 by omega,
      standaloneSparseCount_add_two,
      standaloneSparseCount_add_two]
  omega

private theorem standalone_nodup_subset_length
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

/-- Injectivity lifts duplicate-freeness through separation. -/
theorem sparseSeparate_map_nodup {codes : List (List Bool)}
    (hnd : codes.Nodup) :
    (codes.map sparseSeparate).Nodup := by
  induction codes with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, heq⟩ := List.mem_map.mp hm
        have hxy : x = y := sparseSeparate_injective heq.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih hnd.2

/-- Fixed-cardinality indicator families have Fibonacci-size capacity. -/
theorem standalone_fixed_code_count
    (E F : Nat) (codes : List (List Bool))
    (hnd : codes.Nodup)
    (hlen : ∀ bits ∈ codes, bits.length = E)
    (htrue : ∀ bits ∈ codes, sparseBitCount bits = F) :
    codes.length ≤ standaloneSparseCount (E+F) := by
  have hsep := sparseSeparate_map_nodup hnd
  have hsub : ∀ z ∈ codes.map sparseSeparate,
      z ∈ standaloneSparseVectors (E+F) := by
    intro z hz
    obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hz
    have hlenSep : (sparseSeparate bits).length = E+F := by
      rw [sparseSeparate_length, hlen bits hb, htrue bits hb]
    rw [← hlenSep]
    exact sparseSeparate_mem bits
  have hle := standalone_nodup_subset_length hsep hsub
  simpa [standaloneSparseCount] using hle

/-- Fourth powers distribute over multiplication. -/
theorem standalone_fourth_mul (x y : Nat) :
    fourth (x*y) = fourth x * fourth y := by
  simp [fourth, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem standalone_fourth_two_pow (A : Nat) :
    fourth (2^A) = 2^(4*A) := by
  simp [fourth, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm]

/-- Explicit Fibonacci growth bound. -/
theorem standaloneSparseCount_fourth_bound : ∀ n : Nat,
    fourth (standaloneSparseCount n) ≤ 16 * 2^(3*n) := by
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
                      have hstep := standaloneSparseCount_add_four (d+1)
                      have hmono := fourth_mono hstep
                      have hprev := ih (d+1) (by omega)
                      calc
                        fourth (standaloneSparseCount
                          (Nat.succ (Nat.succ (Nat.succ
                            (Nat.succ (Nat.succ d))))))
                            = fourth (standaloneSparseCount ((d+1)+4)) := by
                              omega
                        _ ≤ fourth (8 * standaloneSparseCount (d+1)) := hmono
                        _ = 4096 * fourth
                            (standaloneSparseCount (d+1)) := by
                          simp [standalone_fourth_mul, fourth,
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

/-- Eighth power used for the rational exponent `7/8`. -/
def standaloneEighth (x : Nat) : Nat := fourth x * fourth x

/-- **Strict-base sparse-code arithmetic.** -/
theorem standalone_sparse_eighth_bound
    (C A M S : Nat)
    (hC : C = A + M)
    (hAM : A ≤ M)
    (hcount : S ≤ 2^A * standaloneSparseCount M) :
    standaloneEighth S ≤ 2^(7*C + 8) := by
  have hs4 := fourth_mono hcount
  have hsc := standaloneSparseCount_fourth_bound M
  have h4 : fourth S ≤ 2^(4*A + 3*M + 4) := by
    calc
      fourth S ≤ fourth (2^A * standaloneSparseCount M) := hs4
      _ = 2^(4*A) * fourth (standaloneSparseCount M) := by
        rw [standalone_fourth_mul, standalone_fourth_two_pow]
      _ ≤ 2^(4*A) * (16 * 2^(3*M)) :=
        Nat.mul_le_mul_left _ hsc
      _ = 2^(4*A + 3*M + 4) := by
        rw [show 4*A + 3*M + 4 = 4*A + (3*M+4) by omega,
          Nat.pow_add, Nat.pow_add]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  unfold standaloneEighth
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
