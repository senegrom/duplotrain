import ComponentCapacity

/-!
# Finite coding theorem for the strict-exponential strategy

A state in one fixed-support epoch will be encoded by

1. a projected pseudoforest code `p < P`; and
2. `A` Boolean lobe bits.

This file proves that a duplicate-free list of such codes has at most
`P * 2^A` elements, and combines that count with the three-quarter exponent
estimates.
-/

namespace Echo

/-- All Boolean vectors of a given length. -/
def boolVectors : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 =>
      (boolVectors n).map (fun v => false :: v) ++
      (boolVectors n).map (fun v => true :: v)

theorem boolVectors_length : ∀ A,
    (boolVectors A).length = 2^A := by
  intro A
  induction A with
  | zero => rfl
  | succ n ih =>
      simp [boolVectors, ih, Nat.pow_succ]
      omega

theorem mem_boolVectors : ∀ {A : Nat} {v : List Bool},
    v.length = A → v ∈ boolVectors A := by
  intro A
  induction A with
  | zero =>
      intro v hv
      have hnil : v = [] := by
        cases v with
        | nil => rfl
        | cons b bs => simp only [List.length_cons] at hv; omega
      rw [hnil]
      exact List.mem_cons_self
  | succ n ih =>
      intro v hv
      cases v with
      | nil => simp only [List.length_nil] at hv; omega
      | cons b bs =>
          have hbs : bs.length = n := by
            simp only [List.length_cons] at hv
            omega
          cases b with
          | false =>
              unfold boolVectors
              exact List.mem_append_left _
                (List.mem_map.mpr ⟨bs, ih hbs, rfl⟩)
          | true =>
              unfold boolVectors
              exact List.mem_append_right _
                (List.mem_map.mpr ⟨bs, ih hbs, rfl⟩)

/-- Universe of a bounded natural code and an `A`-bit vector. -/
def profileCodeUniverse (P A : Nat) : List (Nat × List Bool) :=
  (List.range P).flatMap fun p =>
    (boolVectors A).map fun bits => (p, bits)

private theorem codeRect_length (ps : List Nat) (A : Nat) :
    (ps.flatMap (fun p =>
      (boolVectors A).map fun bits => (p, bits))).length
      = ps.length * (boolVectors A).length := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

/-- The code universe has exactly `P * 2^A` elements. -/
theorem profileCodeUniverse_length (P A : Nat) :
    (profileCodeUniverse P A).length = P * 2^A := by
  unfold profileCodeUniverse
  rw [codeRect_length, List.length_range, boolVectors_length]

private theorem nodup_subset_length_code
    {l S : List (Nat × List Bool)}
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ S) :
    l.length ≤ S.length := by
  induction l generalizing S with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ S.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      have hlen : (S.erase x).length = S.length - 1 :=
        List.length_erase_of_mem hx
      rw [hlen] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- Pairwise-distinct bounded codes use at most `P * 2^A` values. -/
theorem profile_code_count
    (P A : Nat) (codes : List (Nat × List Bool))
    (hnd : codes.Nodup)
    (hP : ∀ z ∈ codes, z.1 < P)
    (hA : ∀ z ∈ codes, z.2.length = A) :
    codes.length ≤ P * 2^A := by
  have hsub : ∀ z ∈ codes, z ∈ profileCodeUniverse P A := by
    intro z hz
    unfold profileCodeUniverse
    apply List.mem_flatMap.mpr
    refine ⟨z.1, List.mem_range.mpr (hP z hz), ?_⟩
    exact List.mem_map.mpr ⟨z.2, mem_boolVectors (hA z hz), by
      cases z
      rfl⟩
  have hle := nodup_subset_length_code hnd hsub
  rw [profileCodeUniverse_length] at hle
  exact hle

/-- `fourth` is monotone. -/
theorem fourth_mono {x y : Nat} (h : x ≤ y) :
    fourth x ≤ fourth y := by
  unfold fourth
  have hs : x*x ≤ y*y := Nat.mul_le_mul h h
  exact Nat.mul_le_mul hs hs

/-- **Encoded three-quarter bound.**  Once states inject into a projected code
of capacity `P` plus `A` active lobe bits, the profile inequalities give the
strict-exponential estimate in integer fourth-power form. -/
theorem encoded_three_quarter_bound
    (C L M A P : Nat)
    (codes : List (Nat × List Bool))
    (hnd : codes.Nodup)
    (hcodeP : ∀ z ∈ codes, z.1 < P)
    (hcodeA : ∀ z ∈ codes, z.2.length = A)
    (hC : C = L + M)
    (hAL : A ≤ L) (hAM : A ≤ M)
    (hcap : P*P ≤ 2^M) :
    fourth codes.length ≤ 2^(3*C) := by
  have hcount := profile_code_count P A codes hnd hcodeP hcodeA
  have hfourth : fourth codes.length ≤ fourth (2^A * P) := by
    apply fourth_mono
    simpa [Nat.mul_comm] using hcount
  exact Nat.le_trans hfourth
    (three_quarter_fourth_bound C L M A P hC hAL hAM hcap)

/-- Encoded three-quarter bound using only star-pair independence of the
active lobe coordinates.  The hypothesis `2*A ≤ C` is supplied by
`star_independent_length` once the active-cell list is shown to contain at
most one endpoint from each mouth-partner pair. -/
theorem encoded_three_quarter_star_pair_bound
    (C L M A P : Nat)
    (codes : List (Nat × List Bool))
    (hnd : codes.Nodup)
    (hcodeP : ∀ z ∈ codes, z.1 < P)
    (hcodeA : ∀ z ∈ codes, z.2.length = A)
    (hC : C = L + M)
    (hAL : A ≤ L) (hhalf : 2*A ≤ C)
    (hcap : P*P ≤ 2^M) :
    fourth codes.length ≤ 2^(3*C) := by
  have hcount := profile_code_count P A codes hnd hcodeP hcodeA
  have hfourth : fourth codes.length ≤ fourth (2^A * P) := by
    apply fourth_mono
    simpa [Nat.mul_comm] using hcount
  exact Nat.le_trans hfourth
    (three_quarter_star_pair_bound C L M A P hC hAL hhalf hcap)

end Echo
