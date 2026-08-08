import StrictEpochCertificate

/-!
# A component-free fallback: sparse full-edge codes

Let a fixed support have `E` represented edges and let a projected state have
`F` full edges.  Insert one `false` bit after every `true` bit in the full-edge
indicator.  The result

* has length `E + F`,
* has no adjacent `true` bits, and
* determines the original indicator exactly.

When endpoint accounting gives `E + F = M`, projected states therefore inject
into sparse Boolean vectors of length `M`.  Their Fibonacci growth is already
a strict-base improvement over `2^M`, without explicitly enumerating support
components.
-/

namespace Echo

/-- Insert a separator after each selected/full edge. -/
def separateTrue : List Bool → List Bool
  | [] => []
  | false :: rest => false :: separateTrue rest
  | true :: rest => true :: false :: separateTrue rest

/-- Left inverse for `separateTrue` on its image. -/
def unseparateTrue : List Bool → List Bool
  | [] => []
  | false :: rest => false :: unseparateTrue rest
  | true :: [] => [true]
  | true :: _ :: rest => true :: unseparateTrue rest

/-- Separation can be decoded exactly. -/
theorem unseparate_separate : ∀ bits : List Bool,
    unseparateTrue (separateTrue bits) = bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;> simp [separateTrue, unseparateTrue, ih]

/-- Hence separation is injective. -/
theorem separateTrue_injective {a b : List Bool}
    (h : separateTrue a = separateTrue b) : a = b := by
  have hd := congrArg unseparateTrue h
  simpa [unseparate_separate] using hd

/-- Separation length is original length plus the number of selected bits. -/
theorem separateTrue_length : ∀ bits : List Bool,
    (separateTrue bits).length = bits.length + trueCount bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;> simp [separateTrue, trueCount, ih] <;> omega

/-- All sparse Boolean vectors of length `n`; multiplicity-free in fact, though
only the length and coverage properties are needed below. -/
def sparseVectors : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false], [true]]
  | n+2 =>
      (sparseVectors (n+1)).map (fun v => false :: v) ++
      (sparseVectors n).map (fun v => true :: false :: v)

/-- Every separated indicator lies in the sparse universe of its length. -/
theorem separateTrue_mem_sparse : ∀ bits : List Bool,
    separateTrue bits ∈ sparseVectors (separateTrue bits).length := by
  intro bits
  induction bits with
  | nil =>
      exact List.mem_cons_self
  | cons b rest ih =>
      cases b with
      | false =>
          let tail := separateTrue rest
          cases tail with
          | nil =>
              simp [separateTrue, sparseVectors]
          | cons x xs =>
              have hi : x :: xs ∈ sparseVectors ((x :: xs).length) := by
                simpa [tail] using ih
              simp only [separateTrue, List.length_cons]
              change false :: x :: xs ∈ sparseVectors (xs.length + 2)
              unfold sparseVectors
              apply List.mem_append_left
              exact List.mem_map.mpr ⟨x :: xs, by simpa using hi, rfl⟩
      | true =>
          let tail := separateTrue rest
          have hi : tail ∈ sparseVectors tail.length := by
            simpa [tail] using ih
          simp only [separateTrue, List.length_cons]
          change true :: false :: tail ∈ sparseVectors (tail.length + 2)
          unfold sparseVectors
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨tail, hi, rfl⟩

/-- Sparse-vector count. -/
def sparseCount (n : Nat) : Nat := (sparseVectors n).length

theorem sparseCount_zero : sparseCount 0 = 1 := rfl

theorem sparseCount_one : sparseCount 1 = 2 := rfl

theorem sparseCount_add_two (n : Nat) :
    sparseCount (n+2) = sparseCount (n+1) + sparseCount n := by
  simp [sparseCount, sparseVectors]

/-- The sparse counts are monotone. -/
theorem sparseCount_le_succ : ∀ n : Nat,
    sparseCount n ≤ sparseCount (n+1) := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
      rw [show n+1+1 = n+2 by omega, sparseCount_add_two]
      omega

/-- Four additional coordinates multiply the sparse universe by at most 8. -/
theorem sparseCount_add_four (n : Nat) :
    sparseCount (n+4) ≤ 8 * sparseCount n := by
  have h1 := sparseCount_le_succ n
  have h2 := sparseCount_le_succ (n+1)
  have h3 := sparseCount_le_succ (n+2)
  rw [show n+4 = (n+2)+2 by omega, sparseCount_add_two,
      show n+3 = (n+1)+2 by omega, sparseCount_add_two,
      sparseCount_add_two]
  omega

/-- A duplicate-free list of separated indicators has at most
`sparseCount M` members when every separated indicator has length `M`. -/
theorem separated_code_count
    (M : Nat) (codes : List (List Bool))
    (hnd : (codes.map separateTrue).Nodup)
    (hlen : ∀ bits ∈ codes,
      (separateTrue bits).length = M) :
    codes.length ≤ sparseCount M := by
  have hsub : ∀ z ∈ codes.map separateTrue,
      z ∈ sparseVectors M := by
    intro z hz
    obtain ⟨bits, hbits, rfl⟩ := List.mem_map.mp hz
    rw [← hlen bits hbits]
    exact separateTrue_mem_sparse bits
  have hle := by
    induction (codes.map separateTrue) generalizing (sparseVectors M) with
    | nil => exact Nat.zero_le _
    | cons x rest ih =>
        rw [List.nodup_cons] at hnd
        have hx := hsub x List.mem_cons_self
        have hsub' : ∀ y ∈ rest,
            y ∈ (sparseVectors M).erase x := by
          intro y hy
          have hyS := hsub y (List.mem_cons_of_mem _ hy)
          have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
          exact (List.mem_erase_of_ne hyx).mpr hyS
        have hr := ih hnd.2 hsub'
        rw [List.length_erase_of_mem hx] at hr
        have hpos : 0 < (sparseVectors M).length := by
          cases sparseVectors M with
          | nil => cases hx
          | cons _ _ => simp
        simp only [List.length_cons]
        omega
  simpa [sparseCount] using hle

/-- If the original indicators are duplicate-free, their separated images are
also duplicate-free. -/
theorem separate_map_nodup {codes : List (List Bool)}
    (hnd : codes.Nodup) :
    (codes.map separateTrue).Nodup := by
  induction codes with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
        have : x = y := separateTrue_injective hxy.symm
        exact hnd.1 (this ▸ hy)
      · exact ih hnd.2

/-- Convenient fixed-cardinality form: indicators of `E` edges with `F` true
bits inject into sparse vectors of length `E+F`. -/
theorem fixed_full_code_count
    (E F : Nat) (codes : List (List Bool))
    (hnd : codes.Nodup)
    (hlen : ∀ bits ∈ codes, bits.length = E)
    (htrue : ∀ bits ∈ codes, trueCount bits = F) :
    codes.length ≤ sparseCount (E+F) := by
  apply separated_code_count (E+F) codes (separate_map_nodup hnd)
  intro bits hb
  rw [separateTrue_length, hlen bits hb, htrue bits hb]

end Echo
