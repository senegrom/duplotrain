import BlockSparseBound

/-!
# Fixed-cardinality indicators via the four-bit sparse universe

Insert `false` after every `true`.  This operation is injective, creates a
no-adjacent string, and changes length from `E` to `E+F`, where `F` is the
number of true entries.  Therefore duplicate-free `E`-bit indicators with
exactly `F` true entries have capacity at most
`blockSparseUniverse (E+F).length`.
-/

namespace Echo

/-- Number of selected entries. -/
def blockTrueCount : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + blockTrueCount rest

/-- Insert one separator after every selected entry. -/
def blockSeparate : List Bool → List Bool
  | [] => []
  | false :: rest => false :: blockSeparate rest
  | true :: rest => true :: false :: blockSeparate rest

/-- Decoder on the separator image. -/
def blockUnseparate : List Bool → List Bool
  | [] => []
  | false :: rest => false :: blockUnseparate rest
  | true :: [] => [true]
  | true :: _ :: rest => true :: blockUnseparate rest

theorem blockUnseparate_separate : ∀ bits : List Bool,
    blockUnseparate (blockSeparate bits) = bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;> simp [blockSeparate, blockUnseparate, ih]

/-- Separation is injective. -/
theorem blockSeparate_injective {a b : List Bool}
    (h : blockSeparate a = blockSeparate b) : a = b := by
  have hd := congrArg blockUnseparate h
  simpa [blockUnseparate_separate] using hd

/-- Prepending `false` preserves the no-adjacent property. -/
theorem noAdjacent_false_cons {bits : List Bool}
    (h : NoAdjacent bits) : NoAdjacent (false :: bits) := by
  cases bits with
  | nil => trivial
  | cons b rest =>
      simp [NoAdjacent]
      exact h

/-- Every separated string has no adjacent true entries. -/
theorem blockSeparate_noAdjacent : ∀ bits : List Bool,
    NoAdjacent (blockSeparate bits) := by
  intro bits
  induction bits with
  | nil => trivial
  | cons b rest ih =>
      cases b with
      | false =>
          exact noAdjacent_false_cons ih
      | true =>
          simp only [blockSeparate, NoAdjacent]
          exact ⟨by simp, noAdjacent_false_cons ih⟩

/-- Separation length is original length plus the true count. -/
theorem blockSeparate_length : ∀ bits : List Bool,
    (blockSeparate bits).length = bits.length + blockTrueCount bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [blockSeparate, blockTrueCount, ih] <;> omega

/-- Injectivity preserves duplicate-freeness under separation. -/
theorem blockSeparate_map_nodup {codes : List (List Bool)}
    (hnd : codes.Nodup) :
    (codes.map blockSeparate).Nodup := by
  induction codes with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, heq⟩ := List.mem_map.mp hm
        have hxy : x = y := blockSeparate_injective heq.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih hnd.2

/-- **Fixed-cardinality full-edge indicators have block-sparse capacity.** -/
theorem block_fixed_code_count
    (E F : Nat) (codes : List (List Bool))
    (hnd : codes.Nodup)
    (hlen : ∀ bits ∈ codes, bits.length = E)
    (htrue : ∀ bits ∈ codes, blockTrueCount bits = F) :
    codes.length ≤ (blockSparseUniverse (E+F)).length := by
  have hsep := blockSeparate_map_nodup hnd
  have hlenSep : ∀ z ∈ codes.map blockSeparate,
      z.length = E+F := by
    intro z hz
    obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hz
    rw [blockSeparate_length, hlen bits hb, htrue bits hb]
  have hsparse : ∀ z ∈ codes.map blockSeparate, NoAdjacent z := by
    intro z hz
    obtain ⟨bits, _, rfl⟩ := List.mem_map.mp hz
    exact blockSeparate_noAdjacent bits
  have hcount := blockSparse_code_count (E+F)
    (codes.map blockSeparate) hsep hlenSep hsparse
  simpa only [List.length_map] using hcount

end Echo
