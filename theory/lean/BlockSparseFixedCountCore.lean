import BlockSparseBoundCore

/-!
# Fixed-cardinality indicators in the corrected block universe
-/

namespace Echo

/-- Number of true entries. -/
def blockCoreTrueCount : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + blockCoreTrueCount rest

/-- Insert one false separator after every true entry. -/
def blockCoreSeparate : List Bool → List Bool
  | [] => []
  | false :: rest => false :: blockCoreSeparate rest
  | true :: rest => true :: false :: blockCoreSeparate rest

/-- Decoder on the image. -/
def blockCoreUnseparate : List Bool → List Bool
  | [] => []
  | false :: rest => false :: blockCoreUnseparate rest
  | true :: [] => [true]
  | true :: _ :: rest => true :: blockCoreUnseparate rest

theorem blockCoreUnseparate_separate : ∀ bits : List Bool,
    blockCoreUnseparate (blockCoreSeparate bits) = bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [blockCoreSeparate, blockCoreUnseparate, ih]

theorem blockCoreSeparate_injective {a b : List Bool}
    (h : blockCoreSeparate a = blockCoreSeparate b) : a = b := by
  have hd := congrArg blockCoreUnseparate h
  simpa [blockCoreUnseparate_separate] using hd

/-- Prepending false preserves no-adjacency. -/
theorem blockNoAdjacent_false_cons {bits : List Bool}
    (h : BlockNoAdjacent bits) :
    BlockNoAdjacent (false :: bits) := by
  cases bits with
  | nil => trivial
  | cons b rest =>
      exact ⟨by simp, h⟩

/-- Separated strings have no adjacent true entries. -/
theorem blockCoreSeparate_noAdjacent : ∀ bits : List Bool,
    BlockNoAdjacent (blockCoreSeparate bits) := by
  intro bits
  induction bits with
  | nil => trivial
  | cons b rest ih =>
      cases b with
      | false =>
          exact blockNoAdjacent_false_cons ih
      | true =>
          exact ⟨by simp, blockNoAdjacent_false_cons ih⟩

/-- Length after separation. -/
theorem blockCoreSeparate_length : ∀ bits : List Bool,
    (blockCoreSeparate bits).length =
      bits.length + blockCoreTrueCount bits := by
  intro bits
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      cases b <;>
        simp [blockCoreSeparate, blockCoreTrueCount, ih] <;> omega

/-- Injectivity preserves duplicate-freeness. -/
theorem blockCoreSeparate_map_nodup {codes : List (List Bool)}
    (hnd : codes.Nodup) :
    (codes.map blockCoreSeparate).Nodup := by
  induction codes with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, heq⟩ := List.mem_map.mp hm
        have hxy : x = y := blockCoreSeparate_injective heq.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih hnd.2

end Echo
