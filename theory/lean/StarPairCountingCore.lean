import EchoMachine

/-!
# Half-density for an involutive pairing

A duplicate-free list containing at most one member from each `star` pair has
at most half as many entries as any finite duplicate-free universe containing
both endpoints of all represented pairs.
-/

namespace Echo

variable (m : Machine)

/-- At most one cell from each mouth-partner pair. -/
def StarSeparatedCore (active : List Nat) : Prop :=
  active.Nodup ∧ ∀ c ∈ active, m.star c ∉ active

/-- Expand every active cell to its two-element star pair. -/
def starPairExpansion : List Nat → List Nat
  | [] => []
  | c :: rest => c :: m.star c :: starPairExpansion rest

/-- Membership in the expansion. -/
theorem mem_starPairExpansion_cases {active : List Nat} {x : Nat} :
    x ∈ starPairExpansion m active →
      x ∈ active ∨ m.star x ∈ active := by
  induction active with
  | nil => simp [starPairExpansion]
  | cons c rest ih =>
      intro hx
      simp only [starPairExpansion, List.mem_cons] at hx
      rcases hx with h | h | h
      · exact Or.inl (Or.inl h)
      · right
        have hs : m.star x = c := by
          rw [h, m.star_invol]
        exact Or.inl hs
      · rcases ih h with hm | hm
        · exact Or.inl (Or.inr hm)
        · exact Or.inr (Or.inr hm)

/-- Expansion doubles the length. -/
theorem starPairExpansion_length : ∀ active : List Nat,
    (starPairExpansion m active).length = 2 * active.length := by
  intro active
  induction active with
  | nil => rfl
  | cons c rest ih =>
      simp [starPairExpansion, ih]
      omega

/-- Star separation makes the expansion duplicate-free. -/
theorem starPairExpansion_nodup {active : List Nat}
    (hsep : StarSeparatedCore m active) :
    (starPairExpansion m active).Nodup := by
  induction active with
  | nil => simp [starPairExpansion]
  | cons a rest ih =>
      have hnd := List.nodup_cons.mp hsep.1
      have hrest : StarSeparatedCore m rest := by
        constructor
        · exact hnd.2
        · intro c hc hsc
          exact hsep.2 c (List.mem_cons_of_mem _ hc)
            (List.mem_cons_of_mem _ hsc)
      have hi := ih hrest
      rw [starPairExpansion, List.nodup_cons, List.nodup_cons]
      refine ⟨?_, ?_, hi⟩
      · intro ha
        simp only [List.mem_cons] at ha
        rcases ha with heq | ha
        · exact hsep.2 a List.mem_cons_self (by
            rw [← heq]
            exact List.mem_cons_self)
        · rcases mem_starPairExpansion_cases m ha with har | hsar
          · exact hnd.1 har
          · exact hsep.2 a List.mem_cons_self
              (List.mem_cons_of_mem _ hsar)
      · intro hsa
        rcases mem_starPairExpansion_cases m hsa with hsar | haar
        · exact hsep.2 a List.mem_cons_self
            (List.mem_cons_of_mem _ hsar)
        · have har : a ∈ rest := by
            simpa [m.star_invol] using haar
          exact hnd.1 har

private theorem starPair_nodup_subset_length
    {xs ys : List Nat}
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

/-- **Star-separated lists have half density.** -/
theorem starSeparatedCore_count
    (active cells : List Nat)
    (hsep : StarSeparatedCore m active)
    (hcells : cells.Nodup)
    (hcover : ∀ c ∈ active,
      c ∈ cells ∧ m.star c ∈ cells) :
    2 * active.length ≤ cells.length := by
  have hnd := starPairExpansion_nodup m hsep
  have hsub : ∀ x ∈ starPairExpansion m active, x ∈ cells := by
    intro x hx
    rcases mem_starPairExpansion_cases m hx with hx | hsx
    · exact (hcover x hx).1
    · have h := (hcover (m.star x) hsx).2
      simpa [m.star_invol] using h
  have hle := starPair_nodup_subset_length hnd hsub
  rw [starPairExpansion_length] at hle
  exact hle

end Echo
