import TreeEpochCode

/-!
# Manufacturing tree certificates from a decreasing rank

A rooted tree orientation admits a simple numerical certificate: the two
endpoints of the full edge are roots, while every other selected edge moves to
a strictly smaller rank.  Strong induction on that rank constructs the
`RootedAt` proof required by `TreeReplay`.

This replaces arbitrary path objects by a compact, checkable rank function.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- One cell is either a root endpoint or takes a non-full edge to a
lower-ranked cell in the component. -/
def RankedToward (k f : Nat) (cells : List Nat)
    (rank : Nat → Nat) (c : Nat) : Prop :=
  c = m.cellOf f ∨
  c = m.cellOf (m.bar f) ∨
  (¬ Full m e r0 k (reg m e r0 k c) ∧
   m.cellOf (m.bar (reg m e r0 k c)) ∈ cells ∧
   rank (m.cellOf (m.bar (reg m e r0 k c))) < rank c)

/-- A decreasing rank yields finite root certificates for every listed cell. -/
theorem rootedCells_of_rank
    (k f : Nat) (cells : List Nat) (rank : Nat → Nat)
    (htoward : ∀ c ∈ cells, RankedToward m e r0 k f cells rank c) :
    RootedCells m e r0 k f cells := by
  intro c hc
  have hmain : ∀ N n c, n ≤ N → rank c = n → c ∈ cells →
      RootedAt m e r0 k f c := by
    intro N
    induction N with
    | zero =>
        intro n c hn hrank hc
        rcases htoward c hc with hleft | hright | ⟨hnfull, hmem, hlt⟩
        · rw [hleft]
          exact RootedAt.left
        · rw [hright]
          exact RootedAt.right
        · rw [hrank] at hlt
          omega
    | succ N ihN =>
        intro n c hn hrank hc
        rcases htoward c hc with hleft | hright | ⟨hnfull, hmem, hlt⟩
        · rw [hleft]
          exact RootedAt.left
        · rw [hright]
          exact RootedAt.right
        · apply RootedAt.step c hnfull
          exact ihN (rank (m.cellOf (m.bar (reg m e r0 k c))))
            (m.cellOf (m.bar (reg m e r0 k c)))
            (by rw [hrank] at hlt; omega) rfl hmem
  exact hmain (rank c) (rank c) c (Nat.le_refl _) rfl hc

/-- A rank certificate varying with time constructs a `TreeBlockCert`. -/
def treeBlockOfRank
    (times : Nat → Prop)
    (cells edges : List Nat)
    (fullAt : Nat → Nat)
    (rankAt : Nat → Nat → Nat)
    (hmem : ∀ k, times k → fullAt k ∈ edges)
    (hfull : ∀ k, times k → Full m e r0 k (fullAt k))
    (htoward : ∀ k, times k → ∀ c ∈ cells,
      RankedToward m e r0 k (fullAt k) cells (rankAt k) c) :
    TreeBlockCert m e r0 times where
  cells := cells
  edges := edges
  fullAt := fullAt
  full_mem := hmem
  full_full := hfull
  rooted := fun k hk =>
    rootedCells_of_rank m e r0 k (fullAt k) cells (rankAt k)
      (htoward k hk)

/-- The rank need not be globally bounded: on a finite component, strict
decrease alone is enough. -/
theorem rankedToward_nonroot_decreases
    {k f c : Nat} {cells : List Nat} {rank : Nat → Nat}
    (h : RankedToward m e r0 k f cells rank c)
    (hl : c ≠ m.cellOf f)
    (hr : c ≠ m.cellOf (m.bar f)) :
    rank (m.cellOf (m.bar (reg m e r0 k c))) < rank c := by
  rcases h with h | h | h
  · exact absurd h hl
  · exact absurd h hr
  · exact h.2.2

end Echo
