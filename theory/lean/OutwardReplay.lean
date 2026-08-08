import EpochStrictBound

/-!
# Rooted replay from non-backtracking support paths

A full support edge selects both of its endpoints.  Starting from either
endpoint, take an occupied edge whose far endpoint is not the parent just used.
The near endpoint cannot select this new edge, because it already selects its
parent edge.  Occupancy therefore forces the far endpoint to select the new
edge back toward the root.

Inductively, every non-backtracking support path emanating from a full edge is
oriented toward that edge.  This directly manufactures `RootedAt` and
`RootedCells` certificates, replacing the extra numerical-rank hypothesis of
`RootRank.lean` by an ordinary path/connectivity certificate.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A support path grown outwards from a full edge.  The second index is the
slot selected at the current cell and points one step back toward the root.
The extension condition rules out immediate backtracking, including a
parallel edge to the same parent cell. -/
inductive Outward (k f : Nat) : Nat → Nat → Prop
  | left : Outward k f (m.cellOf f) f
  | right : Outward k f (m.cellOf (m.bar f)) (m.bar f)
  | step {c p s : Nat} :
      Outward k f c p →
      Occupied m e r0 k s →
      m.cellOf s = c →
      m.cellOf (m.bar s) ≠ m.cellOf (m.bar p) →
      Outward k f (m.cellOf (m.bar s)) (m.bar s)

/-- The carried slot belongs to the current path cell. -/
theorem outward_slot_cell {k f c p : Nat}
    (h : Outward m e r0 k f c p) :
    m.cellOf p = c := by
  induction h with
  | left => rfl
  | right => rfl
  | step => rfl

/-- **Path forcing.**  Every outward-path cell selects its parent slot and is
rooted at the initial full edge. -/
theorem outward_confirmed_rooted
    {k f c p : Nat}
    (hfull : Full m e r0 k f)
    (h : Outward m e r0 k f c p) :
    Confirmed m e r0 k p ∧ RootedAt m e r0 k f c := by
  induction h with
  | left =>
      exact ⟨hfull.1, RootedAt.left⟩
  | right =>
      exact ⟨hfull.2, RootedAt.right⟩
  | @step c p s hpath hocc hcell hparent ih =>
      have hpcell : m.cellOf p = c :=
        outward_slot_cell m e r0 hpath
      have hnot : ¬ Confirmed m e r0 k s := by
        intro hs
        have heq : p = s :=
          confirmed_same_cell_eq m e r0 ih.1 hs
            (hpcell.trans hcell.symm)
        apply hparent
        rw [heq]
      have hbar : Confirmed m e r0 k (m.bar s) := by
        rcases hocc with hs | hs
        · exact absurd hs hnot
        · exact hs
      have hnfullSlot : ¬ Full m e r0 k (m.bar s) := by
        intro hf
        unfold Full at hf
        apply hnot
        simpa [m.bar_invol] using hf.2
      have hreg : reg m e r0 k (m.cellOf (m.bar s)) = m.bar s := by
        unfold Confirmed at hbar
        exact hbar
      have hnfullReg :
          ¬ Full m e r0 k
            (reg m e r0 k (m.cellOf (m.bar s))) := by
        rw [hreg]
        exact hnfullSlot
      refine ⟨?_, ?_⟩
      · exact hbar
      · apply RootedAt.step (m.cellOf (m.bar s)) hnfullReg
        rw [hreg, m.bar_invol, hcell]
        exact ih.2

/-- Every listed cell admits an outward support path from the full edge. -/
def OutwardCells (k f : Nat) (cells : List Nat) : Prop :=
  ∀ c ∈ cells, ∃ p, Outward m e r0 k f c p

/-- Outward connectivity gives the replay certificate expected by
`TreeReplay`. -/
theorem rootedCells_of_outward
    {k f : Nat} {cells : List Nat}
    (hfull : Full m e r0 k f)
    (hout : OutwardCells m e r0 k f cells) :
    RootedCells m e r0 k f cells := by
  intro c hc
  rcases hout c hc with ⟨p, hp⟩
  exact (outward_confirmed_rooted m e r0 hfull hp).2

/-- An epoch-varying family of outward paths constructs a complete tree block
certificate. -/
def treeBlockOfOutward
    (times : Nat → Prop)
    (cells edges : List Nat)
    (fullAt : Nat → Nat)
    (hmem : ∀ k, times k → fullAt k ∈ edges)
    (hfull : ∀ k, times k → Full m e r0 k (fullAt k))
    (hout : ∀ k, times k →
      OutwardCells m e r0 k (fullAt k) cells) :
    TreeBlockCert m e r0 times where
  cells := cells
  edges := edges
  fullAt := fullAt
  full_mem := hmem
  full_full := hfull
  rooted := fun k hk =>
    rootedCells_of_outward m e r0 (hfull k hk) (hout k hk)

/-- Reusing the same outward paths at two times, equality of the full marker
forces equality of every register in the block. -/
theorem outward_block_replay
    {k₁ k₂ f : Nat} {cells : List Nat}
    (hf₁ : Full m e r0 k₁ f)
    (hf₂ : Full m e r0 k₂ f)
    (h₁ : OutwardCells m e r0 k₁ f cells)
    (h₂ : OutwardCells m e r0 k₂ f cells) :
    ∀ c ∈ cells,
      reg m e r0 k₁ c = reg m e r0 k₂ c := by
  exact rootedCells_snapshot_eq m e r0
    (rootedCells_of_outward m e r0 hf₁ h₁)
    (rootedCells_of_outward m e r0 hf₂ h₂)

end Echo
