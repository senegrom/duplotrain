import EpochStrictBound

/-!
# Rooted replay from non-backtracking support paths: core certificate

This is the dependency-minimal form of `OutwardReplay.lean`: it proves that
an occupied non-backtracking path grown from a full edge is forced to point
back toward that edge, and turns such paths into `RootedCells` and
`TreeBlockCert` witnesses.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

inductive OutwardPath (k f : Nat) : Nat → Nat → Prop
  | left : OutwardPath k f (m.cellOf f) f
  | right : OutwardPath k f (m.cellOf (m.bar f)) (m.bar f)
  | step {c p s : Nat} :
      OutwardPath k f c p →
      Occupied m e r0 k s →
      m.cellOf s = c →
      m.cellOf (m.bar s) ≠ m.cellOf (m.bar p) →
      OutwardPath k f (m.cellOf (m.bar s)) (m.bar s)

theorem outwardPath_slot_cell {k f c p : Nat}
    (h : OutwardPath m e r0 k f c p) :
    m.cellOf p = c := by
  induction h with
  | left => rfl
  | right => rfl
  | step => rfl

/-- Every path endpoint selects the path edge leading back to the full root,
and hence carries a `RootedAt` certificate. -/
theorem outwardPath_confirmed_rooted
    {k f c p : Nat}
    (hfull : Full m e r0 k f)
    (h : OutwardPath m e r0 k f c p) :
    Confirmed m e r0 k p ∧ RootedAt m e r0 k f c := by
  induction h with
  | left =>
      exact ⟨hfull.1, RootedAt.left⟩
  | right =>
      exact ⟨hfull.2, RootedAt.right⟩
  | @step c p s hpath hocc hcell hparent ih =>
      have hpcell : m.cellOf p = c :=
        outwardPath_slot_cell m e r0 hpath
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

/-- Every listed cell admits a non-backtracking support path from the full
edge. -/
def OutwardPathCells (k f : Nat) (cells : List Nat) : Prop :=
  ∀ c ∈ cells, ∃ p, OutwardPath m e r0 k f c p

theorem rootedCells_of_outwardPath
    {k f : Nat} {cells : List Nat}
    (hfull : Full m e r0 k f)
    (hout : OutwardPathCells m e r0 k f cells) :
    RootedCells m e r0 k f cells := by
  intro c hc
  rcases hout c hc with ⟨p, hp⟩
  exact (outwardPath_confirmed_rooted m e r0 hfull hp).2

/-- A family of path certificates over an epoch is a tree-block replay
certificate. -/
def treeBlockOfOutwardPath
    (times : Nat → Prop)
    (cells edges : List Nat)
    (fullAt : Nat → Nat)
    (hmem : ∀ k, times k → fullAt k ∈ edges)
    (hfull : ∀ k, times k → Full m e r0 k (fullAt k))
    (hout : ∀ k, times k →
      OutwardPathCells m e r0 k (fullAt k) cells) :
    TreeBlockCert m e r0 times where
  cells := cells
  edges := edges
  fullAt := fullAt
  full_mem := hmem
  full_full := hfull
  rooted := fun k hk =>
    rootedCells_of_outwardPath m e r0 (hfull k hk) (hout k hk)

end Echo
