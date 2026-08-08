import OutwardReplayCore

/-!
# Ordinary support reachability implies rooted replay

No shortest-path or numerical-rank construction is needed.  While following an
arbitrary occupied support walk from a full edge:

* a step to the current parent simply pops the existing `OutwardPath`;
* every other step extends it.

Thus every cell in the ordinary connected support component of a full edge has
an `OutwardPath`, and `OutwardReplayCore` turns that path into the exact
`RootedAt` / `RootedCells` replay certificate.  This closes the static tree
component part of the projected-code argument.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- One oriented occupied support edge from cell `c` to cell `d`. -/
def SupportStep (k c d : Nat) : Prop :=
  ∃ s,
    Occupied m e r0 k s ∧
    m.cellOf s = c ∧
    m.cellOf (m.bar s) = d

/-- Ordinary reachability from either endpoint of a chosen full edge. -/
inductive ReachFromFull (k f : Nat) : Nat → Prop
  | left : ReachFromFull k f (m.cellOf f)
  | right : ReachFromFull k f (m.cellOf (m.bar f))
  | step {c d : Nat} :
      ReachFromFull k f c →
      SupportStep m e r0 k c d →
      ReachFromFull k f d

/-- An outward path always contains, by popping one constructor, a path to its
current parent cell.  At a root endpoint the parent is the other root. -/
theorem outwardPath_parent
    {k f c p : Nat}
    (h : OutwardPath m e r0 k f c p) :
    ∃ q, OutwardPath m e r0 k f (m.cellOf (m.bar p)) q := by
  cases h with
  | left =>
      exact ⟨m.bar f, OutwardPath.right⟩
  | right =>
      refine ⟨f, ?_⟩
      simpa [m.bar_invol] using
        (OutwardPath.left :
          OutwardPath m e r0 k f (m.cellOf f) f)
  | @step c q s hprev hocc hcell hparent =>
      refine ⟨q, ?_⟩
      simpa [m.bar_invol, hcell] using hprev

/-- Every ordinarily reachable support cell admits an outward path. -/
theorem outwardPath_of_reach
    {k f c : Nat}
    (h : ReachFromFull m e r0 k f c) :
    ∃ p, OutwardPath m e r0 k f c p := by
  induction h with
  | left =>
      exact ⟨f, OutwardPath.left⟩
  | right =>
      exact ⟨m.bar f, OutwardPath.right⟩
  | @step c d hreach hstep ih =>
      rcases ih with ⟨p, hp⟩
      rcases hstep with ⟨s, hocc, hsc, hsd⟩
      by_cases hback : m.cellOf (m.bar s) = m.cellOf (m.bar p)
      · rcases outwardPath_parent m e r0 hp with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        have hd : d = m.cellOf (m.bar p) := hsd.symm.trans hback
        simpa [hd] using hq
      · refine ⟨m.bar s, ?_⟩
        have hout := OutwardPath.step hp hocc hsc hback
        simpa [hsd] using hout

/-- A list of cells lies in the occupied support component of `f`. -/
def ReachableCells (k f : Nat) (cells : List Nat) : Prop :=
  ∀ c ∈ cells, ReachFromFull m e r0 k f c

/-- **Connected full-edge component replay certificate.** -/
theorem rootedCells_of_reach
    {k f : Nat} {cells : List Nat}
    (hfull : Full m e r0 k f)
    (hreach : ReachableCells m e r0 k f cells) :
    RootedCells m e r0 k f cells := by
  intro c hc
  rcases outwardPath_of_reach m e r0 (hreach c hc) with ⟨p, hp⟩
  exact (outwardPath_confirmed_rooted m e r0 hfull hp).2

/-- Reachability varying over an epoch gives the complete tree-block
certificate used by the injective projected code. -/
def treeBlockOfReach
    (times : Nat → Prop)
    (cells edges : List Nat)
    (fullAt : Nat → Nat)
    (hmem : ∀ k, times k → fullAt k ∈ edges)
    (hfull : ∀ k, times k → Full m e r0 k (fullAt k))
    (hreach : ∀ k, times k →
      ReachableCells m e r0 k (fullAt k) cells) :
    TreeBlockCert m e r0 times where
  cells := cells
  edges := edges
  fullAt := fullAt
  full_mem := hmem
  full_full := hfull
  rooted := fun k hk =>
    rootedCells_of_reach m e r0 (hfull k hk) (hreach k hk)

end Echo
