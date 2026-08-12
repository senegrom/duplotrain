import HiddenAbsorb

/-!
# Core freezing lemma for no-full non-lobe cells

In a support-preserving step, a productive different-edge write implies that
the overwritten edge was full.  A productive same-edge write moves to the
opposite endpoint and is therefore a lobe.  Hence a no-full non-lobe cell is
unchanged.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- No jump edge has both endpoints in this cell. -/
def CoreNoLobe (c : Nat) : Prop :=
  ∀ s, m.cellOf s = c → m.cellOf (m.bar s) ≠ c

/-- No edge selected from this cell is full at time `k`. -/
def CoreNoFull (k c : Nat) : Prop :=
  ∀ s, m.cellOf s = c → ¬ Full m e r0 k s

/-- **One support-preserving step freezes a no-full non-lobe cell.** -/
theorem reg_step_eq_of_coreNoFull_coreNoLobe
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k c : Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hnfull : CoreNoFull m e r0 k c)
    (hnlobe : CoreNoLobe m c) :
    reg m e r0 (k+1) c = reg m e r0 k c := by
  by_cases hdest : m.cellOf (e (k+1)) = c
  · subst c
    let new := e (k+1)
    let old := reg m e r0 k (m.cellOf new)
    have holdCell : m.cellOf old = m.cellOf new := by
      exact reg_cell m e r0 hr0 k (m.cellOf new)
    have hwrite :
        reg m e r0 (k+1) (m.cellOf new) = new := by
      exact reg_write m e r0 rfl
    by_cases heq : old = new
    · rw [hwrite, ← heq]
    · have hp : ProductiveStep m e r0 k := by
        unfold ProductiveStep
        intro h
        exact heq h.symm
      have holdConf : Confirmed m e r0 k old :=
        old_register_confirmed m e r0 hr0 k (m.cellOf new)
      have holdAfter : Occupied m e r0 (k+1) old :=
        (hsupport old).mp (Or.inl holdConf)
      by_cases hsame : SameEdge m old new
      · rcases hsame with hsame | hsame
        · exact absurd hsame.symm heq
        · have hbarCell :
              m.cellOf (m.bar old) = m.cellOf new := by
            rw [← hsame]
          exact absurd hbarCell (hnlobe old holdCell)
      · have hfull : Full m e r0 k old := by
          exact old_edge_full_of_preserved m e r0
            hrun hr0 k hp holdAfter hsame
        exact absurd hfull (hnfull old holdCell)
  · exact reg_skip m e r0 (k := k) (c := c) hdest

end Echo
