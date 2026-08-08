import HiddenAbsorb

/-!
# Standalone freezing lemma for no-full non-lobe cells

During a support-preserving step, a productive write to a different jump edge
requires the overwritten edge to have been full.  A productive write on the
same jump edge moves to its opposite endpoint, hence is a lobe.  Therefore a
cell with neither an incident full edge nor a lobe cannot change its register.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The cell contains no jump edge with both endpoints in that cell. -/
def StandaloneNoLobe (c : Nat) : Prop :=
  ∀ s, m.cellOf s = c → m.cellOf (m.bar s) ≠ c

/-- No represented edge selected from the cell is full. -/
def StandaloneNoFull (k c : Nat) : Prop :=
  ∀ s, m.cellOf s = c → ¬ Full m e r0 k s

/-- **One support-preserving step cannot change a no-full non-lobe cell.** -/
theorem reg_step_eq_of_noFull_noLobe_standalone
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k c : Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hnfull : StandaloneNoFull m e r0 k c)
    (hnlobe : StandaloneNoLobe m c) :
    reg m e r0 (k+1) c = reg m e r0 k c := by
  by_cases hdest : m.cellOf (e (k+1)) = c
  · let new := e (k+1)
    let old := reg m e r0 k c
    have holdCell : m.cellOf old = c := by
      exact reg_cell m e r0 hr0 k c
    have hwrite : reg m e r0 (k+1) c = new := by
      have hw := reg_write m e r0
        (show m.cellOf (e (k+1)) = c from hdest)
      simpa [new] using hw
    by_cases heq : old = new
    · rw [hwrite, ← heq]
    · have hp : ProductiveStep m e r0 k := by
        unfold ProductiveStep
        simpa [old, new, hdest] using heq
      have holdConf : Confirmed m e r0 k old :=
        old_register_confirmed m e r0 hr0 k c
      have holdAfter : Occupied m e r0 (k+1) old :=
        (hsupport old).mp (Or.inl holdConf)
      by_cases hsame : SameEdge m old new
      · rcases hsame with hsame | hsame
        · exact absurd hsame.symm heq
        · have hbarCell : m.cellOf (m.bar old) = c := by
            rw [← hsame]
            exact hdest
          exact absurd hbarCell (hnlobe old holdCell)
      · have hfullRaw := old_edge_full_of_preserved m e r0
          hrun hr0 k hp
          (by simpa [old, new, hdest] using holdAfter)
          (by simpa [old, new, hdest] using hsame)
        have hfull : Full m e r0 k old := by
          simpa [old, new, hdest] using hfullRaw
        exact absurd hfull (hnfull old holdCell)
  · exact reg_skip m e r0 (k := k) (c := c) hdest

/-- The whole listed block is unchanged in one step. -/
theorem snap_step_eq_of_noFull_noLobe_standalone
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) (cells : List Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hnfull : ∀ c ∈ cells, StandaloneNoFull m e r0 k c)
    (hnlobe : ∀ c ∈ cells, StandaloneNoLobe m c) :
    snap m e r0 cells (k+1) = snap m e r0 cells k := by
  unfold snap
  apply List.map_congr_left
  intro c hc
  exact reg_step_eq_of_noFull_noLobe_standalone m e r0
    hrun hr0 k c hsupport (hnfull c hc) (hnlobe c hc)

end Echo
