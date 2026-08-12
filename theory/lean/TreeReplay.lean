import SupportSize

/-!
# Tree-component replay from a rooted certificate

A fixed-support tree component has one full edge.  Every other register points
along the unique route toward that edge.  Instead of importing a graph library,
we express exactly the finite certificate needed for replay:

`RootedAt k f c` says that, in state `k`, cell `c` reaches one endpoint of the
full edge `f` by repeatedly following non-full selected edges.

The main theorem proves by induction on this certificate that another state
with the same occupied support and the same full edge has the identical
register at `c`.  Thus a certified tree component is completely determined by
its full edge.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A cell has a finite selected-edge route to the full edge `f`. -/
inductive RootedAt (k f : Nat) : Nat → Prop
  | left : RootedAt k f (m.cellOf f)
  | right : RootedAt k f (m.cellOf (m.bar f))
  | step (c : Nat)
      (hnfull : ¬ Full m e r0 k (reg m e r0 k c))
      (next : RootedAt k f
        (m.cellOf (m.bar (reg m e r0 k c)))) :
      RootedAt k f c

/-- The slot selected by a well-formed register is confirmed. -/
theorem register_confirmed
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (k c : Nat) :
    Confirmed m e r0 k (reg m e r0 k c) := by
  unfold Confirmed
  have hc := reg_cell m e r0 hr0 k c
  rw [hc]

/-- **Tree replay at one cell.**  Same support and the same full root edge
force equality at every cell carrying a finite root certificate. -/
theorem rootedAt_replay
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j f c : Nat}
    (hsupport : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfullI : Full m e r0 i f)
    (hfullJ : Full m e r0 j f)
    (hroot : RootedAt m e r0 i f c) :
    reg m e r0 j c = reg m e r0 i c := by
  induction hroot with
  | left =>
      exact hfullJ.1.trans hfullI.1.symm
  | right =>
      exact hfullJ.2.trans hfullI.2.symm
  | step c hnfull next ih =>
      let s := reg m e r0 i c
      have hsI : Confirmed m e r0 i s := by
        dsimp [s]
        exact register_confirmed m e r0 hr0 i c
      have hoccI : Occupied m e r0 i s := Or.inl hsI
      have hoccJ : Occupied m e r0 j s :=
        (hsupport s).mp hoccI
      have hnotBar : ¬ Confirmed m e r0 j (m.bar s) := by
        intro hbJ
        have hcbar : m.cellOf (m.bar s) =
            m.cellOf (m.bar (reg m e r0 i c)) := by rfl
        have hregNext : reg m e r0 j (m.cellOf (m.bar s)) =
            reg m e r0 i (m.cellOf (m.bar s)) := by
          simpa [s] using ih
        have hbI : Confirmed m e r0 i (m.bar s) := by
          unfold Confirmed at hbJ ⊢
          rw [← hregNext]
          exact hbJ
        have hfullS : Full m e r0 i s := ⟨hsI, hbI⟩
        exact hnfull hfullS
      have hsJ : Confirmed m e r0 j s :=
        hoccJ.resolve_right hnotBar
      unfold Confirmed at hsJ
      have hc : m.cellOf s = c := by
        dsimp [s]
        exact reg_cell m e r0 hr0 i c
      rw [hc] at hsJ
      exact hsJ

/-- A list of cells is rooted at the same full edge. -/
def RootedCells (k f : Nat) (cells : List Nat) : Prop :=
  ∀ c ∈ cells, RootedAt m e r0 k f c

/-- Replay of a complete certified tree-component snapshot. -/
theorem rootedCells_snap_replay
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {i j f : Nat}
    (hsupport : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfullI : Full m e r0 i f)
    (hfullJ : Full m e r0 j f)
    (hroot : RootedCells m e r0 i f cells) :
    snap m e r0 cells j = snap m e r0 cells i := by
  unfold snap
  apply List.map_congr_left
  intro c hc
  exact rootedAt_replay m e r0 hr0 hsupport hfullI hfullJ
    (hroot c hc)

/-- If two certified states use physical representatives of the same full
edge, their component snapshots agree. -/
theorem rootedCells_sameEdge_replay
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {i j f g : Nat}
    (hsupport : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfullI : Full m e r0 i f)
    (hfullJ : Full m e r0 j g)
    (hfg : SameEdge m f g)
    (hroot : RootedCells m e r0 i f cells) :
    snap m e r0 cells j = snap m e r0 cells i := by
  have hfullJf : Full m e r0 j f := by
    rcases hfg with rfl | h
    · exact hfullJ
    · subst g
      constructor
      · have h := hfullJ.2
        rw [m.bar_invol] at h
        exact h
      · exact hfullJ.1
  exact rootedCells_snap_replay m e r0 hr0 cells hsupport
    hfullI hfullJf hroot

end Echo
