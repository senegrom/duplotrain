import ReachReplay
import NoFullFreezeCore

/-!
# Full-edge reachability is backward-persistent

Under a support-preserving step, every full edge after the step comes from a
full edge before the step in the same occupied support component:

* unchanged full edges persist directly;
* a newly full arrival edge is fed by the overwritten full edge; and
* productive same-edge writes cannot create a full edge.

Consequently, if no full edge reaches a cell, that remains true forever while
support is fixed.  A non-lobe cell with this property is therefore frozen by
`NoFullFreezeCore`, without explicitly decomposing the support graph.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Fullness is independent of endpoint representative. -/
theorem persistence_full_bar_iff (k s : Nat) :
    Full m e r0 k (m.bar s) ↔ Full m e r0 k s := by
  unfold Full
  rw [m.bar_invol]
  exact and_comm

/-- Changing the representative of one jump edge preserves fullness. -/
theorem full_of_sameEdge
    {k s t : Nat} (h : SameEdge m s t) :
    Full m e r0 k s → Full m e r0 k t := by
  intro hs
  rcases h with rfl | rfl
  · exact hs
  · exact (persistence_full_bar_iff m e r0 k s).mpr hs

/-- Rooting reachability at the opposite endpoint representative changes
nothing. -/
theorem reach_bar_root
    {k f c : Nat}
    (h : ReachFromFull m e r0 k f c) :
    ReachFromFull m e r0 k (m.bar f) c := by
  induction h with
  | left =>
      simpa [m.bar_invol] using
        (ReachFromFull.right :
          ReachFromFull m e r0 k (m.bar f)
            (m.cellOf (m.bar (m.bar f))))
  | right =>
      exact (ReachFromFull.left :
        ReachFromFull m e r0 k (m.bar f)
          (m.cellOf (m.bar f)))
  | @step c d hprev hstep ih =>
      exact ReachFromFull.step ih hstep

/-- Same-edge representatives preserve support reachability. -/
theorem reach_of_sameEdge
    {k s t c : Nat} (h : SameEdge m s t) :
    ReachFromFull m e r0 k s c →
      ReachFromFull m e r0 k t c := by
  intro hs
  rcases h with rfl | rfl
  · exact hs
  · exact reach_bar_root m e r0 hs

/-- Re-root a support walk once both endpoints of the old root are reachable
from the new root. -/
theorem reach_rebase
    {k f g c : Nat}
    (hl : ReachFromFull m e r0 k g (m.cellOf f))
    (hr : ReachFromFull m e r0 k g (m.cellOf (m.bar f)))
    (h : ReachFromFull m e r0 k f c) :
    ReachFromFull m e r0 k g c := by
  induction h with
  | left => exact hl
  | right => exact hr
  | @step c d hprev hstep ih =>
      exact ReachFromFull.step ih hstep

/-- Reachability transports across equal supports. -/
theorem persistence_reach_support_congr
    {i j f c : Nat}
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (h : ReachFromFull m e r0 i f c) :
    ReachFromFull m e r0 j f c := by
  induction h with
  | left => exact ReachFromFull.left
  | right => exact ReachFromFull.right
  | @step c d hprev hstep ih =>
      apply ReachFromFull.step ih
      rcases hstep with ⟨s, hocc, hsrc, hdst⟩
      exact ⟨s, (hsupport s).mp hocc, hsrc, hdst⟩

/-- If the arrival edge is full after a support-preserving step, an old full
edge reaches everything that the arrival edge reaches. -/
theorem full_arrival_has_predecessor
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k c : Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hfullNew : Full m e r0 (k+1) (e (k+1)))
    (hreachNew : ReachFromFull m e r0 k (e (k+1)) c) :
    ∃ g, Full m e r0 k g ∧
      ReachFromFull m e r0 k g c := by
  let new := e (k+1)
  let old := reg m e r0 k (m.cellOf new)
  have holdCell : m.cellOf old = m.cellOf new := by
    exact reg_cell m e r0 hr0 k (m.cellOf new)
  have holdConf : Confirmed m e r0 k old :=
    old_register_confirmed m e r0 hr0 k (m.cellOf new)
  have hbarNew : Confirmed m e r0 k (m.bar new) := by
    simpa [new] using head_confirmed m e r0 hrun hr0 k
  by_cases heq : old = new
  · have hfullBefore : Full m e r0 k new := by
      constructor
      · simpa [heq] using holdConf
      · exact hbarNew
    exact ⟨new, hfullBefore, hreachNew⟩
  · by_cases hsame : SameEdge m old new
    · rcases hsame with hsame | hsame
      · exact absurd hsame.symm heq
      · have holdAfter : Confirmed m e r0 (k+1) old := by
          have hb := hfullNew.2
          simpa [new, hsame, m.bar_invol] using hb
        have hnewAfter : Confirmed m e r0 (k+1) new :=
          hfullNew.1
        have hcollapse : new = old :=
          confirmed_same_cell_eq m e r0 hnewAfter holdAfter
            holdCell.symm
        exact absurd hcollapse.symm heq
    · have holdAfterOcc : Occupied m e r0 (k+1) old :=
        (hsupport old).mp (Or.inl holdConf)
      have hfullOld : Full m e r0 k old :=
        old_edge_full_of_preserved m e r0
          hrun hr0 k (by
            unfold ProductiveStep
            simpa [old, new] using heq)
          holdAfterOcc hsame
      have hnewOccBefore : Occupied m e r0 k new :=
        (hsupport new).mpr (Or.inl hfullNew.1)
      have hleft : ReachFromFull m e r0 k old
          (m.cellOf new) := by
        have hroot : ReachFromFull m e r0 k old
            (m.cellOf old) := ReachFromFull.left
        simpa [holdCell] using hroot
      have hright : ReachFromFull m e r0 k old
          (m.cellOf (m.bar new)) := by
        apply ReachFromFull.step hleft
        exact ⟨new, hnewOccBefore, rfl, rfl⟩
      exact ⟨old, hfullOld,
        reach_rebase m e r0 hleft hright hreachNew⟩

/-- **Every full-reachable cell after a support-preserving step was already
full-reachable before it.** -/
theorem full_reach_predecessor
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k f c : Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hfull : Full m e r0 (k+1) f)
    (hreach : ReachFromFull m e r0 (k+1) f c) :
    ∃ g, Full m e r0 k g ∧
      ReachFromFull m e r0 k g c := by
  have hreachBefore := persistence_reach_support_congr m e r0
    (fun s => (hsupport s).symm) hreach
  rcases (confirmed_step m e r0 k f).mp hfull.1 with
      hfNew | ⟨_, hfOld⟩
  · have hsame : SameEdge m f (e (k+1)) := Or.inl hfNew
    have hfullNew := full_of_sameEdge m e r0 hsame hfull
    have hreachNew := reach_of_sameEdge m e r0 hsame hreachBefore
    exact full_arrival_has_predecessor m e r0 hrun hr0
      k c hsupport hfullNew hreachNew
  · rcases (confirmed_step m e r0 k (m.bar f)).mp hfull.2 with
        hbarNew | ⟨_, hbarOld⟩
    · have hfBar : e (k+1) = m.bar f := by
        exact hbarNew.symm
      have hsame : SameEdge m f (e (k+1)) := Or.inr hfBar
      have hfullNew := full_of_sameEdge m e r0 hsame hfull
      have hreachNew := reach_of_sameEdge m e r0 hsame hreachBefore
      exact full_arrival_has_predecessor m e r0 hrun hr0
        k c hsupport hfullNew hreachNew
    · exact ⟨f, ⟨hfOld, hbarOld⟩, hreachBefore⟩

/-- No full edge reaches the cell. -/
def NoFullReach (k c : Nat) : Prop :=
  ∀ f, Full m e r0 k f →
    ¬ ReachFromFull m e r0 k f c

/-- No-full reachability is forward invariant while support is fixed. -/
theorem noFullReach_step
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k c : Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hno : NoFullReach m e r0 k c) :
    NoFullReach m e r0 (k+1) c := by
  intro f hf hr
  rcases full_reach_predecessor m e r0 hrun hr0
      k f c hsupport hf hr with ⟨g, hg, hgr⟩
  exact hno g hg hgr

/-- No full reach implies the local `CoreNoFull` condition. -/
theorem coreNoFull_of_noFullReach
    {k c : Nat}
    (hno : NoFullReach m e r0 k c) :
    CoreNoFull m e r0 k c := by
  intro s hsc hfull
  apply hno s hfull
  have hroot : ReachFromFull m e r0 k s (m.cellOf s) :=
    ReachFromFull.left
  simpa [hsc] using hroot

end Echo
