import PairedReachReplay
import NoFullFreezeCore

/-!
# Backward persistence of full reachability on the paired-walk model

Under a support-preserving step, every cell reachable from a full edge after
the step was reachable from some full edge before the step.  Therefore the
absence of full reach is forward invariant and can be combined with the local
no-full/non-lobe freezing lemma.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Fullness is endpoint-independent. -/
theorem pairedFull_bar_iff (k s : Nat) :
    Full m e r0 k (m.bar s) ↔ Full m e r0 k s := by
  unfold Full
  rw [m.bar_invol]
  exact and_comm

/-- Same-edge representatives preserve fullness. -/
theorem pairedFull_of_sameEdge
    {k s t : Nat} (h : SameEdge m s t) :
    Full m e r0 k s → Full m e r0 k t := by
  intro hs
  rcases h with rfl | rfl
  · exact hs
  · exact (pairedFull_bar_iff m e r0 k s).mpr hs

/-- The opposite endpoint is an equivalent reachability root. -/
theorem graphReach_bar_root
    {k f c : Nat}
    (h : GraphReach m e r0 k f c) :
    GraphReach m e r0 k (m.bar f) c := by
  induction h with
  | left =>
      simpa [m.bar_invol] using
        (GraphReach.right :
          GraphReach m e r0 k (m.bar f)
            (m.cellOf (m.bar (m.bar f))))
  | right =>
      exact (GraphReach.left :
        GraphReach m e r0 k (m.bar f)
          (m.cellOf (m.bar f)))
  | @step c d hprev hstep ih =>
      exact GraphReach.step ih hstep

/-- Same-edge representatives preserve reachability. -/
theorem graphReach_of_sameEdge
    {k s t c : Nat} (h : SameEdge m s t) :
    GraphReach m e r0 k s c → GraphReach m e r0 k t c := by
  intro hs
  rcases h with rfl | rfl
  · exact hs
  · exact graphReach_bar_root m e r0 hs

/-- Re-root a walk when both old root endpoints are reachable from the new
root. -/
theorem graphReach_rebase
    {k f g c : Nat}
    (hl : GraphReach m e r0 k g (m.cellOf f))
    (hr : GraphReach m e r0 k g (m.cellOf (m.bar f)))
    (h : GraphReach m e r0 k f c) :
    GraphReach m e r0 k g c := by
  induction h with
  | left => exact hl
  | right => exact hr
  | @step c d hprev hstep ih =>
      exact GraphReach.step ih hstep

/-- A full arrival edge descends from an old full edge in the same support
component. -/
theorem full_arrival_predecessor_paired
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k c : Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hfullNew : Full m e r0 (k+1) (e (k+1)))
    (hreachNew : GraphReach m e r0 k (e (k+1)) c) :
    ∃ g, Full m e r0 k g ∧ GraphReach m e r0 k g c := by
  let new := e (k+1)
  let old := reg m e r0 k (m.cellOf new)
  have holdCell : m.cellOf old = m.cellOf new :=
    reg_cell m e r0 hr0 k (m.cellOf new)
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
        have hcollapse : new = old :=
          confirmed_same_cell_eq m e r0 hfullNew.1 holdAfter
            holdCell.symm
        exact absurd hcollapse.symm heq
    · have holdAfterOcc : Occupied m e r0 (k+1) old :=
        (hsupport old).mp (Or.inl holdConf)
      have hp : ProductiveStep m e r0 k := by
        unfold ProductiveStep
        simpa [old, new] using heq
      have hfullOld : Full m e r0 k old :=
        old_edge_full_of_preserved m e r0
          hrun hr0 k hp holdAfterOcc hsame
      have hnewOccBefore : Occupied m e r0 k new :=
        (hsupport new).mpr (Or.inl hfullNew.1)
      have hleft : GraphReach m e r0 k old (m.cellOf new) := by
        have hroot : GraphReach m e r0 k old (m.cellOf old) :=
          GraphReach.left
        rw [holdCell] at hroot
        exact hroot
      have hright : GraphReach m e r0 k old
          (m.cellOf (m.bar new)) := by
        apply GraphReach.step hleft
        exact ⟨new, hnewOccBefore, rfl, rfl⟩
      exact ⟨old, hfullOld,
        graphReach_rebase m e r0 hleft hright hreachNew⟩

/-- **Every full-reachable cell after the step was already full-reachable.** -/
theorem full_reach_predecessor_paired
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k f c : Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hfull : Full m e r0 (k+1) f)
    (hreach : GraphReach m e r0 (k+1) f c) :
    ∃ g, Full m e r0 k g ∧ GraphReach m e r0 k g c := by
  have hreachBefore := graphReach_support_congr m e r0
    (fun s => (hsupport s).symm) hreach
  rcases (confirmed_step m e r0 k f).mp hfull.1 with
      hfNew | ⟨_, hfOld⟩
  · have hsame : SameEdge m f (e (k+1)) :=
      Or.inl hfNew.symm
    have hfullNew := pairedFull_of_sameEdge m e r0 hsame hfull
    have hreachNew := graphReach_of_sameEdge m e r0 hsame hreachBefore
    exact full_arrival_predecessor_paired m e r0 hrun hr0
      k c hsupport hfullNew hreachNew
  · rcases (confirmed_step m e r0 k (m.bar f)).mp hfull.2 with
        hbarNew | ⟨_, hbarOld⟩
    · have hsame : SameEdge m f (e (k+1)) :=
        Or.inr hbarNew.symm
      have hfullNew := pairedFull_of_sameEdge m e r0 hsame hfull
      have hreachNew := graphReach_of_sameEdge m e r0 hsame hreachBefore
      exact full_arrival_predecessor_paired m e r0 hrun hr0
        k c hsupport hfullNew hreachNew
    · exact ⟨f, ⟨hfOld, hbarOld⟩, hreachBefore⟩

/-- No full edge reaches the cell. -/
def PairedNoFullReach (k c : Nat) : Prop :=
  ∀ f, Full m e r0 k f → ¬ GraphReach m e r0 k f c

/-- No-full reachability persists forward under fixed support. -/
theorem pairedNoFullReach_step
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k c : Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hno : PairedNoFullReach m e r0 k c) :
    PairedNoFullReach m e r0 (k+1) c := by
  intro f hf hr
  rcases full_reach_predecessor_paired m e r0 hrun hr0
      k f c hsupport hf hr with ⟨g, hg, hgr⟩
  exact hno g hg hgr

/-- No full reach implies the local no-full condition. -/
theorem coreNoFull_of_pairedNoFullReach
    {k c : Nat}
    (hno : PairedNoFullReach m e r0 k c) :
    CoreNoFull m e r0 k c := by
  intro s hsc hfull
  apply hno s hfull
  have hroot : GraphReach m e r0 k s (m.cellOf s) :=
    GraphReach.left
  rw [hsc] at hroot
  exact hroot

end Echo
