import PairedNoFullReachFreeze

/-!
# Freezing relative to the occupied support

The older pointwise replay theorem classified a cell as `CoreNoLobe` only when
no jump edge in the entire abstract machine joined the cell to itself.  That is
stronger than the dynamics needs: a dormant internal edge cannot participate
in a fixed-support epoch.

This file replaces the structural condition by the exact support-relative one.
A cell is support-non-lobed when no *occupied* jump edge has both endpoints in
that cell.  The local freezing proof uses only this fact.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- No occupied jump edge has both endpoints in `c` at time `k`. -/
def CoreNoOccupiedLobe (k c : Nat) : Prop :=
  ∀ s, m.cellOf s = c → m.cellOf (m.bar s) = c →
    ¬ Occupied m e r0 k s

/-- No occupied lobe occurs in `c` anywhere in the interval. -/
def PairedNoOccupiedLobe (lo hi c : Nat) : Prop :=
  ∀ k, lo ≤ k → k ≤ hi → CoreNoOccupiedLobe m e r0 k c

/-- Support equality transports the support-relative non-lobe property. -/
theorem coreNoOccupiedLobe_congr
    {i j c : Nat}
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hno : CoreNoOccupiedLobe m e r0 i c) :
    CoreNoOccupiedLobe m e r0 j c := by
  intro s hs hbar hocc
  exact hno s hs hbar ((hsupport s).mpr hocc)

/-- **One support-preserving step freezes a no-full cell with no occupied
lobe.**  Dormant lobe edges are irrelevant. -/
theorem reg_step_eq_of_coreNoFull_coreNoOccupiedLobe
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k c : Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hnfull : CoreNoFull m e r0 k c)
    (hnlobe : CoreNoOccupiedLobe m e r0 k c) :
    reg m e r0 (k+1) c = reg m e r0 k c := by
  by_cases hdest : m.cellOf (e (k+1)) = c
  · subst c
    let new := e (k+1)
    let old := reg m e r0 k (m.cellOf new)
    have holdCell : m.cellOf old = m.cellOf new :=
      reg_cell m e r0 hr0 k (m.cellOf new)
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
      have holdOcc : Occupied m e r0 k old := Or.inl holdConf
      have holdAfter : Occupied m e r0 (k+1) old :=
        (hsupport old).mp holdOcc
      by_cases hsame : SameEdge m old new
      · rcases hsame with hsame | hsame
        · exact absurd hsame.symm heq
        · have hbarCell :
              m.cellOf (m.bar old) = m.cellOf new := by
            rw [← hsame]
          exact False.elim
            ((hnlobe old holdCell hbarCell) holdOcc)
      · have hfull : Full m e r0 k old := by
          exact old_edge_full_of_preserved m e r0
            hrun hr0 k hp holdAfter hsame
        exact absurd hfull (hnfull old holdCell)
  · exact reg_skip m e r0 (k := k) (c := c) hdest

/-- Every prefix preserves no-full reach and the initial register under the
support-relative non-lobe condition. -/
theorem pairedNoFullReach_reg_prefix_supportRelative
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi c : Nat}
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hnlobe : PairedNoOccupiedLobe m e r0 lo hi c)
    (hno : PairedNoFullReach m e r0 lo c) :
    ∀ d, lo+d ≤ hi →
      PairedNoFullReach m e r0 (lo+d) c ∧
      reg m e r0 (lo+d) c = reg m e r0 lo c := by
  intro d
  induction d with
  | zero =>
      intro _
      exact ⟨hno, rfl⟩
  | succ d ih =>
      intro hbound
      have hprevBound : lo+d ≤ hi := by omega
      have hprev := ih hprevBound
      have hkLo : lo ≤ lo+d := by omega
      have hkLt : lo+d < hi := by omega
      have hs := hfixed (lo+d) hkLo hkLt
      have hlocal := coreNoFull_of_pairedNoFullReach m e r0 hprev.1
      have hreg := reg_step_eq_of_coreNoFull_coreNoOccupiedLobe m e r0
        hrun hr0 (lo+d) c hs hlocal
        (hnlobe (lo+d) hkLo (Nat.le_of_lt hkLt))
      have hnext := pairedNoFullReach_step m e r0 hrun hr0
        (lo+d) c hs hprev.1
      refine ⟨?_, ?_⟩
      · simpa [Nat.add_assoc] using hnext
      · have hidx : lo + (d+1) = lo+d+1 := by omega
        calc
          reg m e r0 (lo+(d+1)) c
              = reg m e r0 (lo+d+1) c :=
                congrArg (fun n => reg m e r0 n c) hidx
          _ = reg m e r0 (lo+d) c := hreg
          _ = reg m e r0 lo c := hprev.2

/-- Endpoint register equality using only absence of occupied lobes. -/
theorem reg_frozen_of_pairedNoFullReach_supportRelative
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi c : Nat}
    (hlohi : lo ≤ hi)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hnlobe : PairedNoOccupiedLobe m e r0 lo hi c)
    (hno : PairedNoFullReach m e r0 lo c) :
    reg m e r0 hi c = reg m e r0 lo c := by
  have h := (pairedNoFullReach_reg_prefix_supportRelative m e r0
    hrun hr0 hfixed hnlobe hno (hi-lo) (by omega)).2
  have heq : lo + (hi-lo) = hi := by omega
  simpa [heq] using h

end Echo
