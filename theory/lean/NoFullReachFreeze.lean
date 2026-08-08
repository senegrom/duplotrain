import FullReachPersistenceCore

/-!
# Pointwise freezing from no-full reachability

Backward persistence of full reachability implies forward persistence of its
negation.  Combining that invariant with the one-step no-full/non-lobe lemma
freezes a cell throughout a fixed-support interval, without constructing its
support component.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Support is unchanged at every step of `[lo,hi]`. -/
def CoreSupportFixed (lo hi : Nat) : Prop :=
  ∀ k, lo ≤ k → k < hi → ∀ s,
    Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s

/-- At every prefix, no full edge reaches the cell and its register equals the
left-end register. -/
theorem noFullReach_reg_prefix
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi c : Nat}
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hnlobe : CoreNoLobe m c)
    (hno : CoreNoFullReach m e r0 lo c) :
    ∀ d, lo+d ≤ hi →
      CoreNoFullReach m e r0 (lo+d) c ∧
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
      have hlocal := coreNoFull_of_noFullReach m e r0 hprev.1
      have hreg := reg_step_eq_of_coreNoFull_coreNoLobe m e r0
        hrun hr0 (lo+d) c hs hlocal hnlobe
      have hnext := coreNoFullReach_step m e r0 hrun hr0
        (lo+d) c hs hprev.1
      refine ⟨?_, ?_⟩
      · simpa [Nat.add_assoc] using hnext
      · calc
          reg m e r0 (lo + (d+1)) c
              = reg m e r0 (lo+d+1) c := by omega
          _ = reg m e r0 (lo+d) c := hreg
          _ = reg m e r0 lo c := hprev.2

/-- Endpoint register equality. -/
theorem reg_frozen_of_noFullReach
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi c : Nat}
    (hlohi : lo ≤ hi)
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hnlobe : CoreNoLobe m c)
    (hno : CoreNoFullReach m e r0 lo c) :
    reg m e r0 hi c = reg m e r0 lo c := by
  have h := (noFullReach_reg_prefix m e r0 hrun hr0
    hfixed hnlobe hno (hi-lo) (by omega)).2
  have heq : lo + (hi-lo) = hi := by omega
  simpa [heq] using h

/-- Finite block form when every listed cell has no full reach at the left
endpoint. -/
theorem snap_frozen_of_noFullReach
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat} (cells : List Nat)
    (hlohi : lo ≤ hi)
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hnlobe : ∀ c ∈ cells, CoreNoLobe m c)
    (hno : ∀ c ∈ cells, CoreNoFullReach m e r0 lo c) :
    snap m e r0 cells hi = snap m e r0 cells lo := by
  unfold snap
  apply List.map_congr_left
  intro c hc
  exact reg_frozen_of_noFullReach m e r0 hrun hr0
    hlohi hfixed (hnlobe c hc) (hno c hc)

end Echo
