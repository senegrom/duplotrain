import FullReachPersistencePaired

/-!
# Pointwise freezing from paired no-full reachability
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Occupied support is unchanged at each step of `[lo,hi]`. -/
def PairedSupportFixed (lo hi : Nat) : Prop :=
  ∀ k, lo ≤ k → k < hi → ∀ s,
    Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s

/-- Fixed support gives equality between ordered interval times. -/
theorem pairedSupportFixed_between_of_le
    {lo hi i j : Nat}
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hiLo : lo ≤ i) (hij : i ≤ j) (hjHi : j ≤ hi) :
    ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i+d := ⟨j-i, by omega⟩
  intro s
  induction d with
  | zero => exact Iff.rfl
  | succ d ih =>
      have hkLo : lo ≤ i+d := by omega
      have hkLt : i+d < hi := by omega
      exact ih.trans (hfixed (i+d) hkLo hkLt s)

/-- Symmetric arbitrary-time support equality. -/
theorem pairedSupportFixed_between
    {lo hi i j : Nat}
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hiLo : lo ≤ i) (hiHi : i ≤ hi)
    (hjLo : lo ≤ j) (hjHi : j ≤ hi) :
    ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s := by
  by_cases hij : i ≤ j
  · exact pairedSupportFixed_between_of_le m e r0
      hfixed hiLo hij hjHi
  · have hji : j ≤ i := by omega
    exact fun s => (pairedSupportFixed_between_of_le m e r0
      hfixed hjLo hji hiHi s).symm

/-- Restrict a fixed-support interval. -/
theorem pairedSupportFixed_restrict
    {lo hi i j : Nat}
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hiLo : lo ≤ i) (hij : i ≤ j) (hjHi : j ≤ hi) :
    PairedSupportFixed m e r0 i j := by
  intro k hkLo hkLt s
  exact hfixed k (by omega) (by omega) s

/-- Every prefix preserves no-full reach and the initial register. -/
theorem pairedNoFullReach_reg_prefix
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi c : Nat}
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hnlobe : CoreNoLobe m c)
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
      have hreg := reg_step_eq_of_coreNoFull_coreNoLobe m e r0
        hrun hr0 (lo+d) c hs hlocal hnlobe
      have hnext := pairedNoFullReach_step m e r0 hrun hr0
        (lo+d) c hs hprev.1
      refine ⟨?_, ?_⟩
      · simpa [Nat.add_assoc] using hnext
      · calc
          reg m e r0 (lo+(d+1)) c
              = reg m e r0 (lo+d+1) c := by omega
          _ = reg m e r0 (lo+d) c := hreg
          _ = reg m e r0 lo c := hprev.2

/-- Endpoint register equality. -/
theorem reg_frozen_of_pairedNoFullReach
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi c : Nat}
    (hlohi : lo ≤ hi)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hnlobe : CoreNoLobe m c)
    (hno : PairedNoFullReach m e r0 lo c) :
    reg m e r0 hi c = reg m e r0 lo c := by
  have h := (pairedNoFullReach_reg_prefix m e r0 hrun hr0
    hfixed hnlobe hno (hi-lo) (by omega)).2
  have heq : lo + (hi-lo) = hi := by omega
  simpa [heq] using h

end Echo
