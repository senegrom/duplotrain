import PairedPointwiseReplayCore

/-!
# Deriving the pointwise replay cover from active-lobe completeness

A lobe cell which is never written during the interval is constant by
`reg_stable`.  Hence only lobe cells actually written during the interval need
a Boolean representative.  If the active-lobe list covers all such cells,
every represented cell is automatically classified as

* active lobe;
* structurally non-lobe; or
* frozen.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Cell `c` is written strictly after `lo` and no later than `hi`. -/
def CellWrittenIn
    (m : Machine) (e r0 : Nat → Nat)
    (lo hi c : Nat) : Prop :=
  ∃ l, lo < l ∧ l ≤ hi ∧ m.cellOf (e l) = c

/-- Every structurally lobed represented cell which is written in the interval
has a representative in the active-lobe list. -/
def ActiveLobesComplete
    (m : Machine) (e r0 : Nat → Nat)
    (lo hi : Nat) (cells lobes : List Nat) : Prop :=
  ∀ c ∈ cells,
    (∃ a, m.cellOf a = c ∧ m.cellOf (m.bar a) = c) →
    CellWrittenIn m e r0 lo hi c →
    ∃ b, b ∈ lobes ∧ m.cellOf b = c

/-- No writes in the interval make one register coordinate constant. -/
theorem pairedPointFrozen_of_noWrite
    {lo hi c : Nat}
    (hno : ¬ CellWrittenIn m e r0 lo hi c) :
    PairedPointFrozen m e r0 lo hi c := by
  intro i hiLo hiHi j hjLo hjHi
  by_cases hij : i ≤ j
  · have hstable :
        reg m e r0 (i + (j-i)) c = reg m e r0 i c := by
      apply reg_stable m e r0 (j-i)
      intro l hil hlj
      intro heq
      apply hno
      exact ⟨l, by omega, by omega, heq⟩
    have hnorm : i + (j-i) = j := by omega
    rw [hnorm] at hstable
    exact hstable.symm
  · have hji : j ≤ i := by omega
    have hstable :
        reg m e r0 (j + (i-j)) c = reg m e r0 j c := by
      apply reg_stable m e r0 (i-j)
      intro l hjl hli
      intro heq
      apply hno
      exact ⟨l, by omega, by omega, heq⟩
    have hnorm : j + (i-j) = i := by omega
    rw [hnorm] at hstable
    exact hstable

end Echo
