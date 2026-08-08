import NoFullReachFreeze

/-!
# Fixed support between arbitrary interval times
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Ordered form of support equality. -/
theorem coreSupportFixed_between_of_le
    {lo hi i j : Nat}
    (hfixed : CoreSupportFixed m e r0 lo hi)
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

/-- Symmetric arbitrary-time form. -/
theorem coreSupportFixed_between
    {lo hi i j : Nat}
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hiLo : lo ≤ i) (hiHi : i ≤ hi)
    (hjLo : lo ≤ j) (hjHi : j ≤ hi) :
    ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s := by
  by_cases hij : i ≤ j
  · exact coreSupportFixed_between_of_le m e r0 hfixed
      hiLo hij hjHi
  · have hji : j ≤ i := by omega
    exact fun s => (coreSupportFixed_between_of_le m e r0
      hfixed hjLo hji hiHi s).symm

/-- Restrict a fixed-support interval to a subinterval. -/
theorem coreSupportFixed_restrict
    {lo hi i j : Nat}
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hiLo : lo ≤ i) (hij : i ≤ j) (hjHi : j ≤ hi) :
    CoreSupportFixed m e r0 i j := by
  intro k hkLo hkLt s
  exact hfixed k (by omega) (by omega) s

end Echo
