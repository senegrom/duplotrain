import RunwaySpliceNovelty

/-!
# Three fresh vectors for a historical runway entry

The closed runway-splice theorem supplies four explicit Gray corners.  Its
first corner is the state at which the ambient run enters the manufactured
runway/lobe pair.  When that entry has already been recorded in the
construction history, only the other three corners can be globally fresh.

Everything here is stated over raw `Wiring`/`stepN` dynamics.  In particular,
the result is a strengthening of the local changed-forward branch, not an
assumption about the still-open global repair construction.
-/

namespace GeneralN

/-- Every finite prefix of a positive closed period is live. -/
theorem runway_period_stepN_some
    {w : Wiring} {start : Nat × Tongues} {period d : Nat}
    (hpositive : 0 < period)
    (hperiod : stepN w period start = some start) :
    ∃ finish, stepN w d start = some finish := by
  have hfar : stepN w ((d + 1) * period) start = some start :=
    stepN_mul_period_pair_novelty hperiod (d + 1)
  have hbound : d ≤ (d + 1) * period := by
    have hone : 1 ≤ period := by omega
    have hmul := Nat.mul_le_mul_left (d + 1) hone
    simp only [Nat.mul_one] at hmul
    omega
  exact stepN_prefix_some hbound hfar

end GeneralN
