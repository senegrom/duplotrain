import RunwayHistoricalThree

/-!
# Eventual periodicity supplies raw prefixes of every length

Extracted from the removed Mellit support-interaction module: the one
liveness fact its downstream consumers actually kept using.
-/

namespace GeneralN

/-- Eventual periodicity supplies successful raw prefixes of every length. -/
theorem EventuallyPeriodic.stepN_some_all
    {w : Wiring} {start : Nat × Tongues}
    (H : EventuallyPeriodic w start) (d : Nat) :
    ∃ finish, stepN w d start = some finish := by
  obtain ⟨lead, period, settled, hpositive, hsettled, hperiod⟩ := H
  have hcycles :
      stepN w ((d + 1) * period) settled = some settled :=
    stepN_mul_period_pair_novelty hperiod (d + 1)
  have hfar :
      stepN w (lead + (d + 1) * period) start = some settled := by
    rw [stepN_add, hsettled]
    exact hcycles
  have hone : 1 ≤ period := by omega
  have hmul := Nat.mul_le_mul_left (d + 1) hone
  simp only [Nat.mul_one] at hmul
  have hbound : d ≤ lead + (d + 1) * period := by omega
  exact stepN_prefix_some hbound hfar

end GeneralN
