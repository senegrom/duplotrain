import TrackFiniteAlternation

/-!
# Productive writes cannot happen inside a pointwise retrace

A settled retrace window (every depth shows the settled tongue state)
admits no productive write: the vectors before and after any interior
step coincide.  Extracted from the serial-continuation module so the
sharp changed-contact and protected-pair closures do not depend on the
six-event programme.
-/

namespace GeneralN

/-- A productive write cannot occur strictly inside a window whose every
depth carries the settled state. -/
theorem productive_not_inside_pointwise_retrace
    {w : Wiring} {N repeatTime span openTime q : Nat}
    {start : Nat × Tongues} {old settled : Tongues}
    (hrepeat : stepN w repeatTime start = some (q, old))
    (hpointwise : ∀ d, d ≤ span →
      ∃ port, stepN w d (q, old) =
        some (port, if d = 0 then old else settled))
    (hproductive : RawProductiveAt w N start openTime)
    (hafter : repeatTime < openTime) :
    repeatTime + span ≤ openTime := by
  apply Classical.byContradiction
  intro hnot
  have hopenBeforeEnd : openTime < repeatTime + span := by omega
  let d := openTime - repeatTime
  have hdPositive : 0 < d := by
    dsimp [d]
    omega
  have hdLt : d < span := by
    dsimp [d]
    omega
  have hdSucc : d + 1 ≤ span := by omega
  have htime : repeatTime + d = openTime := by
    dsimp [d]
    omega
  have htimeSucc : repeatTime + (d + 1) = openTime + 1 := by omega
  obtain ⟨beforePort, hbeforeLocal⟩ := hpointwise d (by omega)
  obtain ⟨afterPort, hafterLocal⟩ := hpointwise (d + 1) hdSucc
  have hbeforeGlobal :
      stepN w openTime start = some (beforePort, settled) := by
    rw [← htime, stepN_add, hrepeat]
    simpa [Nat.ne_of_gt hdPositive] using hbeforeLocal
  have hafterGlobal :
      stepN w (openTime + 1) start = some (afterPort, settled) := by
    rw [← htimeSucc, stepN_add, hrepeat]
    simp only [Option.bind_some]
    simpa using hafterLocal
  apply hproductive.2
  simp [restrictedTonguesAt, tonguesAt,
    hbeforeGlobal, hafterGlobal]

end GeneralN
