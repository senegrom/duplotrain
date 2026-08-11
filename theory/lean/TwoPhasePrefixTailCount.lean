import BoundaryOverlapTailCount

/-!
# Two-phase prefix followed by a directly counted tail

The endpoint phase is shared by the prefix and suffix.  Therefore a two-phase
prefix adds at most one vector beyond the suffix's own direct count.
-/

namespace GeneralN

/-- A prefix whose complete tongue vector is always its initial or endpoint
state, followed by a suffix with direct cap `cap`, has at most `cap+1`
distinct restricted vectors. -/
theorem two_phase_prefix_then_direct_tail_distinct_le_succ
    {w : Wiring} {N lead cap : Nat}
    {start endpoint : Nat × Tongues}
    (hreach : stepN w lead start = some endpoint)
    (hphase : ∀ d, d ≤ lead →
      ∃ port phase,
        stepN w d start = some (port, phase) ∧
        (phase = start.2 ∨ phase = endpoint.2))
    (htail : ∀ (tailTimes : List Nat),
      (∀ k ∈ tailTimes, (stepN w k endpoint).isSome) →
      (tailTimes.map (restrictedTonguesAt w N endpoint)).Nodup →
      tailTimes.length ≤ cap)
    (hcapPos : 0 < cap)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ cap + 1 := by
  let initialVector := VectorCount.restrict N start.2
  let endpointVector := VectorCount.restrict N endpoint.2
  let history := [initialVector, endpointVector]
  have hprefixCover : ∀ d, d ≤ lead →
      restrictedTonguesAt w N start d ∈ history := by
    intro d hd
    obtain ⟨port, phase, hrun, hphaseEq⟩ := hphase d hd
    have hvector : restrictedTonguesAt w N start d =
        VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hrun]
    rw [hvector]
    rcases hphaseEq with rfl | rfl
    · simp [history, initialVector]
    · simp [history, endpointVector]
  have hboundary : VectorCount.restrict N endpoint.2 ∈ history := by
    simp [history, endpointVector]
  have hcount := boundary_history_then_direct_tail_distinct_le
    hreach history hprefixCover hboundary htail hcapPos
      times hlive hnd
  have hhistory : history.length = 2 := by simp [history]
  rw [hhistory] at hcount
  omega

end GeneralN
