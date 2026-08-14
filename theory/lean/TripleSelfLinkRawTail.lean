import TripleSelfLinkPlacement

/-!
# Raw closure after the placed self-link

This file consumes the raw endpoint outcomes produced by
`TripleSelfLinkPlacement`.  It is intentionally separate from the validated
placement checkpoint.

The first reduction below removes the easy periodic case without any clock
interpolation: once the raw closing configuration has completed a full lap,
every later configuration is an exact replay of one period earlier.  Hence a
globally novel close must occur strictly inside the first lap.  The remaining
first-lap case is where the physical self-link bounce must be converted into
the two-phase or four-phase tail used by the literal five-close bound.
-/

namespace GeneralN




theorem RawCycleThroughSelfLink.self_period_has_first_revisit
    {w : Wiring} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close) :
    ∃ passages,
      passages.length = R.period ∧
      PhysicalTrace w (R.branch, R.state) passages
        (R.branch, R.state) ∧
      ¬ SwitchSimple passages := by
  obtain ⟨passages, hlength, htrace⟩ :=
    physicalTrace_of_stepN w R.self_period
  refine ⟨passages, hlength, htrace, ?_⟩
  intro hsimple
  cases hpassages : passages with
  | nil =>
      rw [hpassages] at hlength
      simp only [List.length_nil] at hlength
      have hpositive : 0 < R.period := R.period_positive
      omega
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have htrace' : PhysicalTrace w (R.branch, R.state)
          ((p, x) :: rest) (R.branch, R.state) := by
        simpa [hpassages] using htrace
      have hsimple' : SwitchSimple ((p, x) :: rest) := by
        simpa [hpassages] using hsimple
      have hfirst : R.branch = p := htrace'.head_arrive.1
      have hlast :
          w.link (lastPassageExit x rest) = some R.branch :=
        htrace'.last_link
      have hlastExit : lastPassageExit x rest = R.branch :=
        w.link_injective hlast R.self_link
      exact (htrace'.simple_last_exit_ne_first_entry hsimple')
        (by omega)

/-- The first-revisit normal form can therefore be applied directly to the
actual periodic raw orbit.  This theorem is deliberately only a physical
fork: the simple-cycle branch and the manufactured-reflector branch are not
silently called a bounded tail. -/
theorem RawCycleThroughSelfLink.first_revisit_cycle_or_reflector
    {w : Wiring} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close) :
    ∃ atRepeat visited,
      stepN w visited (R.branch, R.state) = some atRepeat ∧
      (SettlesOnSimpleCycle w atRepeat ∨
        ∃ (A : ManufacturedReflector w R.branch R.branch)
            (state : Tongues) (backSteps : Nat),
          PathGrooves A.toSupported.paths state ∧
          A.baseState = R.state ∧
          state = A.activatedState ∧
          stepN w backSteps atRepeat = some (R.branch, state) ∧
          (∀ j, j ∉ A.exploration.map passageSwitch →
            state j = R.state j)) := by
  obtain ⟨passages, _hlength, htrace, hnonsimple⟩ :=
    R.self_period_has_first_revisit
  exact htrace.first_revisit_activated_outcome
    hnonsimple R.self_link

end GeneralN
