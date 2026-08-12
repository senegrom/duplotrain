import TripleSelfLinkPlacement
import SixEventSharpClosure

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

/-- A raw periodic configuration reproduces the complete configuration one
period earlier at every time after the first completed lap. -/
theorem stepN_eq_one_period_earlier
    {w : Wiring} {start cycleStart : Nat × Tongues}
    {base period t : Nat}
    (hbase : stepN w base start = some cycleStart)
    (hperiod : stepN w period cycleStart = some cycleStart)
    (hafter : base + period ≤ t) :
    stepN w t start = stepN w (t - period) start := by
  let d := t - (base + period)
  have ht : t = base + (period + d) := by
    dsimp [d]
    omega
  have hprevious : t - period = base + d := by
    dsimp [d]
    omega
  calc
    stepN w t start = stepN w (period + d) cycleStart := by
      rw [ht, stepN_add, hbase]
      simp only [Option.bind_some]
    _ = stepN w d cycleStart := by
      rw [stepN_add, hperiod]
      simp only [Option.bind_some]
    _ = stepN w (t - period) start := by
      rw [hprevious, stepN_add, hbase]
      simp only [Option.bind_some]

/-- The preceding complete-configuration replay also reproduces the
restricted tongue vector. -/
theorem restrictedTonguesAt_eq_one_period_earlier
    {w : Wiring} {N : Nat} {start cycleStart : Nat × Tongues}
    {base period t : Nat}
    (hbase : stepN w base start = some cycleStart)
    (hperiod : stepN w period cycleStart = some cycleStart)
    (hafter : base + period ≤ t) :
    restrictedTonguesAt w N start t =
      restrictedTonguesAt w N start (t - period) := by
  have hstep := stepN_eq_one_period_earlier hbase hperiod hafter
  simp only [restrictedTonguesAt, tonguesAt]
  rw [hstep]

/-- A globally novel post-vector cannot be sampled after a complete raw lap
from an earlier periodic configuration. -/
theorem RawNovelAt.not_after_completed_period
    {w : Wiring} {N : Nat} {start cycleStart : Nat × Tongues}
    {base period k : Nat}
    (H : RawNovelAt w N start k)
    (hbase : stepN w base start = some cycleStart)
    (hperiod : stepN w period cycleStart = some cycleStart)
    (hperiodPositive : 0 < period)
    (hafter : base + period ≤ k + 1) : False := by
  have heq := restrictedTonguesAt_eq_one_period_earlier
    (N := N) hbase hperiod hafter
  exact (H.post_ne_earlier (by omega)) heq

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

/-- Rotating the same period to the outside of the self-link gives the useful
orientation for repair: the incoming edge is the self-link stem.  The trace
is still nonsimple because its final prefix passage exits through the
self-linked branch and the last passage starts at that same branch. -/
theorem RawCycleThroughSelfLink.outside_period_has_first_revisit
    {w : Wiring} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close) :
    ∃ outside passages,
      w.link (3 * (R.branch / 3)) = some outside ∧
      passages.length = R.period ∧
      PhysicalTrace w (outside, R.state) passages
        (outside, R.state) ∧
      ¬ SwitchSimple passages := by
  obtain ⟨outside, hmouth, hout, _houtPeriod⟩ := R.outside_period
  have hselfPeriod := R.self_period
  have hsplit : R.period = 1 + (R.period - 1) := by
    have hpositive : 0 < R.period := R.period_positive
    omega
  have hreturn :
      stepN w (R.period - 1) (outside, R.state) =
        some (R.branch, R.state) := by
    rw [hsplit, stepN_add, hout] at hselfPeriod
    exact hselfPeriod
  have hperiodTwo : 2 ≤ R.period := by
    by_cases hone : R.period = 1
    · have hcfg : (outside, R.state) = (R.branch, R.state) := by
        simpa [hone, stepN] using hreturn
      have houtside : outside = R.branch :=
        congrArg Prod.fst hcfg
      have hstemLink :
          w.link (3 * (R.branch / 3)) = some R.branch := by
        simpa [houtside] using hmouth
      have hstem : 3 * (R.branch / 3) = R.branch :=
        w.link_injective hstemLink R.self_link
      have hmod : R.branch % 3 = 0 := by omega
      exact (R.branch_port hmod).elim
    · have hpositive : 0 < R.period := R.period_positive
      omega
  obtain ⟨runwayPrefix, hprefixLength, hprefix⟩ :=
    physicalTrace_of_stepN w hreturn
  have hprefixNonempty : runwayPrefix ≠ [] := by
    intro hempty
    rw [hempty] at hprefixLength
    simp only [List.length_nil] at hprefixLength
    omega
  have hpin : pin R.state R.branch = R.state :=
    pin_of_agrees R.self_selected
  have harrive : arrive R.state R.branch =
      (3 * (R.branch / 3), R.state) := by
    simp [arrive, R.branch_port, hpin]
  have hlast : PhysicalTrace w (R.branch, R.state)
      [(R.branch, 3 * (R.branch / 3))]
      (outside, R.state) :=
    PhysicalTrace.cons harrive hmouth (PhysicalTrace.nil _)
  let passages :=
    runwayPrefix ++ [(R.branch, 3 * (R.branch / 3))]
  have hfull : PhysicalTrace w (outside, R.state) passages
      (outside, R.state) := by
    dsimp [passages]
    exact hprefix.append hlast
  have hlength : passages.length = R.period := by
    dsimp [passages]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  refine ⟨outside, passages, hmouth, hlength, hfull, ?_⟩
  intro hsimple
  cases hprefixEq : runwayPrefix with
  | nil => exact hprefixNonempty hprefixEq
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have hprefix' : PhysicalTrace w (outside, R.state)
          ((p, x) :: rest) (R.branch, R.state) := by
        simpa [hprefixEq] using hprefix
      have hlastLink :
          w.link (lastPassageExit x rest) = some R.branch :=
        hprefix'.last_link
      have hlastExit : lastPassageExit x rest = R.branch :=
        w.link_injective hlastLink R.self_link
      have hleft : R.branch / 3 ∈
          (((p, x) :: rest).map passageSwitch) := by
        have hmem := hprefix'.last_exit_switch_mem
        simpa [hlastExit] using hmem
      have hsimple' : SwitchSimple
          (((p, x) :: rest) ++
            [(R.branch, 3 * (R.branch / 3))]) := by
        simpa [passages, hprefixEq] using hsimple
      unfold SwitchSimple at hsimple'
      rw [List.map_append] at hsimple'
      have hparts := List.nodup_append.mp hsimple'
      have hright : R.branch / 3 ∈
          ([(R.branch, 3 * (R.branch / 3))].map passageSwitch) := by
        simp [passageSwitch]
      have hne := hparts.2.2 (R.branch / 3) hleft
        (R.branch / 3) hright
      exact hne rfl

/-- The outside-oriented first revisit either enters a simple cycle or
manufactures the reflector opposite the self-link stem.  This is the exact
physical fork needed for the subsequent pair/tail argument. -/
theorem RawCycleThroughSelfLink.outside_first_revisit_cycle_or_reflector
    {w : Wiring} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close) :
    ∃ outside atRepeat visited,
      w.link (3 * (R.branch / 3)) = some outside ∧
      stepN w visited (outside, R.state) = some atRepeat ∧
      (SettlesOnSimpleCycle w atRepeat ∨
        ∃ (A : ManufacturedReflector w outside
              (3 * (R.branch / 3)))
            (state : Tongues) (backSteps : Nat),
          PathGrooves A.toSupported.paths state ∧
          A.baseState = R.state ∧
          state = A.activatedState ∧
          stepN w backSteps atRepeat =
            some (3 * (R.branch / 3), state) ∧
          (∀ j, j ∉ A.exploration.map passageSwitch →
            state j = R.state j)) := by
  obtain ⟨outside, passages, hmouth, _hlength, htrace,
      hnonsimple⟩ := R.outside_period_has_first_revisit
  obtain ⟨atRepeat, visited, hvisited, houtcome⟩ :=
    htrace.first_revisit_activated_outcome hnonsimple hmouth
  exact ⟨outside, atRepeat, visited, hmouth, hvisited, houtcome⟩

end GeneralN
