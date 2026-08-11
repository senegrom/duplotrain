import FirstActivatedExact
import TripleSelfLinkSimpleCycleClosure
import TrackNoveltyCover

/-!
# Direct tongue count for the first simple-cycle outcome

The trace-retaining first-revisit theorem exposes a transient switch-simple
lap followed by a stable switch-simple lap.  Once the stable lap is reached,
every passage is grooved and every later tongue vector is the settled vector.
Thus the complete run is represented by the original prefix and one transient
lap: at most `2*N+1` positions.
-/

namespace GeneralN

/-- A switch-simple prefix followed by one transient lap and a stable grooved
lap exposes at most `2*N+1` distinct restricted tongue vectors. -/
theorem prefix_then_stable_simple_cycle_distinct_le_two_mul_succ
    {w : Wiring} {N L : Nat}
    {start atRepeat : Nat × Tongues}
    {cycle : List Passage} {settled : Tongues}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hreach : stepN w L start = some atRepeat)
    (hL : L ≤ N)
    (hnonempty : cycle ≠ [])
    (htransient : PhysicalTrace w atRepeat cycle
      (atRepeat.1, settled))
    (hstable : PhysicalTrace w (atRepeat.1, settled) cycle
      (atRepeat.1, settled))
    (hsimple : SwitchSimple cycle)
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 1 := by
  have hcycleLe : cycle.length ≤ N :=
    htransient.switchSimple_length_le_switches hN hsimple
  have hpositive : 0 < cycle.length := by
    cases cycle with
    | nil => exact (hnonempty rfl).elim
    | cons passage rest => simp
  have hperiod : stepN w cycle.length (atRepeat.1, settled) =
      some (atRepeat.1, settled) := hstable.sound
  have hgrooved : PassagesGrooved settled cycle :=
    hstable.grooved_of_switchSimple hsimple
  have hwindow : ∀ d, d ≤ cycle.length → ∃ port phase,
      stepN w d (atRepeat.1, settled) = some (port, phase) ∧
        (phase = settled ∨ phase = settled) := by
    intro d hd
    obtain ⟨port, hrun⟩ :=
      hstable.grooved_prefix_tongues settled hgrooved hd
    exact ⟨port, settled, hrun, Or.inl rfl⟩
  have hall : ∀ d, ∃ port phase,
      stepN w d (atRepeat.1, settled) = some (port, phase) ∧
        (phase = settled ∨ phase = settled) :=
    periodic_two_phase_prefix_tongues hpositive hperiod hwindow
  let cutoff := L + cycle.length
  have hboundary : stepN w cutoff start =
      some (atRepeat.1, settled) := by
    dsimp [cutoff]
    rw [stepN_add, hreach]
    exact htransient.sound
  let history := (List.range (cutoff + 1)).map
    (restrictedTonguesAt w N start)
  have hboundaryMem : VectorCount.restrict N settled ∈ history := by
    have hvector : restrictedTonguesAt w N start cutoff =
        VectorCount.restrict N settled := by
      simp [restrictedTonguesAt, tonguesAt, hboundary]
    rw [← hvector]
    exact List.mem_map.mpr
      ⟨cutoff, List.mem_range.mpr (by omega), rfl⟩
  have hcover : NoveltyCoverOn w N start times history 0 := by
    refine ⟨[], by simp, ?_⟩
    intro k hk
    simp only [List.nil_append]
    by_cases hpre : k ≤ cutoff
    · exact List.mem_map.mpr
        ⟨k, List.mem_range.mpr (by omega), rfl⟩
    · let d := k - cutoff
      have hkEq : k = cutoff + d := by
        dsimp [d]
        omega
      obtain ⟨port, phase, hrun, hphase⟩ := hall d
      have hphaseEq : phase = settled := hphase.elim id id
      subst phase
      have hglobal : stepN w k start = some (port, settled) := by
        rw [hkEq, stepN_add, hboundary]
        exact hrun
      have hvector : restrictedTonguesAt w N start k =
          VectorCount.restrict N settled := by
        simp [restrictedTonguesAt, tonguesAt, hglobal]
      rw [hvector]
      exact hboundaryMem
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistoryLen : history.length = cutoff + 1 := by
    simp [history]
  have hcutoff : cutoff + 1 ≤ 2 * N + 1 := by
    dsimp [cutoff]
    omega
  have hcount' : times.length ≤ history.length := by
    simpa using hcount
  omega

/-- First activation with a direct simple-cycle count.  The alternative is the
same exact manufactured-reflector certificate as in
`first_activated_quantitative_outcome_exact`. -/
theorem first_activated_count_outcome
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish)
    (hentry : w.link e = some start.1) :
    (∀ times : List Nat,
      (times.map (restrictedTonguesAt w N start)).Nodup →
      times.length ≤ 2 * N + 1) ∨
      ∃ (A : ManufacturedReflector w start.1 e)
          (state : Tongues),
        A.exploration.length + A.runway.length + 1 ≤ 2 * N + 1 ∧
        PathGrooves A.toSupported.paths state ∧
        A.baseState = start.2 ∧
        state = A.activatedState ∧
        stepN w (A.exploration.length + A.runway.length + 1) start =
          some (e, state) ∧
        (∀ j, j ∉ A.exploration.map passageSwitch →
          state j = start.2 j) := by
  obtain ⟨before, old, repeated, after, middle,
      hbeforeTrace, hafterTrace, hbeforeSimple, hold, hsameSwitch⟩ :=
    first_revisit_of_long_run hN hlive
  obtain ⟨runway, path, hsplit⟩ := List.append_of_mem hold
  rcases old with ⟨p, x⟩
  rcases repeated with ⟨q, y⟩
  subst before
  obtain ⟨atOld, hrunway, hexcursion⟩ :=
    hbeforeTrace.split_append
  have hatOldPort : atOld.1 = p := hexcursion.head_arrive.1
  rcases atOld with ⟨oldPort, u₀⟩
  simp only at hatOldPort
  subst oldPort
  obtain ⟨v, hrepeat⟩ := hafterTrace.head_arrive.2
  have hmiddlePort : middle.1 = q := hafterTrace.head_arrive.1
  rcases middle with ⟨middlePort, u⟩
  simp only at hmiddlePort
  subst middlePort
  have hsw : p / 3 = q / 3 := by
    simpa [passageSwitch] using hsameSwitch
  have hfork := first_revisit_cycle_traces_or_activated_reflector w
    hrunway hexcursion hbeforeSimple hsw hrepeat hentry
  have hvisited :
      stepN w (runway ++ (p, x) :: path).length start =
        some (q, u) := hbeforeTrace.sound
  have hvisitedLe :
      (runway ++ (p, x) :: path).length ≤ N :=
    hbeforeTrace.simple_length_le hN hbeforeSimple
  rcases hfork with hcycle | hreflector
  · left
    obtain ⟨cycle, settled, hnonempty, htransient,
      hstable, hsimpleCycle⟩ := hcycle
    intro times hnd
    exact prefix_then_stable_simple_cycle_distinct_le_two_mul_succ
      hN hvisited hvisitedLe hnonempty htransient hstable
      hsimpleCycle times hnd
  · right
    obtain ⟨A, state, hgrooves, hbase, hactivated,
      _hback, hpreserves⟩ := hreflector
    have hexplorationLe : A.exploration.length ≤ N :=
      A.exploration_trace.simple_length_le hN A.exploration_simple
    have hrunwayLe : A.runway.length ≤ A.exploration.length := by
      cases A <;>
        simp [ManufacturedReflector.runway,
          ManufacturedReflector.exploration]
    have hgroovesActivated :
        PathGrooves A.toSupported.paths A.activatedState := by
      rw [← hactivated]
      exact hgrooves
    have hbackExact :
        stepN w (A.runway.length + 1) A.preReturn =
          some (e, A.activatedState) := by
      have htrace := physicalTrace_contact_retraces_prefix
        A.runway_trace (A.runway_grooved hgroovesActivated)
        A.entryEdge A.return_arrive_mouth
      simpa [reversePassages_length] using htrace.sound
    have hreachBase :
        stepN w (A.exploration.length + A.runway.length + 1)
          (start.1, A.baseState) = some (e, A.activatedState) := by
      have hlen :
          A.exploration.length + A.runway.length + 1 =
            A.exploration.length + (A.runway.length + 1) := by omega
      rw [hlen, stepN_add, A.exploration_trace.sound]
      exact hbackExact
    refine ⟨A, state, ?_, hgrooves, hbase, hactivated, ?_, hpreserves⟩
    · omega
    · simpa [hbase, hactivated] using hreachBase

end GeneralN
