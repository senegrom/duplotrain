import TrackGlobalRepair
import StateLaw
import FirstReflectorNovelty
import TripleSelfLinkSimpleCycleClosure

/-!
# Sharp tongue count for the first simple-cycle outcome

The old `2*N+1` count charged an entire transient cycle lap by position.  In
the actual first-revisit construction the same-exit cycle is much sharper:
either it is stable immediately, or its very first passage installs the
settled tongue vector and every remaining passage is already grooved at that
vector.  Hence the cycle tail has only the repeat vector and the settled
vector.  A switch-simple prefix of length at most `N` therefore gives at most
`N+2` vectors total.
-/

namespace GeneralN

/-- Prefix plus an at-most-two-phase transient/stable cycle tail. -/
theorem prefix_then_two_phase_cycle_distinct_le_succ_succ
    {w : Wiring} {N L : Nat}
    {start atRepeat : Nat × Tongues}
    {cycle : List Passage} {settled : Tongues}
    (hreach : stepN w L start = some atRepeat)
    (hL : L ≤ N)
    (hnonempty : cycle ≠ [])
    (htransient : PhysicalTrace w atRepeat cycle
      (atRepeat.1, settled))
    (hstable : PhysicalTrace w (atRepeat.1, settled) cycle
      (atRepeat.1, settled))
    (hsimple : SwitchSimple cycle)
    (htransientPhase : ∀ d, d ≤ cycle.length → ∃ port phase,
      stepN w d atRepeat = some (port, phase) ∧
        (phase = atRepeat.2 ∨ phase = settled))
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 2 := by
  have hpositive : 0 < cycle.length := by
    cases cycle with
    | nil => exact (hnonempty rfl).elim
    | cons passage rest => simp
  have hperiod : stepN w cycle.length (atRepeat.1, settled) =
      some (atRepeat.1, settled) := hstable.sound
  have hgrooved : PassagesGrooved settled cycle :=
    hstable.grooved_of_switchSimple hsimple
  have hsettledAll : ∀ d, ∃ port,
      stepN w d (atRepeat.1, settled) = some (port, settled) := by
    intro d
    have hwindow : ∀ r, r ≤ cycle.length → ∃ port phase,
        stepN w r (atRepeat.1, settled) = some (port, phase) ∧
          (phase = settled ∨ phase = settled) := by
      intro r hr
      obtain ⟨port, hrun⟩ :=
        hstable.grooved_prefix_tongues settled hgrooved hr
      exact ⟨port, settled, hrun, Or.inl rfl⟩
    obtain ⟨port, phase, hrun, hphase⟩ :=
      periodic_two_phase_prefix_tongues hpositive hperiod hwindow d
    exact ⟨port, by rcases hphase with h | h <;> rwa [h] at hrun⟩
  let history := ((List.range (L + 1)).map
    (restrictedTonguesAt w N start)) ++
      [VectorCount.restrict N settled]
  have hrepeatMem : VectorCount.restrict N atRepeat.2 ∈ history := by
    apply List.mem_append_left
    have hvec : restrictedTonguesAt w N start L =
        VectorCount.restrict N atRepeat.2 := by
      simp [restrictedTonguesAt, tonguesAt, hreach]
    rw [← hvec]
    exact List.mem_map.mpr ⟨L, List.mem_range.mpr (by omega), rfl⟩
  have hcover : NoveltyCoverOn w N start times history 0 := by
    refine ⟨[], by simp, ?_⟩
    intro k hk
    simp only [List.append_nil]
    by_cases hkpre : k ≤ L
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩
    · let d := k - L
      have hkEq : k = L + d := by dsimp [d]; omega
      by_cases hd : d ≤ cycle.length
      · obtain ⟨port, phase, hrun, hphase⟩ := htransientPhase d hd
        have hglobal : stepN w k start = some (port, phase) := by
          rw [hkEq, stepN_add, hreach]
          simpa using hrun
        have hvec : restrictedTonguesAt w N start k =
            VectorCount.restrict N phase := by
          simp [restrictedTonguesAt, tonguesAt, hglobal]
        rw [hvec]
        rcases hphase with h | h
        · rw [h]
          exact hrepeatMem
        · apply List.mem_append_right
          simp [h]
      · let r := d - cycle.length
        have hdEq : d = cycle.length + r := by dsimp [r]; omega
        obtain ⟨port, hrun⟩ := hsettledAll r
        have hglobal : stepN w k start = some (port, settled) := by
          rw [hkEq, hdEq, stepN_add, hreach]
          simp only [Option.bind_some]
          rw [stepN_add, htransient.sound]
          simpa using hrun
        have hvec : restrictedTonguesAt w N start k =
            VectorCount.restrict N settled := by
          simp [restrictedTonguesAt, tonguesAt, hglobal]
        rw [hvec]
        apply List.mem_append_right
        simp
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistory : history.length ≤ N + 2 := by
    simp [history]
    omega
  omega

/-- First activation with the sharp `N+2` simple-cycle count. -/
theorem first_activated_count_outcome_sharp
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish)
    (hentry : w.link e = some start.1) :
    (∀ times : List Nat,
      (times.map (restrictedTonguesAt w N start)).Nodup →
      times.length ≤ N + 2) ∨
      ∃ (A : ManufacturedReflector w start.1 e)
          (state : Tongues),
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
  obtain ⟨atOld, hrunway, hexcursion⟩ := hbeforeTrace.split_append
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
  have hvisitedLe : (runway ++ (p, x) :: path).length ≤ N :=
    hbeforeTrace.simple_length_le hN hbeforeSimple
  rcases hfork with hcycle | hreflector
  · left
    obtain ⟨cycle, settled, hnonempty, htransient,
      hstable, hsimpleCycle, hphase, _hpositive⟩ := hcycle
    intro times hnd
    exact prefix_then_two_phase_cycle_distinct_le_succ_succ
      hvisited hvisitedLe hnonempty htransient hstable
      hsimpleCycle hphase times hnd
  · right
    obtain ⟨A, state, hgrooves, hbase, hactivated,
      _hback, hpreserves⟩ := hreflector
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
      have hlen : A.exploration.length + A.runway.length + 1 =
          A.exploration.length + (A.runway.length + 1) := by omega
      rw [hlen, stepN_add, A.exploration_trace.sound]
      exact hbackExact
    refine ⟨A, state, hgrooves, hbase, hactivated, ?_, hpreserves⟩
    simpa [hbase, hactivated] using hreachBase

end GeneralN
