import TrackQuantitative
import FirstReflectorNovelty

/-! Exact-length manufactured-reflector extraction. -/

namespace GeneralN

/-- Exact-length version of `first_activated_quantitative_outcome`. -/
theorem first_activated_quantitative_outcome_exact
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish)
    (hentry : w.link e = some start.1) :
    EventuallyPeriodicWithin w start (3 * N) ∨
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
  have hfork := first_revisit_quantitative_or_activated_reflector w
    hrunway hexcursion hbeforeSimple hsw hrepeat hentry
  have hvisited :
      stepN w (runway ++ (p, x) :: path).length start =
        some (q, u) := hbeforeTrace.sound
  have hvisitedLe :
      (runway ++ (p, x) :: path).length ≤ N :=
    hbeforeTrace.simple_length_le hN hbeforeSimple
  rcases hfork with hcycle | hreflector
  · left
    obtain ⟨period, settled, hpos, hperiodLe, honce, hfixed⟩ :=
      hcycle
    have hlocal : EventuallyPeriodicWithin w (q, u)
        (2 * (runway ++ (p, x) :: path).length) := by
      refine ⟨period, period, (q, settled), hpos, ?_, honce, hfixed⟩
      omega
    exact (hlocal.prepend hvisited).weaken (by omega)
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
