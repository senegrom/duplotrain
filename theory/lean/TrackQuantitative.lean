import TrackGlobalRepair
import StateLaw

/-!
# Quantitative extraction from the direct physical-track theorem

`TrackGlobalRepair` proves that every sufficiently long live lazy-point run
is eventually periodic.  Its qualitative predicate deliberately forgets the
size of the transient and period.  This file retains that information and
turns it into a count of observed configurations.

This file completes that extraction.  `state_law_linear` proves, directly in
the language of `Wiring` and `stepN`, that one train sees at most `34*N+3`
distinct tongue vectors.  The sharper coefficient-one target `StateLaw`
(`N+6`, conjecturally improvable to `N+4`) remains open.
-/

namespace GeneralN

/-- Quantitative eventual periodicity: after `lead` steps the run repeats a
positive `period`, and the complete lasso fits below `cap`. -/
def EventuallyPeriodicWithin
    (w : Wiring) (start : Nat × Tongues) (cap : Nat) : Prop :=
  ∃ lead period settled,
    0 < period ∧
    lead + period ≤ cap ∧
    stepN w lead start = some settled ∧
    stepN w period settled = some settled

theorem EventuallyPeriodicWithin.weaken
    {w : Wiring} {start : Nat × Tongues} {small large : Nat}
    (h : EventuallyPeriodicWithin w start small)
    (hle : small ≤ large) :
    EventuallyPeriodicWithin w start large := by
  obtain ⟨lead, period, settled, hpos, hcap, hlead, hperiod⟩ := h
  exact ⟨lead, period, settled, hpos,
    Nat.le_trans hcap hle, hlead, hperiod⟩

/-- A live prefix adds exactly its length to a quantitative lasso cap. -/
theorem EventuallyPeriodicWithin.prepend
    {w : Wiring} {start middle : Nat × Tongues}
    {travel cap : Nat}
    (hprefix : stepN w travel start = some middle)
    (hperiodic : EventuallyPeriodicWithin w middle cap) :
    EventuallyPeriodicWithin w start (travel + cap) := by
  obtain ⟨lead, period, settled, hpos, hcap, hlead, hperiod⟩ :=
    hperiodic
  refine ⟨travel + lead, period, settled, hpos, ?_, ?_, hperiod⟩
  · omega
  · rw [stepN_add, hprefix]
    exact hlead

/-- Every reached suffix of a bounded deterministic lasso has the same cap.
Before the lead, discard the elapsed prefix; after the lead, the reached
configuration lies directly on the same period. -/
theorem EventuallyPeriodicWithin.forward
    {w : Wiring} {start middle : Nat × Tongues}
    {travel cap : Nat}
    (hperiodic : EventuallyPeriodicWithin w start cap)
    (hreach : stepN w travel start = some middle) :
    EventuallyPeriodicWithin w middle cap := by
  obtain ⟨lead, period, settled, hpos, hcap, hlead, hperiod⟩ :=
    hperiodic
  by_cases hle : travel ≤ lead
  · let remaining := lead - travel
    have hlen : lead = travel + remaining := by
      dsimp [remaining]
      omega
    have hmiddleSettled :
        stepN w remaining middle = some settled := by
      rw [hlen, stepN_add, hreach] at hlead
      exact hlead
    exact ⟨remaining, period, settled, hpos, by omega,
      hmiddleSettled, hperiod⟩
  · let offset := travel - lead
    have hlen : travel = lead + offset := by
      dsimp [offset]
      omega
    have hsettledMiddle :
        stepN w offset settled = some middle := by
      rw [hlen, stepN_add, hlead] at hreach
      exact hreach
    have hcycle : stepN w period middle = some middle := by
      have hround :
          stepN w (period + offset) settled = some middle := by
        rw [stepN_add, hperiod]
        exact hsettledMiddle
      have hcomm : period + offset = offset + period := by omega
      rw [hcomm, stepN_add, hsettledMiddle] at hround
      exact hround
    exact ⟨0, period, middle, hpos, by omega,
      by simp [stepN], hcycle⟩





theorem first_revisit_quantitative_or_activated_reflector
    (w : Wiring) {start : Nat × Tongues}
    {runway path : List Passage}
    {p x q y e : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hsw : p / 3 = q / 3)
    (hrepeat : arrive u q = (y, v))
    (hentry : w.link e = some start.1) :
    (∃ period settled,
      0 < period ∧
      period ≤ (runway ++ (p, x) :: path).length ∧
      stepN w period (q, u) = some (q, settled) ∧
      stepN w period (q, settled) = some (q, settled)) ∨
    ∃ (A : ManufacturedReflector w start.1 e) (state : Tongues),
      PathGrooves A.toSupported.paths state ∧
      A.baseState = start.2 ∧
      state = A.activatedState ∧
      stepN w (runway.length + 1) (q, u) = some (e, state) ∧
      (∀ j, j ∉ A.exploration.map passageSwitch →
        state j = start.2 j) := by
  have hsimpleExcursion : SwitchSimple ((p, x) :: path) := by
    unfold SwitchSimple at hsimple ⊢
    simp only [List.map_append] at hsimple
    exact (List.nodup_append.mp hsimple).2.1
  have holdStem :
      p = 3 * passageSwitch (p, x) ∨
        x = 3 * passageSwitch (p, x) :=
    hexcursion.passage_stem_endpoint (p, x) List.mem_cons_self
  have hrepeatStem :
      q = 3 * passageSwitch (q, y) ∨
        y = 3 * passageSwitch (q, y) := by
    have hs := arrive_stem_endpoint u q
    rw [hrepeat] at hs
    exact hs
  have hsw' : passageSwitch (p, x) = passageSwitch (q, y) := by
    simpa [passageSwitch] using hsw
  have hshare : p = q ∨ p = y ∨ x = q ∨ x = y :=
    recorded_passages_share_port holdStem hrepeatStem hsw'
  have hfar : w.link start.1 = some e := w.symm _ _ hentry
  have hsupport := crossed_revisit_support_grooved
    hrunway hexcursion hsimple hsw hrepeat
  have hpreserves :
      ∀ j, j ∉ (runway ++ (p, x) :: path).map passageSwitch →
        v j = start.2 j := by
    intro j hforeign
    have hu := (hrunway.append hexcursion).preserves j (by
      intro passage hp hEq
      apply hforeign
      exact List.mem_map.mpr ⟨passage, hp, hEq⟩)
    have hjq : j ≠ q / 3 := by
      intro hEq
      apply hforeign
      apply List.mem_map.mpr
      refine ⟨(p, x),
        List.mem_append_right runway List.mem_cons_self, ?_⟩
      simp only [passageSwitch]
      omega
    exact (arrive_preserves_other hrepeat hjq).trans hu
  rcases hshare with hpq | hpy | hxq | hxy
  · subst q
    left
    have hp := hexcursion.simple_return_period hsimpleExcursion
    refine ⟨((p, x) :: path).length, u, by simp, ?_, hp, hp⟩
    simp
  · subst y
    have hback := hrunway.simple_cross_exit_retraces_prefix
      hexcursion hsimple hrepeat
    rw [hfar] at hback
    by_cases hxq : x = q
    · subst q
      have hpathNil := same_exit_excursion_path_nil
        hexcursion hsimpleExcursion
      subst path
      have hfullGrooved :=
        (hrunway.append hexcursion).grooved_of_switchSimple hsimple
      have hold : arrive u x = (p, u) :=
        hfullGrooved (p, x)
          (List.mem_append_right runway List.mem_cons_self)
      have holdGroove := hold
      rw [hrepeat] at hold
      injection hold with _ huv
      subst v
      have hself : w.link x = some x := by
        simpa [lastPassageExit] using hexcursion.last_link
      let A : ManufacturedStayReflector w start.1 e := {
        base := start.2
        mouthState := u₀
        returnState := u
        runway := runway
        mouth := p
        arm := x
        runwayTrace := by simpa using hrunway
        coreTrace := by simpa using hexcursion
        simple := hsimple
        stemEndpoint := hexcursion.passage_stem_endpoint
          (p, x) List.mem_cons_self
        selfLink := hself
        entryEdge := hentry
      }
      refine Or.inr ⟨.stay A, u, ?_, rfl, rfl, hback, ?_⟩
      · change PathGrooves [runway, [(p, x)]] u
        apply pathGrooves_pair.mpr
        exact ⟨(pathGrooves_pair.mp hsupport).1,
          passagesGrooved_singleton.mpr holdGroove⟩
      · simpa [ManufacturedReflector.exploration] using hpreserves
    · let A : ManufacturedFlipReflector w start.1 e := {
        base := start.2
        mouthState := u₀
        returnState := u
        afterReturn := v
        runway := runway
        candy := path
        mouth := p
        firstArm := x
        secondArm := q
        runwayTrace := by simpa using hrunway
        candyTrace := hexcursion
        simple := hsimple
        crossed := hrepeat
        arms_ne := hxq
        entryEdge := hentry
      }
      refine Or.inr ⟨.flip A, v, ?_, rfl, rfl, hback, ?_⟩
      · change PathGrooves [runway, path] v
        exact hsupport
      · simpa [ManufacturedReflector.exploration] using hpreserves
  · subst q
    have hfull := hrunway.append hexcursion
    have hgrooved := hfull.grooved_of_switchSimple hsimple
    have hold : arrive u x = (p, u) :=
      hgrooved (p, x)
        (List.mem_append_right runway List.mem_cons_self)
    have holdGroove := hold
    rw [hrepeat] at hold
    injection hold with hyp huv
    subst y
    subst v
    have hback := hrunway.simple_cross_exit_retraces_prefix
      hexcursion hsimple (by simpa using hrepeat)
    rw [hfar] at hback
    have hpathNil := same_exit_excursion_path_nil
      hexcursion hsimpleExcursion
    subst path
    have hself : w.link x = some x := by
      simpa [lastPassageExit] using hexcursion.last_link
    let A : ManufacturedStayReflector w start.1 e := {
      base := start.2
      mouthState := u₀
      returnState := u
      runway := runway
      mouth := p
      arm := x
      runwayTrace := by simpa using hrunway
      coreTrace := by simpa using hexcursion
      simple := hsimple
      stemEndpoint := hexcursion.passage_stem_endpoint
        (p, x) List.mem_cons_self
      selfLink := hself
      entryEdge := hentry
    }
    refine Or.inr ⟨.stay A, u, ?_, rfl, rfl, hback, ?_⟩
    · change PathGrooves [runway, [(p, x)]] u
      apply pathGrooves_pair.mpr
      exact ⟨(pathGrooves_pair.mp hsupport).1,
        passagesGrooved_singleton.mpr holdGroove⟩
    · simpa [ManufacturedReflector.exploration] using hpreserves
  · subst y
    left
    have hcycle := hexcursion.simple_same_exit_enters_period
      hsimpleExcursion hrepeat
    refine ⟨((q, x) :: path).length, v, by simp, ?_,
      hcycle.1, hcycle.2⟩
    simp

/-- Quantitative first-component theorem.  Within a live `N+1` prefix the
run either has a lasso of size at most `3*N`, or reaches the activated far
side of one manufactured reflector in at most `2*N+1` steps. -/
theorem first_activated_quantitative_outcome
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish)
    (hentry : w.link e = some start.1) :
    EventuallyPeriodicWithin w start (3 * N) ∨
      ∃ (A : ManufacturedReflector w start.1 e)
          (state : Tongues) (travel : Nat),
        travel ≤ 2 * N + 1 ∧
        PathGrooves A.toSupported.paths state ∧
        A.baseState = start.2 ∧
        state = A.activatedState ∧
        stepN w travel start = some (e, state) ∧
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
      hback, hpreserves⟩ := hreflector
    refine ⟨A, state,
      (runway ++ (p, x) :: path).length + runway.length + 1,
      ?_, hgrooves, hbase, hactivated, ?_, hpreserves⟩
    · have hrunwayLe : runway.length ≤
          (runway ++ (p, x) :: path).length := by simp
      omega
    · have hlen :
          (runway ++ (p, x) :: path).length + runway.length + 1 =
            (runway ++ (p, x) :: path).length +
              (runway.length + 1) := by omega
      rw [hlen, stepN_add, hvisited]
      exact hback
end GeneralN
