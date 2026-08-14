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

/-- A positive return period is a quantitative lasso with zero lead. -/
theorem eventuallyPeriodicWithin_of_period
    {w : Wiring} {start : Nat × Tongues} {period cap : Nat}
    (hpos : 0 < period)
    (hle : period ≤ cap)
    (hperiod : stepN w period start = some start) :
    EventuallyPeriodicWithin w start cap := by
  exact ⟨0, period, start, hpos, by omega,
    by simp [stepN], hperiod⟩

/-- Repeating a closed deterministic segment any number of times returns to
the same configuration. -/
theorem stepN_mul_period
    {w : Wiring} {settled : Nat × Tongues} {period : Nat}
    (hperiod : stepN w period settled = some settled) :
    ∀ q, stepN w (q * period) settled = some settled := by
  intro q
  induction q with
  | zero => simp [stepN]
  | succ q ih =>
      have hlen : (q + 1) * period = q * period + period := by
        simp [Nat.add_mul]
      rw [hlen, stepN_add, ih]
      exact hperiod

/-- Every time after the lead is represented by one time in the half-open
lasso window `[lead, lead+period)`. -/
theorem EventuallyPeriodicWithin.reduce_time
    {w : Wiring} {start : Nat × Tongues} {cap k : Nat}
    (h : EventuallyPeriodicWithin w start cap) :
    ∃ representative,
      representative < cap ∧
      stepN w k start = stepN w representative start := by
  obtain ⟨lead, period, settled, hpos, hcap, hlead, hperiod⟩ := h
  by_cases hk : k < lead
  · exact ⟨k, Nat.lt_of_lt_of_le hk (Nat.le_trans
      (Nat.le_add_right lead period) hcap), rfl⟩
  · let q := (k - lead) / period
    let r := (k - lead) % period
    have hr : r < period := Nat.mod_lt _ hpos
    have hkEq : k = lead + q * period + r := by
      dsimp [q, r]
      have hdiv := Nat.div_add_mod (k - lead) period
      rw [Nat.mul_comm period ((k - lead) / period)] at hdiv
      omega
    have hrep : lead + r < cap := by omega
    refine ⟨lead + r, hrep, ?_⟩
    rw [hkEq, Nat.add_assoc lead (q * period) r,
      stepN_add w lead (q * period + r) start, hlead]
    simp only [Option.bind_some]
    rw [stepN_add w (q * period) r settled,
      stepN_mul_period hperiod q]
    simp only [Option.bind_some]
    rw [stepN_add w lead r start, hlead]
    simp

private theorem nodup_map_fibre
    {α β γ : Type} (xs : List α) (f : α → β) (g : α → γ)
    (hfibre : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → g x = g y)
    (hnd : (xs.map g).Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      constructor
      · intro hmem
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
        have hgy := hfibre x List.mem_cons_self y
          (List.mem_cons_of_mem _ hy) hfy.symm
        exact hnd.1 (List.mem_map.mpr ⟨y, hy, hgy.symm⟩)
      · exact ih
          (fun a ha b hb => hfibre a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb)) hnd.2

/-- A bounded lasso permits at most `cap` pairwise-distinct complete train
configurations at arbitrary sampled live times. -/
theorem EventuallyPeriodicWithin.configuration_count
    {w : Wiring} {start : Nat × Tongues} {cap : Nat}
    (h : EventuallyPeriodicWithin w start cap)
    (ks : List Nat)
    (_hlive : ∀ k ∈ ks, (stepN w k start).isSome)
    (hnd : (ks.map fun k => (stepN w k start).getD start).Nodup) :
    ks.length ≤ cap := by
  classical
  let representative : Nat → Nat := fun k =>
    Classical.choose (h.reduce_time (k := k))
  have hrepLt : ∀ k, representative k < cap := by
    intro k
    exact (Classical.choose_spec (h.reduce_time (k := k))).1
  have hrep : ∀ k,
      stepN w k start = stepN w (representative k) start := by
    intro k
    exact (Classical.choose_spec (h.reduce_time (k := k))).2
  have hrepNodup : (ks.map representative).Nodup := by
    apply nodup_map_fibre ks representative
      (fun k => (stepN w k start).getD start)
    · intro i hi j hj hEq
      have hiEq := hrep i
      have hjEq := hrep j
      rw [hEq] at hiEq
      rw [hiEq, ← hjEq]
    · exact hnd
  have hlt : ∀ r ∈ ks.map representative, r < cap := by
    intro r hr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hr
    exact hrepLt k
  simpa only [List.length_map] using
    nodup_nat_lt_length hrepNodup hlt

/-- Distinct restricted tongue vectors are in particular distinct complete
train configurations, so the same lasso cap bounds the state vectors asked
for by `StateLaw`. -/
theorem EventuallyPeriodicWithin.tongue_vector_count
    {w : Wiring} {start : Nat × Tongues} {cap N : Nat}
    (h : EventuallyPeriodicWithin w start cap)
    (ks : List Nat)
    (hlive : ∀ k ∈ ks, (stepN w k start).isSome)
    (hnd : (ks.map fun k =>
      VectorCount.restrict N (tonguesAt w start k)).Nodup) :
    ks.length ≤ cap := by
  have hconfigs :
      (ks.map fun k => (stepN w k start).getD start).Nodup := by
    apply nodup_map_fibre ks
      (fun k => (stepN w k start).getD start)
      (fun k => VectorCount.restrict N (tonguesAt w start k))
    · intro i hi j hj hEq
      exact congrArg (fun c : Nat × Tongues =>
        VectorCount.restrict N c.2) hEq
    · exact hnd
  exact h.configuration_count ks hlive hconfigs

/-- Quantitative rich first-revisit fork.  A same-direction revisit supplies
its actual simple-cycle period, bounded by the switch-simple exploration;
the crossed cases retain the manufactured reflector and its exact forced
return. -/
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

/-- Quantitative two-component reduction.  A live `3*N+2` prefix either
already has a lasso of size at most `5*N+1`, or it constructs both opposite
manufactured reflectors.  Each construction-and-return journey is bounded by
`2*N+1`; all groove and footprint-preservation data needed by the overlap
repair are retained. -/
theorem two_component_quantitative_outcome
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1) :
    EventuallyPeriodicWithin w start (5 * N + 1) ∨
      ∃ (A : ManufacturedReflector w start.1 e)
          (B : ManufacturedReflector w e start.1)
          (stateA stateB : Tongues)
          (firstTravel secondTravel : Nat),
        firstTravel ≤ 2 * N + 1 ∧
        secondTravel ≤ 2 * N + 1 ∧
        A.baseState = start.2 ∧
        stateA = A.activatedState ∧
        stepN w firstTravel start = some (e, stateA) ∧
        PathGrooves A.toSupported.paths stateA ∧
        B.baseState = stateA ∧
        stateB = B.activatedState ∧
        stepN w secondTravel (e, stateA) =
          some (start.1, stateB) ∧
        PathGrooves B.toSupported.paths stateB ∧
        (∀ j, j ∉ B.exploration.map passageSwitch →
          stateB j = stateA j) := by
  have hsplit :
      stepN w ((N + 1) + (2 * N + 1)) start = some finish := by
    have hlen : (N + 1) + (2 * N + 1) = 3 * N + 2 := by omega
    rw [hlen]
    exact hlive
  obtain ⟨firstFinish, hliveA, _⟩ := stepN_split_some hsplit
  rcases first_activated_quantitative_outcome hN hliveA hentry with
    hperiodicA | hreflectorA
  · exact Or.inl (hperiodicA.weaken (by omega))
  · obtain ⟨A, stateA, firstTravel, hfirstLe, hgroovesA,
      hbaseA, hactivatedA, hreachA, _hpreservesA⟩ := hreflectorA
    obtain ⟨secondFinish, hliveB⟩ :=
      stepN_live_after_reached hreachA hlive (by omega :
        firstTravel + (N + 1) ≤ 3 * N + 2)
    have hentryB : w.link start.1 = some e :=
      w.symm _ _ A.entryEdge
    rcases first_activated_quantitative_outcome
        (w := w) (N := N) (e := start.1)
        hN hliveB hentryB with hperiodicB | hreflectorB
    · left
      exact (hperiodicB.prepend hreachA).weaken (by omega)
    · right
      obtain ⟨B, stateB, secondTravel, hsecondLe, hgroovesB,
        hbaseB, hactivatedB, hreachB, hpreservesB⟩ := hreflectorB
      exact ⟨A, B, stateA, stateB, firstTravel, secondTravel,
        hfirstLe, hsecondLe, hbaseA, hactivatedA,
        hreachA, hgroovesA, hbaseB, hactivatedB,
        hreachB, hgroovesB, hpreservesB⟩

/-! ## Quantitative theta intersections -/

/-- A facing capture found on the new reflector's runway returns within the
sum of the old and new reflector travels. -/
theorem manufactured_runway_theta_capture_bounded
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    {before after : List Passage} {x : Nat}
    (hoccurs : B.runway = before ++ (A.mouth, x) :: after) :
    ∃ travel,
      travel ≤ A.toSupported.travel + B.toSupported.travel ∧
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
  have hAcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  have hlinked : LinkedPassages w
      (before ++ (A.mouth, x) :: after) := by
    rw [← hoccurs]
    exact B.runwayTrace.linked
  have hgrooved : PassagesGrooved state
      (before ++ (A.mouth, x) :: after) := by
    rw [← hoccurs]
    exact (pathGrooves_pair.mp hB).1
  have hsimpleRunway : SwitchSimple B.runway := by
    have hs := B.simple
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hsimple : SwitchSimple
      (before ++ (A.mouth, x) :: after) := by
    rwa [← hoccurs]
  cases before with
  | nil =>
      have htrace := B.runwayTrace
      rw [hoccurs] at htrace
      have hstart : e = A.mouth := htrace.head_arrive.1
      refine ⟨A.candy.length + 2 + A.runway.length, ?_, ?_⟩
      · simp [ManufacturedFlipReflector.toSupported]
        omega
      · simpa [hstart] using hAcapture
  | cons passage before =>
      rcases passage with ⟨r, y⟩
      have hprefixData := simple_grooved_prefix_to_occurrence
        hlinked hgrooved hsimple
      have htrace := B.runwayTrace
      rw [hoccurs] at htrace
      have hstart : e = r := htrace.head_arrive.1
      have hprefix :
          PhysicalTrace w (e, state) ((r, y) :: before)
            (A.mouth, state) := by
        simpa [hstart] using hprefixData.1
      have hforeign : ∀ passage ∈ (r, y) :: before,
          passageSwitch passage ≠ A.actionSwitch := by
        intro passage hp
        have hne := hprefixData.2 passage hp
        simpa [passageSwitch,
          ManufacturedFlipReflector.actionSwitch] using hne
      have hprefixLe : ((r, y) :: before).length ≤ B.runway.length := by
        rw [hoccurs]
        simp
      have hprefixLe' : before.length + 1 ≤ B.runway.length := by
        simpa using hprefixLe
      refine ⟨((r, y) :: before).length +
        (A.candy.length + 2 + A.runway.length), ?_, ?_⟩
      · simp [ManufacturedFlipReflector.toSupported]
        omega
      · exact theta_capture_after_unvisited_prefix
          hprefix hforeign hAcapture

/-- The forward-candy capture has the same sum-of-travels bound. -/
theorem manufactured_candy_forward_theta_capture_bounded
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.firstArm)
    {before after : List Passage} {x : Nat}
    (hoccurs : B.candy = before ++ (A.mouth, x) :: after) :
    ∃ travel,
      travel ≤ A.toSupported.travel + B.toSupported.travel ∧
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
  have hprefixData := B.forward_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hforeign : ∀ passage ∈
      B.runway ++ (B.mouth, B.firstArm) :: before,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hne
  have hcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  let pre := B.runway ++ (B.mouth, B.firstArm) :: before
  have hprefixLe : pre.length ≤ B.toSupported.travel := by
    change pre.length ≤ 2 * B.runway.length + B.candy.length + 2
    dsimp [pre]
    rw [hoccurs]
    simp
    omega
  refine ⟨pre.length +
    (A.candy.length + 2 + A.runway.length), ?_, ?_⟩
  · simp [ManufacturedFlipReflector.toSupported] at hprefixLe ⊢
    omega
  · exact theta_capture_after_unvisited_prefix
      hprefixData.1 hforeign hcapture

/-- The reverse-candy capture has the same sum-of-travels bound. -/
theorem manufactured_candy_reverse_theta_capture_bounded
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.secondArm)
    {before after : List Passage} {p : Nat}
    (hoccurs : B.candy = before ++ (p, A.mouth) :: after) :
    ∃ travel,
      travel ≤ A.toSupported.travel + B.toSupported.travel ∧
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
  have hprefixData := B.reverse_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hforeign : ∀ passage ∈
      B.runway ++
        (B.mouth, B.secondArm) :: reversePassages after,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hne
  have hcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  let pre := B.runway ++
    (B.mouth, B.secondArm) :: reversePassages after
  have hprefixLe : pre.length ≤ B.toSupported.travel := by
    change pre.length ≤ 2 * B.runway.length + B.candy.length + 2
    dsimp [pre]
    rw [hoccurs]
    simp [reversePassages_length]
    omega
  refine ⟨pre.length +
    (A.candy.length + 2 + A.runway.length), ?_, ?_⟩
  · simp [ManufacturedFlipReflector.toSupported] at hprefixLe ⊢
    omega
  · exact theta_capture_after_unvisited_prefix
      hprefixData.1 hforeign hcapture

/-- Quantitative orientation-free support fault.  The capture branch returns
within the sum of the two reflector travels; the other branch is the exact
self-repairing traversal of `B`. -/
theorem manufactured_support_fault_dichotomy_bounded
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      travel ≤ A.toSupported.travel + B.toSupported.travel ∧
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w B.toSupported.travel
        (e, flipAt state A.actionSwitch) =
          some (g, flipAt state B.actionSwitch) := by
  obtain ⟨path, hp, passage, hmem, hsw⟩ := hcontact
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · rcases passage with ⟨p, x⟩
    obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
    have hstem := B.runwayTrace.passage_stem_endpoint (p, x) hmem
    change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
    change p / 3 = A.actionSwitch at hsw
    have hmouth : A.mouth = 3 * A.actionSwitch := by
      have hs := A.mouth_is_stem
      unfold ManufacturedFlipReflector.actionSwitch
      omega
    rcases hstem with hpStem | hxStem
    · have hpMouth : p = A.mouth := by omega
      subst p
      left
      exact manufactured_runway_theta_capture_bounded
        A B state hA hB hoccurs
    · have hxMouth : x = A.mouth := by omega
      right
      simpa [ManufacturedFlipReflector.toSupported] using
        manufactured_runway_theta_repairs A B state hB
          (by simpa [hxMouth] using hoccurs)
  · rcases passage with ⟨p, x⟩
    obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
    have hstem := B.candyTrace.passage_stem_endpoint (p, x)
      (List.mem_cons_of_mem _ hmem)
    change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
    change p / 3 = A.actionSwitch at hsw
    have hmouth : A.mouth = 3 * A.actionSwitch := by
      have hs := A.mouth_is_stem
      unfold ManufacturedFlipReflector.actionSwitch
      omega
    rcases B.selected_arm state with hforward | hreverse
    · rcases hstem with hpStem | hxStem
      · have hpMouth : p = A.mouth := by omega
        subst p
        left
        exact manufactured_candy_forward_theta_capture_bounded
          A B state hA hB hforward hoccurs
      · have hxMouth : x = A.mouth := by omega
        right
        simpa [ManufacturedFlipReflector.toSupported] using
          manufactured_candy_forward_theta_repairs A B state
            hB hforward (by simpa [hxMouth] using hoccurs)
    · rcases hstem with hpStem | hxStem
      · have hpMouth : p = A.mouth := by omega
        right
        simpa [ManufacturedFlipReflector.toSupported] using
          manufactured_candy_reverse_theta_repairs A B state
            hB hreverse (by simpa [hpMouth] using hoccurs)
      · have hxMouth : x = A.mouth := by omega
        left
        exact manufactured_candy_reverse_theta_capture_bounded
          A B state hA hB hreverse
            (by simpa [hxMouth] using hoccurs)

/-- One theta macro-step has length at most `8*N`.  This is deliberately
generous: each reflector travels at most `2*N`, and a capture contributes at
most the sum of the two travels. -/
theorem manufactured_theta_half_bounded
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    ∃ travel, 0 < travel ∧ travel ≤ 8 * N ∧
      stepN w travel (g, state) =
        some (g, flipAt state B.actionSwitch) := by
  have hArun := (A.toSupported.run state hA).1
  have hBrun := (B.toSupported.run state hB).1
  change stepN w A.toSupported.travel (g, state) =
    some (e, flipAt state A.actionSwitch) at hArun
  change stepN w B.toSupported.travel (e, state) =
    some (g, flipAt state B.actionSwitch) at hBrun
  have hAt : A.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip A).travel_le_two_mul_switches hN
  have hBt : B.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip B).travel_le_two_mul_switches hN
  have hApos : 0 < A.toSupported.travel := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip A).travel_pos
  have hBpos : 0 < B.toSupported.travel := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip B).travel_pos
  rcases manufactured_support_fault_dichotomy_bounded
      A B state hA hB hcontact with hcapture | hrepair
  · obtain ⟨captureTravel, hcaptureLe, hcapture⟩ := hcapture
    refine ⟨A.toSupported.travel + captureTravel + B.toSupported.travel,
      by omega, by omega, ?_⟩
    have hlen :
        A.toSupported.travel + captureTravel + B.toSupported.travel =
          A.toSupported.travel +
            (captureTravel + B.toSupported.travel) := by omega
    rw [hlen, stepN_add, hArun]
    simp only [Option.bind_some]
    rw [stepN_add, hcapture]
    exact hBrun
  · refine ⟨A.toSupported.travel + B.toSupported.travel,
      by omega, by omega, ?_⟩
    rw [stepN_add, hArun]
    exact hrepair

/-- A one-sided flip/flip theta intersection closes within `16*N`. -/
theorem manufactured_one_sided_theta_within_sixteen
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch)
    (hBA : (LocalAction.flip B.actionSwitch).Avoids
      [A.runway, A.candy]) :
    EventuallyPeriodicWithin w (g, state) (16 * N) := by
  obtain ⟨firstTravel, hfirstPos, hfirstLe, hfirst⟩ :=
    manufactured_theta_half_bounded hN A B state hA hB hcontact
  have hA' : PathGrooves [A.runway, A.candy]
      (flipAt state B.actionSwitch) :=
    hA.after_avoiding_action hBA
  have hB' : PathGrooves [B.runway, B.candy]
      (flipAt state B.actionSwitch) :=
    (B.toSupported.run state hB).2
  obtain ⟨secondTravel, hsecondPos, hsecondLe, hsecond⟩ :=
    manufactured_theta_half_bounded hN A B
      (flipAt state B.actionSwitch) hA' hB' hcontact
  have hperiod : stepN w (firstTravel + secondTravel) (g, state) =
      some (g, state) := by
    rw [stepN_add, hfirst]
    simp only [Option.bind_some]
    rw [hsecond, flipAt_flipAt]
  exact eventuallyPeriodicWithin_of_period
    (by omega) (by omega) hperiod

/-- Mutual flip/flip intersection settles after one bounded theta half and
then repeats.  The complete lead-plus-period budget is at most `20*N`. -/
theorem manufactured_two_sided_theta_within_twenty
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hAB : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch)
    (hBA : ∃ path ∈ [A.runway, A.candy],
      ∃ passage ∈ path,
        passageSwitch passage = B.actionSwitch) :
    EventuallyPeriodicWithin w (g, state) (20 * N) := by
  obtain ⟨lead, hleadPos, hleadLe, hlead⟩ :=
    manufactured_theta_half_bounded hN A B state hA hB hAB
  have hAt : A.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip A).travel_le_two_mul_switches hN
  have hBt : B.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip B).travel_le_two_mul_switches hN
  have hApos : 0 < A.toSupported.travel := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip A).travel_pos
  have hBpos : 0 < B.toSupported.travel := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip B).travel_pos
  have hreverseFault := manufactured_support_fault_dichotomy_bounded
    B A state hB hA hBA
  have hforwardFault := manufactured_support_fault_dichotomy_bounded
    A B state hA hB hAB
  have hBrun := (B.toSupported.run state hB).1
  change stepN w B.toSupported.travel (e, state) =
    some (g, flipAt state B.actionSwitch) at hBrun
  rcases hreverseFault with hreverseCapture | hreverseRepair
  · obtain ⟨reverseTravel, hreverseLe, hreverseCapture⟩ :=
      hreverseCapture
    have hperiod : stepN w (reverseTravel + lead)
        (g, flipAt state B.actionSwitch) =
          some (g, flipAt state B.actionSwitch) := by
      rw [stepN_add, hreverseCapture]
      exact hlead
    exact ⟨lead, reverseTravel + lead,
      (g, flipAt state B.actionSwitch), by omega, by omega,
      hlead, hperiod⟩
  · rcases hforwardFault with hforwardCapture | hforwardRepair
    · obtain ⟨forwardTravel, hforwardLe, hforwardCapture⟩ :=
        hforwardCapture
      let period := A.toSupported.travel + forwardTravel +
        B.toSupported.travel
      have hperiod : stepN w period
          (g, flipAt state B.actionSwitch) =
            some (g, flipAt state B.actionSwitch) := by
        have hlen : period = A.toSupported.travel +
            (forwardTravel + B.toSupported.travel) := by
          dsimp [period]
          omega
        rw [hlen, stepN_add, hreverseRepair]
        simp only [Option.bind_some]
        rw [stepN_add, hforwardCapture]
        exact hBrun
      exact ⟨lead, period,
        (g, flipAt state B.actionSwitch), by
          dsimp [period]
          omega
        , by
          dsimp [period]
          omega
        , hlead, hperiod⟩
    · let period := A.toSupported.travel + B.toSupported.travel
      have hperiod : stepN w period
          (g, flipAt state B.actionSwitch) =
            some (g, flipAt state B.actionSwitch) := by
        dsimp [period]
        rw [stepN_add, hreverseRepair]
        exact hforwardRepair
      exact ⟨lead, period,
        (g, flipAt state B.actionSwitch), by
          dsimp [period]
          omega
        , by
          dsimp [period]
          omega
        , hlead, hperiod⟩

/-- Quantitative generic runway-fault engine.  In the facing branch the
unvisited prefix followed by the old-mouth capture costs at most the prefix
length plus the old reflector travel. -/
theorem runway_fault_dichotomy_general_bounded
    {w : Wiring} {g e total tailSteps : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    {base : Tongues} {runway : List Passage}
    {newFinish finish : Nat × Tongues}
    (htrace : PhysicalTrace w (e, base) runway newFinish)
    (hgrooved : PassagesGrooved state runway)
    (hsimple : SwitchSimple runway)
    (passage : Passage)
    {before after : List Passage}
    (hoccurs : runway = before ++ passage :: after)
    (hsw : passageSwitch passage = A.actionSwitch)
    (hdecomp : total = before.length + 1 + tailSteps)
    (hnormal : stepN w total (e, state) = some finish) :
    (∃ travel,
      travel ≤ before.length + A.toSupported.travel ∧
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w total (e, flipAt state A.actionSwitch) = some finish := by
  rcases passage with ⟨p, x⟩
  have hmem : (p, x) ∈ runway := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    htrace hoccurs hgrooved hsimple
  have hstem := htrace.passage_stem_endpoint (p, x) hmem
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  change p / 3 = A.actionSwitch at hsw
  have hmouth : A.mouth = 3 * A.actionSwitch := by
    have hs := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch
    omega
  rcases hstem with hp | hx
  · have hpMouth : p = A.mouth := by omega
    subst p
    left
    have hforeign : ∀ passage ∈ before,
        passageSwitch passage ≠ A.actionSwitch := by
      intro passage hp
      have hne := hprefixData.2 passage hp
      simpa [passageSwitch,
        ManufacturedFlipReflector.actionSwitch] using hne
    have hcapture := A.capture_from_mouth state
      (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
    refine ⟨before.length +
      (A.candy.length + 2 + A.runway.length), ?_, ?_⟩
    · simp [ManufacturedFlipReflector.toSupported]
      omega
    · exact theta_capture_after_unvisited_prefix
        hprefixData.1 hforeign hcapture
  · have hxMouth : x = A.mouth := by omega
    have htargetMem : (p, x) ∈ runway := hmem
    have hgrooveBack : arrive state x = (p, state) :=
      hgrooved (p, x) htargetMem
    have hforward : arrive state p = (x, state) :=
      groove_forward hgrooveBack
    have hpbranch : p % 3 ≠ 0 := by
      intro hpmod
      have hne := arrive_exit_ne state p
      rw [hforward] at hne
      apply hne
      omega
    have hforeign : ∀ prior ∈ before,
        passageSwitch prior ≠ A.actionSwitch := by
      intro prior hprior
      have hne := hprefixData.2 prior hprior
      simpa [passageSwitch, hsw] using hne
    obtain ⟨q, hlink⟩ : ∃ q, w.link x = some q := by
      cases after with
      | nil =>
          have htrace' := htrace
          rw [hoccurs] at htrace'
          obtain ⟨middle, hbeforeTrace, htargetTrace⟩ :=
            htrace'.split_append
          have hlast := htargetTrace.last_link
          exact ⟨newFinish.1,
            by simpa [lastPassageExit] using hlast⟩
      | cons next rest =>
          rcases next with ⟨q, y⟩
          have hlinked : LinkedPassages w
              (before ++ (p, x) :: (q, y) :: rest) := by
            rw [← hoccurs]
            exact htrace.linked
          exact ⟨q, linked_after_occurrence hlinked⟩
    have htarget : PhysicalTrace w (p, state)
        [(p, x)] (q, state) :=
      PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
    have hprefixTarget := hprefixData.1.append htarget
    have hsuffix : stepN w tailSteps (q, state) = some finish := by
      have hprefixLen :
          (before ++ [(p, x)]).length = before.length + 1 := by simp
      apply suffix_after_physical_prefix hprefixTarget
      · simpa [hprefixLen] using hdecomp
      · exact hnormal
    right
    have hrepair := flipped_prefix_trailing_then hprefixData.1 hforeign
      hsw hpbranch hforward hlink hsuffix
    rwa [← hdecomp] at hrepair

/-- Quantitative support-fault dichotomy for a flip reflector followed by a
degenerate identity reflector. -/
theorem manufactured_stay_support_fault_dichotomy_bounded
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedStayReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, [(B.mouth, B.arm)]] state)
    (hcontact : ∃ path ∈ [B.runway, [(B.mouth, B.arm)]],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      travel ≤ A.toSupported.travel + B.toSupported.travel ∧
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w B.toSupported.travel
        (e, flipAt state A.actionSwitch) = some (g, state) := by
  have hnormal := (B.toSupported.run state hB).1
  obtain ⟨path, hp, passage, hmem, hsw⟩ := hcontact
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
    have hsimpleRunway : SwitchSimple B.runway := by
      have hs := B.simple
      unfold SwitchSimple at hs ⊢
      simp only [List.map_append] at hs
      exact (List.nodup_append.mp hs).1
    have hRlen : B.runway.length =
        before.length + 1 + after.length := by
      rw [hoccurs]
      simp
      omega
    let tailSteps := after.length + 2 + B.runway.length
    have hdecomp : B.toSupported.travel =
        before.length + 1 + tailSteps := by
      change 2 * B.runway.length + 2 =
        before.length + 1 + tailSteps
      dsimp [tailSteps]
      omega
    rcases runway_fault_dichotomy_general_bounded
        (total := B.toSupported.travel) (tailSteps := tailSteps)
        A state hA B.runwayTrace (pathGrooves_pair.mp hB).1
        hsimpleRunway passage hoccurs hsw hdecomp hnormal with
      hcapture | hrepair
    · left
      obtain ⟨travel, htravel, hstep⟩ := hcapture
      refine ⟨travel, ?_, hstep⟩
      have hbeforeLe : before.length ≤ B.toSupported.travel := by
        change before.length ≤ 2 * B.runway.length + 2
        omega
      omega
    · exact Or.inr hrepair
  · simp only [List.mem_singleton] at hmem
    subst passage
    let route := B.runway ++ [(B.mouth, B.arm)]
    have hrun := B.runway_trace state (pathGrooves_pair.mp hB).1
    have hgrooveBack := passagesGrooved_singleton.mp
      (pathGrooves_pair.mp hB).2
    have hforward := groove_forward hgrooveBack
    have htarget : PhysicalTrace w (B.mouth, state)
        [(B.mouth, B.arm)] (B.arm, state) :=
      PhysicalTrace.cons hforward B.selfLink (PhysicalTrace.nil _)
    have hrouteTrace := hrun.append htarget
    have hrouteGrooved := hrouteTrace.grooved_of_switchSimple B.simple
    have hoccurs : route =
        B.runway ++ (B.mouth, B.arm) :: [] := by rfl
    have hdecomp : B.toSupported.travel =
        B.runway.length + 1 + (B.runway.length + 1) := by
      simp [ManufacturedStayReflector.toSupported]
      omega
    rcases runway_fault_dichotomy_general_bounded
        (total := B.toSupported.travel)
        (tailSteps := B.runway.length + 1)
        A state hA hrouteTrace hrouteGrooved B.simple
        (B.mouth, B.arm) hoccurs hsw hdecomp hnormal with
      hcapture | hrepair
    · left
      obtain ⟨travel, htravel, hstep⟩ := hcapture
      refine ⟨travel, ?_, hstep⟩
      have hrunwayLe : B.runway.length ≤ B.toSupported.travel := by
        change B.runway.length ≤ 2 * B.runway.length + 2
        omega
      omega
    · exact Or.inr hrepair

/-- A flip reflector followed by an intersecting identity reflector closes
within `8*N`. -/
theorem manufactured_flip_then_stay_within_eight
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedStayReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, [(B.mouth, B.arm)]] state)
    (hcontact : ∃ path ∈ [B.runway, [(B.mouth, B.arm)]],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    EventuallyPeriodicWithin w (g, state) (8 * N) := by
  have hArun := (A.toSupported.run state hA).1
  change stepN w A.toSupported.travel (g, state) =
    some (e, flipAt state A.actionSwitch) at hArun
  have hBrun := (B.toSupported.run state hB).1
  have hAt : A.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip A).travel_le_two_mul_switches hN
  have hBt : B.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.stay B).travel_le_two_mul_switches hN
  have hApos : 0 < A.toSupported.travel := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip A).travel_pos
  have hBpos : 0 < B.toSupported.travel := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.stay B).travel_pos
  rcases manufactured_stay_support_fault_dichotomy_bounded
      A B state hA hB hcontact with hcapture | hrepair
  · obtain ⟨captureTravel, hcaptureLe, hcapture⟩ := hcapture
    let period := A.toSupported.travel + captureTravel +
      B.toSupported.travel
    have hperiod : stepN w period (g, state) = some (g, state) := by
      have hlen : period = A.toSupported.travel +
          (captureTravel + B.toSupported.travel) := by
        dsimp [period]
        omega
      rw [hlen, stepN_add, hArun]
      simp only [Option.bind_some]
      rw [stepN_add, hcapture]
      exact hBrun
    apply eventuallyPeriodicWithin_of_period (period := period)
    · dsimp [period]
      omega
    · dsimp [period]
      omega
    · exact hperiod
  · let period := A.toSupported.travel + B.toSupported.travel
    have hperiod : stepN w period (g, state) = some (g, state) := by
      dsimp [period]
      rw [stepN_add, hArun]
      exact hrepair
    apply eventuallyPeriodicWithin_of_period (period := period)
    · dsimp [period]
      omega
    · dsimp [period]
      omega
    · exact hperiod

/-- The explicit four-corner period of two disjoint manufactured reflectors
fits in `8*N` physical train steps. -/
theorem manufactured_pair_within_eight_mul_switches_of_avoids
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths) :
    EventuallyPeriodicWithin w (g, state) (8 * N) := by
  let period := 2 * (A.toSupported.travel + B.toSupported.travel)
  have hperiod : stepN w period (g, state) = some (g, state) := by
    simpa [period] using manufactured_pair_period_of_avoids
      A B state hA hB hAB hBA
  have hAtravel := A.travel_le_two_mul_switches hN
  have hBtravel := B.travel_le_two_mul_switches hN
  have hposA := A.travel_pos
  have hposB := B.travel_pos
  apply eventuallyPeriodicWithin_of_period (period := period)
  · dsimp [period]
    omega
  · dsimp [period]
    omega
  · exact hperiod

/-- **Complete quantitative theta theorem.**  Any two opposite manufactured
reflectors with both supports grooved have a raw configuration lasso whose
lead plus period is at most `20*N`.  This covers identity/flip mixtures,
one-sided intersections, and mutual intersections; it is the quantitative
counterpart of `manufactured_pair_eventually_periodic`. -/
theorem manufactured_pair_within_twenty_mul_switches
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state) :
    EventuallyPeriodicWithin w (g, state) (20 * N) := by
  classical
  cases A with
  | stay SA =>
      cases B with
      | stay SB =>
          exact (manufactured_pair_within_eight_mul_switches_of_avoids
            hN (.stay SA) (.stay SB) state hA hB
              (by trivial) (by trivial)).weaken (by omega)
      | flip FB =>
          change PathGrooves
            [SA.runway, [(SA.mouth, SA.arm)]] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
              [SA.runway, [(SA.mouth, SA.arm)]]
          · exact (manufactured_pair_within_eight_mul_switches_of_avoids
              hN (.stay SA) (.flip FB) state hA hB
                (by trivial) hBA).weaken (by omega)
          · have hcontact := contact_of_not_avoids_flip hBA
            have hlead := (SA.toSupported.run state hA).1
            change stepN w SA.toSupported.travel (g, state) =
              some (e, state) at hlead
            have hlocal := manufactured_flip_then_stay_within_eight
              hN FB SA state hB hA hcontact
            have htravel : SA.toSupported.travel ≤ 2 * N := by
              simpa [ManufacturedReflector.toSupported] using
                (ManufacturedReflector.stay SA).travel_le_two_mul_switches hN
            exact (hlocal.prepend hlead).weaken (by omega)
  | flip FA =>
      cases B with
      | stay SB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves
            [SB.runway, [(SB.mouth, SB.arm)]] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [SB.runway, [(SB.mouth, SB.arm)]]
          · exact (manufactured_pair_within_eight_mul_switches_of_avoids
              hN (.flip FA) (.stay SB) state hA hB
                hAB (by trivial)).weaken (by omega)
          · have hcontact := contact_of_not_avoids_flip hAB
            exact (manufactured_flip_then_stay_within_eight
              hN FA SB state hA hB hcontact).weaken (by omega)
      | flip FB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [FB.runway, FB.candy]
          · by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
                [FA.runway, FA.candy]
            · exact (manufactured_pair_within_eight_mul_switches_of_avoids
                hN (.flip FA) (.flip FB) state hA hB hAB hBA).weaken
                  (by omega)
            · have hcontactBA := contact_of_not_avoids_flip hBA
              have hArun := (FA.toSupported.run state hA)
              have hA' : PathGrooves [FA.runway, FA.candy]
                  (flipAt state FA.actionSwitch) := hArun.2
              have hB' : PathGrooves [FB.runway, FB.candy]
                  (flipAt state FA.actionSwitch) :=
                hB.after_avoiding_action hAB
              have hlocal := manufactured_one_sided_theta_within_sixteen
                hN FB FA (flipAt state FA.actionSwitch)
                  hB' hA' hcontactBA hAB
              have hlead := hArun.1
              change stepN w FA.toSupported.travel (g, state) =
                some (e, flipAt state FA.actionSwitch) at hlead
              have htravel : FA.toSupported.travel ≤ 2 * N := by
                simpa [ManufacturedReflector.toSupported] using
                  (ManufacturedReflector.flip FA).travel_le_two_mul_switches hN
              exact (hlocal.prepend hlead).weaken (by omega)
          · have hcontactAB := contact_of_not_avoids_flip hAB
            by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
                [FA.runway, FA.candy]
            · exact (manufactured_one_sided_theta_within_sixteen
                hN FA FB state hA hB hcontactAB hBA).weaken (by omega)
            · have hcontactBA := contact_of_not_avoids_flip hBA
              exact manufactured_two_sided_theta_within_twenty
                hN FA FB state hA hB hcontactAB hcontactBA

/-- Quantitative global reduction through the common-support case.  A live
`3*N+2` prefix has a lasso of size `24*N+2` unless the second construction
has concretely damaged the first reflector's reusable support. -/
theorem long_run_within_or_damaged_pair
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1) :
    EventuallyPeriodicWithin w start (24 * N + 2) ∨
      ∃ (A : ManufacturedReflector w start.1 e)
          (B : ManufacturedReflector w e start.1)
          (stateA stateB : Tongues)
          (firstTravel secondTravel : Nat),
        firstTravel ≤ 2 * N + 1 ∧
        secondTravel ≤ 2 * N + 1 ∧
        A.baseState = start.2 ∧
        stateA = A.activatedState ∧
        stepN w firstTravel start = some (e, stateA) ∧
        PathGrooves A.toSupported.paths stateA ∧
        B.baseState = stateA ∧
        stateB = B.activatedState ∧
        stepN w secondTravel (e, stateA) =
          some (start.1, stateB) ∧
        PathGrooves B.toSupported.paths stateB ∧
        (∀ j, j ∉ B.exploration.map passageSwitch →
          stateB j = stateA j) ∧
        ¬ PathGrooves A.toSupported.paths stateB ∧
        ¬ A.SupportAvoidsExploration B := by
  rcases two_component_quantitative_outcome hN hlive hentry with
    hperiodic | hpair
  · exact Or.inl (hperiodic.weaken (by omega))
  · obtain ⟨A, B, stateA, stateB, firstTravel, secondTravel,
      hfirstLe, hsecondLe, hbaseA, hactivatedA,
      hreachA, hgroovesA, hbaseB, hactivatedB,
      hreachB, hgroovesB, hpreservesB⟩ := hpair
    by_cases hgroovesAFinal :
        PathGrooves A.toSupported.paths stateB
    · left
      have hlocal := manufactured_pair_within_twenty_mul_switches
        hN A B stateB hgroovesAFinal hgroovesB
      exact ((hlocal.prepend hreachB).prepend hreachA).weaken (by omega)
    · right
      have hcontact : ¬ A.SupportAvoidsExploration B := by
        intro havoid
        apply hgroovesAFinal
        exact A.support_grooves_of_avoiding_exploration
          B stateA stateB hgroovesA hpreservesB havoid
      exact ⟨A, B, stateA, stateB, firstTravel, secondTravel,
        hfirstLe, hsecondLe, hbaseA, hactivatedA,
        hreachA, hgroovesA, hbaseB, hactivatedB,
        hreachB, hgroovesB, hpreservesB,
        hgroovesAFinal, hcontact⟩

/-- Quantitative complete-repair branch.  Repairing `A` costs at most its
`2*N` selected route; the reached endpoint lies on the complete pair's
`20*N` lasso. -/
theorem ManufacturedReflector.completed_route_with_pair_support_within
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (base state finalState : Tongues)
    (hbasePaths : PathGrooves A.toSupported.paths base)
    (hrepair : PhysicalTrace w (g, state)
      (A.orientedRoute state)
      (A.orientedFinish state, finalState))
    (hAfinal : PathGrooves A.toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState) :
    EventuallyPeriodicWithin w (g, state) (22 * N) := by
  obtain ⟨reference, _hreferencePaths, hroute, hfinish,
      hreferenceGrooved, _hguard⟩ :=
    A.current_route_reference base state hbasePaths
  have hfinalGrooved :
      PassagesGrooved finalState (A.orientedRoute state) :=
    hrepair.grooved_of_switchSimple (A.orientedRoute_simple state)
  have hfinalReferenceGrooved :
      PassagesGrooved finalState (A.orientedRoute reference) := by
    rw [hroute]
    exact hfinalGrooved
  have hreferenceGrooved' :
      PassagesGrooved reference (A.orientedRoute reference) := by
    rw [hroute]
    exact hreferenceGrooved
  have horiented := A.oriented_data_eq_of_route_grooved
    reference finalState hreferenceGrooved' hfinalReferenceGrooved
  have hrouteFinal := A.orientedRoute_trace finalState hAfinal
  have hrouteFinal' : PhysicalTrace w (g, finalState)
      (A.orientedRoute state)
      (A.orientedFinish state, finalState) := by
    rw [horiented.1, horiented.2, hroute, hfinish] at hrouteFinal
    exact hrouteFinal
  have hpair := manufactured_pair_within_twenty_mul_switches
    hN A B finalState hAfinal hBfinal
  have hend := hpair.forward hrouteFinal'.sound
  have hrouteLe : (A.orientedRoute state).length ≤ 2 * N :=
    Nat.le_trans (A.orientedRoute_length_le_travel state)
      (A.travel_le_two_mul_switches hN)
  exact (hend.prepend hrepair.sound).weaken (by omega)

/-- The no-change forward merge has a lasso of size at most `12*N`.
The selected-route prefix and reverse-candy suffix each cost at most `2*N`;
an optional capture costs at most another `4*N`. -/
theorem ManufacturedReflector.FacingForwardMerge.within_twelve
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.FacingForwardMerge B) :
    EventuallyPeriodicWithin w (g, B.activatedState) (12 * N) := by
  obtain ⟨R, before, p, x, after, contact, fresh,
      hB, hrouteSplit, hprefix, hpaths, _hp, _harrive,
      _hfreshNe, hcandyMem, hsecond, _hforward⟩ :=
    hmerge.flip_candy
  subst B
  obtain ⟨candyBefore, candyAfter, hcandySplit⟩ :=
    List.append_of_mem hcandyMem
  let alternate := flipAt contact R.actionSwitch
  obtain ⟨tailTravel, htailPositive, htailLe, htailContact,
      htailAlternate⟩ :=
    R.reverse_candy_suffix_absorbs contact hpaths hsecond hcandySplit
  have hrouteSimple :=
    A.orientedRoute_simple
      (ManufacturedReflector.flip R).activatedState
  rw [hrouteSplit] at hrouteSimple
  have hbeforeSimple : SwitchSimple before := by
    unfold SwitchSimple at hrouteSimple ⊢
    simp only [List.map_append, List.map_cons] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).1
  have hbeforeGrooved : PassagesGrooved contact before :=
    hprefix.grooved_of_switchSimple hbeforeSimple
  have hprefixContact :
      PhysicalTrace w (g, contact) before (p, contact) :=
    hprefix.replay_grooved contact hbeforeGrooved
  have hbeforeRoute : before.length ≤
      (A.orientedRoute
        (ManufacturedReflector.flip R).activatedState).length := by
    rw [hrouteSplit]
    simp
  have hbeforeLe : before.length ≤ 2 * N :=
    Nat.le_trans hbeforeRoute
      (Nat.le_trans
        (A.orientedRoute_length_le_travel
          (ManufacturedReflector.flip R).activatedState)
        (A.travel_le_two_mul_switches hN))
  have hRtravel : R.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip R).travel_le_two_mul_switches hN
  have htailBound : tailTravel ≤ 2 * N :=
    Nat.le_trans htailLe hRtravel
  let loopSteps := before.length + tailTravel
  have hloopLe : loopSteps ≤ 4 * N := by
    dsimp [loopSteps]
    omega
  have hlead :
      stepN w loopSteps
        (g, (ManufacturedReflector.flip R).activatedState) =
          some (g, alternate) := by
    dsimp [loopSteps]
    rw [stepN_add, hprefix.sound]
    exact htailContact
  have hcontactToAlternate :
      stepN w loopSteps (g, contact) = some (g, alternate) := by
    dsimp [loopSteps]
    rw [stepN_add, hprefixContact.sound]
    exact htailContact
  have hloopPositive : 0 < loopSteps := by
    dsimp [loopSteps]
    omega
  by_cases htouch : ∃ passage ∈ before,
      passageSwitch passage = R.actionSwitch
  · obtain ⟨passage, hpassage, hswitch⟩ := htouch
    obtain ⟨prior, later, hbeforeSplit⟩ :=
      List.append_of_mem hpassage
    have hdecomp : before.length =
        prior.length + 1 + later.length := by
      rw [hbeforeSplit]
      simp only [List.length_append, List.length_cons]
      omega
    have hnormal :
        stepN w before.length (g, contact) = some (p, contact) :=
      hprefixContact.sound
    rcases runway_fault_dichotomy_general_bounded
        (total := before.length) (tailSteps := later.length)
        R contact hpaths hprefixContact hbeforeGrooved
        hbeforeSimple passage hbeforeSplit hswitch hdecomp hnormal with
      hcapture | hrepair
    · obtain ⟨captureTravel, hcaptureLe, hcapture⟩ := hcapture
      have hpriorLe : prior.length ≤ before.length := by
        omega
      have hcaptureBound : captureTravel ≤ 4 * N := by
        omega
      have hperiod :
          stepN w (captureTravel + loopSteps) (g, alternate) =
            some (g, alternate) := by
        rw [stepN_add, hcapture]
        exact hcontactToAlternate
      exact ⟨loopSteps, captureTravel + loopSteps,
        (g, alternate), by omega, by omega, hlead, hperiod⟩
    · have hperiod :
          stepN w loopSteps (g, alternate) = some (g, alternate) := by
        dsimp [loopSteps]
        rw [stepN_add, hrepair]
        exact htailContact
      exact ⟨loopSteps, loopSteps, (g, alternate),
        hloopPositive, by omega, hlead, hperiod⟩
  · have hforeign : ∀ passage ∈ before,
        passageSwitch passage ≠ R.actionSwitch := by
      intro passage hpassage hswitch
      exact htouch ⟨passage, hpassage, hswitch⟩
    have hprefixAlternate :
        PhysicalTrace w (g, alternate) before (p, alternate) :=
      hprefixContact.flip_unvisited hforeign
    have hperiod :
        stepN w loopSteps (g, alternate) = some (g, alternate) := by
      dsimp [loopSteps]
      rw [stepN_add, hprefixAlternate.sound]
      exact htailAlternate
    exact ⟨loopSteps, loopSteps, (g, alternate),
      hloopPositive, by omega, hlead, hperiod⟩

/-- A state-changing forward splice into an identity reflector has a lasso
of size at most `16*N`.  The manufactured lobe contains one prefix of each
selected route, hence has travel at most `4*N`; a runway contact pairs it
with a retained reflector of travel at most `2*N`, while a core contact is
just two traversals of that lobe. -/
theorem ManufacturedReflector.ChangedForwardMerge.stay_within_sixteen
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedStayReflector w e g}
    (hmerge : A.ChangedForwardMerge (.stay R)) :
    EventuallyPeriodicWithin w
      (g, (ManufacturedReflector.stay R).activatedState) (16 * N) := by
  obtain ⟨entry, mouth, _return, outside, oldPrefix, _oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      _hrouteSplit, _hOldTail, _hApproach, _hApproachGrooved,
      _hApproachForeign, hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, _harms, _hfullGrooved, _hfullTrace, _hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete, hleadLen, htailLen, happroachLe⟩ :=
    hmerge.spliced_lobe_reflector
  have hAtravel : A.toSupported.travel ≤ 2 * N :=
    A.travel_le_two_mul_switches hN
  have hRtravel :
      (ManufacturedReflector.stay R).toSupported.travel ≤ 2 * N :=
    (ManufacturedReflector.stay R).travel_le_two_mul_switches hN
  have hleadLe : leadSteps ≤ 2 * N := by
    rw [hleadLen]
    omega
  have holdPrefixLe : oldPrefix.length + 1 ≤ 2 * N := by
    omega
  have hcandyLen : candy.length = oldPrefix.length + approach.length := by
    rw [hCandyEq]
    simp [reversePassages_length]
  have hlobeLe : candy.length + 2 ≤ 4 * N := by
    omega
  have hCandyFlip :
      PassagesGrooved (flipAt state (mouth / 3)) candy :=
    grooved_after_flip_other hCandy hCandyForeign
  have hOldRoute :=
    (ManufacturedReflector.stay R).orientedRoute_trace state hRpaths
  have hOldSimple :=
    (ManufacturedReflector.stay R).orientedRoute_simple state
  have hOldGrooved := hOldRoute.grooved_of_switchSimple hOldSimple
  have hOldForward : arrive state entry = (mouth, state) :=
    groove_forward (hOldGrooved (entry, mouth) horiented)
  have hentryMouthSwitch : entry / 3 = mouth / 3 := by
    have hswitch := arrive_exit_switch state entry
    rw [hOldForward] at hswitch
    exact hswitch.symm
  change (entry, mouth) ∈
      R.runway ++ [(R.mouth, R.arm)] at horiented
  rcases List.mem_append.mp horiented with hrunway | hcore
  · obtain ⟨before, after, hsplit⟩ :=
      List.append_of_mem hrunway
    obtain ⟨C, hCpaths, hAvoid⟩ :=
      R.suffix_after_runway_passage state hRpaths
        hsplit hmouthLink
    have hAvoid' :
        (LocalAction.flip (mouth / 3)).Avoids
          C.toSupported.paths := by
      simpa [hentryMouthSwitch] using hAvoid
    let L : SupportedReflector w mouth outside := {
      travel := candy.length + 2
      paths := [candy]
      action := .flip (mouth / 3)
      run := by
        intro current hpaths
        have hgrooved : PassagesGrooved current candy :=
          hpaths candy (by simp)
        obtain ⟨hstep, hnext⟩ := hLobe current hgrooved
        constructor
        · exact hstep
        · intro path hpath
          simp only [List.mem_singleton] at hpath
          subst path
          exact hnext
    }
    have hCflip : PathGrooves C.toSupported.paths
        (flipAt state (mouth / 3)) :=
      hCpaths.after_avoiding_action hAvoid'
    have hLflip : PathGrooves L.paths
        (flipAt state (mouth / 3)) := by
      intro path hpath
      simp only [L, List.mem_singleton] at hpath
      subst path
      exact hCandyFlip
    have hperiod := C.toSupported.paired_period L
      (by change True; trivial) hAvoid'
      (flipAt state (mouth / 3)) hCflip hLflip
    have hpositive :
        0 < 2 * (C.toSupported.travel + L.travel) := by
      dsimp [L]
      omega
    have hCtravel : C.toSupported.travel ≤ 2 * N := by
      simpa [ManufacturedReflector.toSupported] using
        (ManufacturedReflector.stay C).travel_le_two_mul_switches hN
    have hLtravel : L.travel ≤ 4 * N := by
      dsimp [L]
      exact hlobeLe
    exact ⟨leadSteps, 2 * (C.toSupported.travel + L.travel),
      (outside, flipAt state (mouth / 3)), hpositive, by omega,
      hreach, hperiod⟩
  · simp only [List.mem_singleton] at hcore
    have hentryEq : entry = R.mouth :=
      congrArg Prod.fst hcore
    have hmouthEq : mouth = R.arm :=
      congrArg Prod.snd hcore
    subst entry
    subst mouth
    have houtsideEq : outside = R.arm := by
      rw [R.selfLink] at hmouthLink
      exact (Option.some.inj hmouthLink).symm
    subst outside
    have hfirst :=
      (hLobe (flipAt state (R.arm / 3)) hCandyFlip).1
    have hfirst' := hfirst
    change stepN w (candy.length + 2)
        (R.arm, flipAt state (R.arm / 3)) =
          some (R.arm,
            flipAt (flipAt state (R.arm / 3)) (R.arm / 3)) at hfirst'
    rw [flipAt_flipAt state (R.arm / 3)] at hfirst'
    have hsecond := (hLobe state hCandy).1
    have hperiod :
        stepN w ((candy.length + 2) + (candy.length + 2))
          (R.arm, flipAt state (R.arm / 3)) =
            some (R.arm, flipAt state (R.arm / 3)) := by
      rw [stepN_add, hfirst']
      exact hsecond
    have hpositive :
        0 < (candy.length + 2) + (candy.length + 2) := by
      omega
    exact ⟨leadSteps,
      (candy.length + 2) + (candy.length + 2),
      (R.arm, flipAt state (R.arm / 3)), hpositive,
      by omega, hreach, hperiod⟩

/-- Quantitative arbitrary-lobe theta period.  Each orientation costs at most
twice the sum of the retained reflector travel and the spliced-lobe travel;
the two orientations therefore close within four times that sum. -/
theorem manufactured_flip_arbitrary_lobe_within
    {w : Wiring} {outside mouth entry returnPort : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    (hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
      C.toSupported.paths)
    {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch) :
    EventuallyPeriodicWithin w
      (outside, flipAt state (mouth / 3))
      (4 * (C.toSupported.travel + (candy.length + 2))) := by
  have hCandy : PassagesGrooved state candy := by
    intro passage hpassage
    exact hgrooved passage (List.mem_cons_of_mem _ hpassage)
  have hnormal := (hLobe state hCandy).1
  obtain ⟨forwardTravel, hforwardPositive, hforwardLe, hforward⟩ :=
    manufactured_flip_arbitrary_lobe_theta_half C state hCpaths
      hgrooved htrace hnormal hcontact
  have hCflip : PathGrooves C.toSupported.paths
      (flipAt state (mouth / 3)) :=
    hCpaths.after_avoiding_action hNewAvoidsC
  have hCandyFlip :
      PassagesGrooved (flipAt state (mouth / 3)) candy :=
    grooved_after_flip_other hCandy hCandyForeign
  obtain ⟨hreverseTrace, hreverseGrooved, _hrestore⟩ :=
    arbitrary_lobe_reverse_trace hentryBranch hentrySwitch
      hgrooved htrace hcrossed hCandyForeign
  have hmap :
      (reversePassages candy).map passageSwitch =
        (candy.map passageSwitch).reverse := by
    cases htrace with
    | @cons _ _ _ _ _ _ _ _ _ tail =>
        exact map_passageSwitch_reversePassages tail
  have hcontactReverse : ∃ passage ∈ reversePassages candy,
      passageSwitch passage = C.actionSwitch := by
    obtain ⟨old, hold, holdSwitch⟩ := hcontact
    have hkeyMem : C.actionSwitch ∈ candy.map passageSwitch :=
      List.mem_map.mpr ⟨old, hold, holdSwitch⟩
    have hreverseKey : C.actionSwitch ∈
        (reversePassages candy).map passageSwitch := by
      rw [hmap]
      exact List.mem_reverse.mpr hkeyMem
    obtain ⟨passage, hpassage, hswitch⟩ :=
      List.mem_map.mp hreverseKey
    exact ⟨passage, hpassage, hswitch⟩
  have hnormalReverse :
      stepN w ((reversePassages candy).length + 2)
        (mouth, flipAt state (mouth / 3)) =
          some (outside,
            flipAt (flipAt state (mouth / 3)) (mouth / 3)) := by
    have hrun :=
      (hLobe (flipAt state (mouth / 3)) hCandyFlip).1
    simpa [reversePassages_length] using hrun
  obtain ⟨reverseTravel, hreversePositive, hreverseLe, hreverse⟩ :=
    manufactured_flip_arbitrary_lobe_theta_half C
      (flipAt state (mouth / 3)) hCflip hreverseGrooved
      hreverseTrace hnormalReverse hcontactReverse
  have hreverse' : stepN w reverseTravel
      (outside, flipAt state (mouth / 3)) =
        some (outside, state) := by
    change stepN w reverseTravel
        (outside, flipAt state (mouth / 3)) =
      some (outside,
        flipAt (flipAt state (mouth / 3)) (mouth / 3)) at hreverse
    rw [flipAt_flipAt state (mouth / 3)] at hreverse
    exact hreverse
  have hperiod : stepN w (reverseTravel + forwardTravel)
      (outside, flipAt state (mouth / 3)) =
        some (outside, flipAt state (mouth / 3)) := by
    rw [stepN_add, hreverse']
    exact hforward
  have hreverseLe' : reverseTravel ≤
      2 * (C.toSupported.travel + (candy.length + 2)) := by
    simpa [reversePassages_length] using hreverseLe
  exact eventuallyPeriodicWithin_of_period (by omega) (by omega) hperiod

/-- A changed-forward splice through the runway of an old flip reflector
closes within `24*N`, provided the newly spliced lobe has travel at most
`4*N` (the bound supplied by the two selected-route prefixes). -/
theorem manufactured_flip_runway_splice_within_twenty_four
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hRpaths : PathGrooves R.toSupported.paths state)
    {entry mouth returnPort outside : Nat} {candy : List Passage}
    (hrunway : (entry, mouth) ∈ R.runway)
    (hmouthLink : w.link mouth = some outside)
    (hentryBranch : entry % 3 ≠ 0)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandy : PassagesGrooved state candy)
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hlobeLe : candy.length + 2 ≤ 4 * N) :
    EventuallyPeriodicWithin w
      (outside, flipAt state (mouth / 3)) (24 * N) := by
  obtain ⟨before, after, hsplit⟩ := List.append_of_mem hrunway
  obtain ⟨C, _hCAction, _hActionsNe, hCpaths, hNewAvoidsC⟩ :=
    R.suffix_after_runway_passage state hRpaths
      hsplit hmouthLink
  have hentrySwitch : entry / 3 = mouth / 3 := by
    have hheadGroove : arrive state entry = (mouth, state) :=
      hgrooved (mouth, entry) List.mem_cons_self
    have hswitch := arrive_exit_switch state entry
    rw [hheadGroove] at hswitch
    exact hswitch.symm
  have hNewAvoidsC' :
      (LocalAction.flip (mouth / 3)).Avoids
        C.toSupported.paths := by
    simpa [hentrySwitch] using hNewAvoidsC
  have hCtravel : C.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip C).travel_le_two_mul_switches hN
  by_cases hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch
  · exact (manufactured_flip_arbitrary_lobe_within C state hCpaths
      hNewAvoidsC' hentryBranch hentrySwitch hgrooved htrace
      hcrossed hCandyForeign hLobe hcontact).weaken (by omega)
  · let L : SupportedReflector w mouth outside := {
      travel := candy.length + 2
      paths := [candy]
      action := .flip (mouth / 3)
      run := by
        intro current hpaths
        have hCandyCurrent : PassagesGrooved current candy :=
          hpaths candy (by simp)
        obtain ⟨hstep, hnext⟩ := hLobe current hCandyCurrent
        constructor
        · exact hstep
        · intro path hpath
          simp only [List.mem_singleton] at hpath
          subst path
          exact hnext
    }
    have hOldAvoidsL : C.toSupported.action.Avoids L.paths := by
      change (LocalAction.flip C.actionSwitch).Avoids [candy]
      intro path hpath passage hpassage
      simp only [List.mem_singleton] at hpath
      subst path
      intro hEq
      exact hcontact ⟨passage, hpassage, hEq⟩
    have hCflip : PathGrooves C.toSupported.paths
        (flipAt state (mouth / 3)) :=
      hCpaths.after_avoiding_action hNewAvoidsC'
    have hCandyFlip :
        PassagesGrooved (flipAt state (mouth / 3)) candy :=
      grooved_after_flip_other hCandy hCandyForeign
    have hLflip : PathGrooves L.paths
        (flipAt state (mouth / 3)) := by
      intro path hpath
      simp only [L, List.mem_singleton] at hpath
      subst path
      exact hCandyFlip
    have hperiod := C.toSupported.paired_period L
      hOldAvoidsL hNewAvoidsC'
      (flipAt state (mouth / 3)) hCflip hLflip
    have hpositive :
        0 < 2 * (C.toSupported.travel + L.travel) := by
      dsimp [L]
      omega
    have hLtravel : L.travel ≤ 4 * N := by
      dsimp [L]
      exact hlobeLe
    exact eventuallyPeriodicWithin_of_period hpositive (by omega) hperiod

/-- Every state-changing forward merge into a manufactured flip reflector
has a lasso of size at most `26*N`.  Runway contacts use the bounded
arbitrary-lobe theta theorem; candy contacts use the exact cycle length
exported by the two splice lemmas. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_within_twenty_six
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R)) :
    EventuallyPeriodicWithin w
      (g, (ManufacturedReflector.flip R).activatedState) (26 * N) := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, hOldTail, hApproach, hApproachGrooved,
      hApproachForeign, hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete, hleadLen, htailLen, happroachLe⟩ :=
    hmerge.spliced_lobe_reflector
  have hAtravel : A.toSupported.travel ≤ 2 * N :=
    A.travel_le_two_mul_switches hN
  have hRtravel :
      (ManufacturedReflector.flip R).toSupported.travel ≤ 2 * N :=
    (ManufacturedReflector.flip R).travel_le_two_mul_switches hN
  have hleadLe : leadSteps ≤ 2 * N := by
    rw [hleadLen]
    omega
  have holdPrefixLe : oldPrefix.length + 1 ≤ 2 * N := by
    omega
  have hcandyLen : candy.length = oldPrefix.length + approach.length := by
    rw [hCandyEq]
    simp [reversePassages_length]
  have hlobeLe : candy.length + 2 ≤ 4 * N := by
    omega
  have hNpos : 0 < N := by
    have hports := hN mouth outside hmouthLink
    omega
  have holdTailLeRoute : oldTail.length ≤
      ((ManufacturedReflector.flip R).orientedRoute state).length := by
    rw [hrouteSplit]
    simp
    omega
  have holdTailLe : oldTail.length ≤ 2 * N :=
    Nat.le_trans holdTailLeRoute
      (Nat.le_trans
        ((ManufacturedReflector.flip R).orientedRoute_length_le_travel state)
        hRtravel)
  have hrunwayLe : R.runway.length ≤ 2 * N := by
    have hle : R.runway.length ≤
        (ManufacturedReflector.flip R).toSupported.travel := by
      simp [ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported]
      omega
    exact Nat.le_trans hle hRtravel
  have happLe : approach.length ≤ 2 * N := by
    omega
  let cycleSteps :=
    oldTail.length + R.runway.length + approach.length + 2
  have hcycleLe : cycleSteps ≤ 8 * N := by
    dsimp [cycleSteps]
    omega
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · have hlocal := manufactured_flip_runway_splice_within_twenty_four
      hN R state hRpaths hrunway hmouthLink hentryBranch
      hfullGrooved hfullTrace hcrossed hCandy hCandyForeign
      hLobe hlobeLe
    exact (hlocal.prepend hreach).weaken (by omega)
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        horiented hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    by_cases hcontact : ∃ passage ∈ approach,
        passageSwitch passage = R.actionSwitch
    · have hperiodic :=
        manufactured_flip_candy_splice_periodic_of_approach_contact
          R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
          hold horientation hentryGrooved hApproach hApproachGrooved
          hApproachForeign hcrossed hmouthLink harms hcontact
      have hperiod : stepN w cycleSteps
          (outside, flipAt state (mouth / 3)) =
            some (outside, flipAt state (mouth / 3)) := by
        simpa [cycleSteps] using hperiodic.2
      have hlocal : EventuallyPeriodicWithin w
          (outside, flipAt state (mouth / 3)) (8 * N) :=
        eventuallyPeriodicWithin_of_period (by
          dsimp [cycleSteps]
          omega) hcycleLe hperiod
      exact (hlocal.prepend hreach).weaken (by omega)
    · have hApproachForeignOld : ∀ passage ∈ approach,
          passageSwitch passage ≠ R.actionSwitch := by
        intro passage hpassage hEq
        exact hcontact ⟨passage, hpassage, hEq⟩
      have hperiodic :=
        manufactured_flip_candy_splice_periodic_of_approach_foreign
          R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
          hold horientation hentryGrooved hApproach hApproachForeign
          hApproachForeignOld hcrossed hmouthLink
      obtain ⟨settled, hcycleLead, hcyclePeriod⟩ := hperiodic.2
      have hcycleLead' : stepN w cycleSteps
          (outside, flipAt state (mouth / 3)) = some settled := by
        simpa [cycleSteps] using hcycleLead
      have hcyclePeriod' : stepN w cycleSteps settled = some settled := by
        simpa [cycleSteps] using hcyclePeriod
      have hlocal : EventuallyPeriodicWithin w
          (outside, flipAt state (mouth / 3)) (16 * N) :=
        ⟨cycleSteps, cycleSteps, settled, by
          dsimp [cycleSteps]
          omega, by omega, hcycleLead', hcyclePeriod'⟩
      exact (hlocal.prepend hreach).weaken (by omega)

theorem ManufacturedReflector.ChangedForwardMerge.within_twenty_six
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.ChangedForwardMerge B) :
    EventuallyPeriodicWithin w (g, B.activatedState) (26 * N) := by
  cases B with
  | stay R => exact (hmerge.stay_within_sixteen hN).weaken (by omega)
  | flip R => exact hmerge.flip_within_twenty_six hN

theorem backward_contact_within_twelve
    {w : Wiring} {N g e p oldEntry : Nat}
    {oldBase oldEnd base u v : Tongues}
    {recorded approach : List Passage}
    (hNpos : 0 < N)
    (hrecordedLe : recorded.length ≤ 2 * N)
    (happroachLe : approach.length ≤ 2 * N)
    (hrecorded :
      PhysicalTrace w (g, oldBase) recorded (oldEntry, oldEnd))
    (hrecordedGrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (happroach : PhysicalTrace w (e, base) approach (p, u))
    (happroachGrooved : PassagesGrooved v approach) :
    EventuallyPeriodicWithin w (e, base) (12 * N) := by
  have hback := physicalTrace_contact_retraces_prefix
    hrecorded hrecordedGrooved hentry hcontact
  have hforward := happroach.replay_grooved v happroachGrooved
  let cycle := (p, oldEntry) ::
    reversePassages recorded ++ approach
  have hcycle : PhysicalTrace w (p, u) cycle (p, v) := by
    dsimp [cycle]
    simpa [List.append_assoc] using hback.append hforward
  have hheadGrooved : arrive v oldEntry = (p, v) := by
    have hbackLocal := arrive_back u p
    rwa [hcontact] at hbackLocal
  have hallGrooved : PassagesGrooved v cycle := by
    intro passage hp
    dsimp [cycle] at hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadGrooved
    · rcases List.mem_append.mp htail with hold | hnew
      · exact reversePassages_grooved hrecordedGrooved passage hold
      · exact happroachGrooved passage hnew
  have hperiod : stepN w cycle.length (p, v) = some (p, v) := by
    dsimp [cycle]
    exact run_grooved_passages w v p oldEntry p
      (reversePassages recorded ++ approach)
      hcycle.linked hallGrooved hcycle.last_link
  have hlead : stepN w (approach.length + cycle.length)
      (e, base) = some (p, v) := by
    rw [stepN_add, happroach.sound]
    exact hcycle.sound
  have hcycleLen : cycle.length =
      1 + recorded.length + approach.length := by
    dsimp [cycle]
    simp [reversePassages_length]
    omega
  have hpositive : 0 < cycle.length := by
    rw [hcycleLen]
    omega
  exact ⟨approach.length + cycle.length, cycle.length, (p, v),
    hpositive, by rw [hcycleLen]; omega, hlead, hperiod⟩

/-- Quantitative classification of a state-changing protected-support
contact.  The backward orientation is the `12*N` exact retrace/replay lasso;
the forward orientation is retained verbatim for splice repair. -/
theorem ManufacturedReflector.protected_changed_contact_within_or_forward
    {w : Wiring} {N g e p x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedReflector w e g)
    {startState u v : Tongues}
    {route approach suffix : List Passage}
    {path : List Passage} {old : Passage}
    (hrouteLe : route.length ≤ 2 * N)
    (hrouteSplit : route = approach ++ (p, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, u))
    (hpaths : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    EventuallyPeriodicWithin w (g, startState) (12 * N) ∨
      ∃ oriented repaired,
        oriented ∈ B.orientedRoute u ∧
        arrive u oriented.2 = (oriented.1, u) ∧
        passageSwitch oriented = p / 3 ∧
        x = oriented.2 ∧
        arrive v oriented.1 = (oriented.2, repaired) ∧
        arrive repaired oriented.2 = (oriented.1, repaired) := by
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hdirection⟩ :=
    B.changed_contact_on_orientedRoute u v hpaths
      hpath hold hswitch harrive hchanged
  rcases hdirection with hbackward | hforward
  · obtain ⟨recorded, tail, hBsplit⟩ :=
      List.append_of_mem horiented
    have hBroute := B.orientedRoute_trace u hpaths
    have hBsimple := B.orientedRoute_simple u
    have hBgrooved := hBroute.grooved_of_switchSimple hBsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hBroute hBsplit hBgrooved hBsimple
    have hrecorded := hprefixData.1
    have hrecordedForeign : ∀ passage ∈ recorded,
        passageSwitch passage ≠ p / 3 := by
      intro passage hp hEq
      apply hprefixData.2 passage hp
      exact hEq.trans horientedSwitch.symm
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hBsimple ⊢
      rw [hBsplit] at hBsimple
      simp only [List.map_append, List.map_cons] at hBsimple
      exact (List.nodup_append.mp hBsimple).1
    have hflip : v = flipAt u (p / 3) :=
      changed_arrival_eq_flipAt harrive hchanged
    have hrecordedV : PhysicalTrace w
        (e, v) recorded (oriented.1, v) := by
      rw [hflip]
      exact hrecorded.flip_unvisited hrecordedForeign
    have hrecordedGroovedV : PassagesGrooved v recorded :=
      hrecordedV.grooved_of_switchSimple hrecordedSimple
    have hrouteSimple' := hrouteSimple
    rw [hrouteSplit] at hrouteSimple'
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple' ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      exact (List.nodup_append.mp hrouteSimple').1
    have happroachForeign : ∀ passage ∈ approach,
        passageSwitch passage ≠ p / 3 := by
      unfold SwitchSimple at hrouteSimple'
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      have hparts := List.nodup_append.mp hrouteSimple'
      intro passage hp hEq
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (p / 3) (by simp [passageSwitch])
      exact hne hEq
    have happroachV : PhysicalTrace w
        (g, flipAt startState (p / 3)) approach (p, v) := by
      rw [hflip]
      exact happroach.flip_unvisited happroachForeign
    have happroachGroovedV : PassagesGrooved v approach :=
      happroachV.grooved_of_switchSimple happroachSimple
    have hNpos : 0 < N := by
      have hp := hN g e B.entryEdge
      omega
    have hrecordedLeRoute : recorded.length ≤
        (B.orientedRoute u).length := by
      rw [hBsplit]
      simp
    have hrecordedLe : recorded.length ≤ 2 * N :=
      Nat.le_trans hrecordedLeRoute
        (Nat.le_trans (B.orientedRoute_length_le_travel u)
          (B.travel_le_two_mul_switches hN))
    have happroachLe : approach.length ≤ 2 * N := by
      have hprefixLe : approach.length ≤ route.length := by
        rw [hrouteSplit]
        simp
      exact Nat.le_trans hprefixLe hrouteLe
    exact Or.inl (backward_contact_within_twelve hNpos
      hrecordedLe happroachLe hrecorded hrecordedGroovedV
      B.entryEdge (by simpa [hbackward] using harrive)
      happroach happroachGroovedV)
  · obtain ⟨hforwardExit, repaired, hrepair, hgroove⟩ := hforward
    exact Or.inr ⟨oriented, repaired, horiented,
      horientedGroove, horientedSwitch,
      hforwardExit, hrepair, hgroove⟩

/-- Quantitative no-tongue-change counterpart: a backward protected contact
closes within `12*N`; otherwise the exact forward merge is retained. -/
theorem ManufacturedReflector.protected_facing_contact_within_or_forward
    {w : Wiring} {N g e p marker fresh : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedReflector w e g)
    {startState contact : Tongues}
    {route approach suffix path : List Passage}
    (hrouteLe : route.length ≤ 2 * N)
    (hrouteSplit : route = approach ++ (p, marker) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hpath : path ∈ B.toSupported.paths)
    (hold : (fresh, p) ∈ path)
    (harrive : arrive contact p = (fresh, contact)) :
    EventuallyPeriodicWithin w (g, startState) (12 * N) ∨
      (p, fresh) ∈ B.orientedRoute contact := by
  obtain ⟨oriented, horiented, horientation⟩ :=
    B.support_passage_on_orientedRoute contact hpath hold
  rcases horientation with hsame | hreverse
  · have horientedEq : oriented = (fresh, p) := hsame
    subst oriented
    obtain ⟨recorded, tail, hBsplit⟩ :=
      List.append_of_mem horiented
    have hBroute := B.orientedRoute_trace contact hpaths
    have hBsimple := B.orientedRoute_simple contact
    have hBgrooved := hBroute.grooved_of_switchSimple hBsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hBroute hBsplit hBgrooved hBsimple
    have hrecorded := hprefixData.1
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hBsimple ⊢
      rw [hBsplit] at hBsimple
      simp only [List.map_append, List.map_cons] at hBsimple
      exact (List.nodup_append.mp hBsimple).1
    have hrecordedGrooved : PassagesGrooved contact recorded :=
      hrecorded.grooved_of_switchSimple hrecordedSimple
    have hrouteSimple' := hrouteSimple
    rw [hrouteSplit] at hrouteSimple'
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple' ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      exact (List.nodup_append.mp hrouteSimple').1
    have happroachGrooved : PassagesGrooved contact approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have hNpos : 0 < N := by
      have hp := hN g e B.entryEdge
      omega
    have hrecordedLeRoute : recorded.length ≤
        (B.orientedRoute contact).length := by
      rw [hBsplit]
      simp
    have hrecordedLe : recorded.length ≤ 2 * N :=
      Nat.le_trans hrecordedLeRoute
        (Nat.le_trans (B.orientedRoute_length_le_travel contact)
          (B.travel_le_two_mul_switches hN))
    have happroachLe : approach.length ≤ 2 * N := by
      have hprefixLe : approach.length ≤ route.length := by
        rw [hrouteSplit]
        simp
      exact Nat.le_trans hprefixLe hrouteLe
    exact Or.inl (backward_contact_within_twelve hNpos
      hrecordedLe happroachLe hrecorded hrecordedGrooved
      B.entryEdge harrive happroach happroachGrooved)
  · right
    simpa [hreverse] using horiented

/-- Quantitative final-return mouth capture.  The approach and each old
reflector capture cost at most `2*N`, giving lead plus period at most `12*N`.
-/
theorem ManufacturedFlipReflector.facing_mouth_contact_within_twelve
    {w : Wiring} {N g e x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedFlipReflector w e g)
    {startState contact : Tongues}
    {route approach suffix : List Passage}
    (hrouteLe : route.length ≤ 2 * N)
    (hrouteSplit : route = approach ++ (B.mouth, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach
      (B.mouth, contact))
    (hpaths : PathGrooves [B.runway, B.candy] contact) :
    EventuallyPeriodicWithin w (g, startState) (12 * N) := by
  have hrouteSimple' := hrouteSimple
  rw [hrouteSplit] at hrouteSimple'
  have happroachSimple : SwitchSimple approach := by
    unfold SwitchSimple at hrouteSimple' ⊢
    simp only [List.map_append, List.map_cons] at hrouteSimple'
    exact (List.nodup_append.mp hrouteSimple').1
  have hforeign : ∀ passage ∈ approach,
      passageSwitch passage ≠ B.actionSwitch := by
    unfold SwitchSimple at hrouteSimple'
    simp only [List.map_append, List.map_cons] at hrouteSimple'
    have hparts := List.nodup_append.mp hrouteSimple'
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (B.mouth, x)) (by simp)
    apply hne
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hEq
  have happroachGrooved : PassagesGrooved contact approach :=
    happroach.grooved_of_switchSimple happroachSimple
  have happroachContact : PhysicalTrace w
      (g, contact) approach (B.mouth, contact) :=
    happroach.replay_grooved contact happroachGrooved
  let alternate := flipAt contact B.actionSwitch
  have happroachAlternate : PhysicalTrace w
      (g, alternate) approach (B.mouth, alternate) := by
    dsimp [alternate]
    exact happroachContact.flip_unvisited hforeign
  have hpathsAlternate :
      PathGrooves [B.runway, B.candy] alternate := by
    dsimp [alternate]
    change PathGrooves [B.runway, B.candy]
      ((LocalAction.flip B.actionSwitch).apply contact)
    exact hpaths.after_avoiding_action B.support_foreign
  let cap := B.candy.length + 2 + B.runway.length
  have hcaptureFromAlternate :
      stepN w cap (B.mouth, alternate) = some (g, contact) := by
    dsimp [cap, alternate]
    exact B.capture_from_mouth contact
      (pathGrooves_pair.mp hpaths).1
      (pathGrooves_pair.mp hpaths).2
  have hcaptureFromContact :
      stepN w cap (B.mouth, contact) = some (g, alternate) := by
    have hcapture := B.capture_from_mouth alternate
      (pathGrooves_pair.mp hpathsAlternate).1
      (pathGrooves_pair.mp hpathsAlternate).2
    simpa [cap, alternate, flipAt_flipAt] using hcapture
  let half := approach.length + cap
  have hhalfAlternate :
      stepN w half (g, alternate) = some (g, contact) := by
    dsimp [half]
    rw [stepN_add, happroachAlternate.sound]
    exact hcaptureFromAlternate
  have hhalfContact :
      stepN w half (g, contact) = some (g, alternate) := by
    dsimp [half]
    rw [stepN_add, happroachContact.sound]
    exact hcaptureFromContact
  have hperiod :
      stepN w (half + half) (g, alternate) =
        some (g, alternate) := by
    rw [stepN_add, hhalfAlternate]
    exact hhalfContact
  have hlead : stepN w half (g, startState) =
      some (g, alternate) := by
    dsimp [half]
    rw [stepN_add, happroach.sound]
    exact hcaptureFromContact
  have happroachLe : approach.length ≤ 2 * N := by
    have hprefixLe : approach.length ≤ route.length := by
      rw [hrouteSplit]
      simp
    exact Nat.le_trans hprefixLe hrouteLe
  have hcapLe : cap ≤ 2 * N := by
    have hcaptureLe : cap ≤
        (ManufacturedReflector.flip B).toSupported.travel := by
      dsimp [cap]
      simp [ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported]
      omega
    exact Nat.le_trans hcaptureLe
      ((ManufacturedReflector.flip B).travel_le_two_mul_switches hN)
  have hhalfLe : half ≤ 4 * N := by
    dsimp [half]
    omega
  have hpositive : 0 < half + half := by
    dsimp [half, cap]
    omega
  exact ⟨half, half + half, (g, alternate), hpositive,
    by omega, hlead, hperiod⟩

/-- Orientation-free quantitative form of the final-return exception. -/
theorem ManufacturedReflector.return_change_facing_within_twelve
    {w : Wiring} {N g e p x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedReflector w e g)
    {startState contact : Tongues}
    {route approach suffix : List Passage}
    (hrouteLe : route.length ≤ 2 * N)
    (hrouteSplit : route = approach ++ (p, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hp : p % 3 = 0)
    (hswitch : p / 3 = B.preReturn.1 / 3)
    (hreturnChange : B.activatedState (p / 3) ≠
      B.preReturn.2 (p / 3)) :
    EventuallyPeriodicWithin w (g, startState) (12 * N) := by
  cases B with
  | stay R => exact (hreturnChange rfl).elim
  | flip R =>
      have hsecondSwitch : R.secondArm / 3 = R.mouth / 3 := by
        have hs := arrive_exit_switch R.returnState R.secondArm
        rw [R.crossed] at hs
        exact hs.symm
      have hmouthStem := R.mouth_is_stem
      have hpmouth : p = R.mouth := by
        change p / 3 = R.secondArm / 3 at hswitch
        omega
      subst p
      exact R.facing_mouth_contact_within_twelve hN hrouteLe
        hrouteSplit hrouteSimple happroach hpaths

/-- Fully quantitative protected-repair classification.  Every early exit is
a `12*N` lasso; the only residuals are the two named forward merges and the
complete repaired route with both supports grooved. -/
theorem manufactured_pair_protected_repair_quantitative_outcomes
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    EventuallyPeriodicWithin w (g, B.activatedState) (12 * N) ∨
      A.FacingForwardMerge B ∨
      A.ChangedForwardMerge B ∨
      ∃ finalState,
        PhysicalTrace w (g, B.activatedState)
          (A.orientedRoute B.activatedState)
          (A.orientedFinish B.activatedState, finalState) ∧
        PathGrooves A.toSupported.paths finalState ∧
        PathGrooves B.toSupported.paths finalState := by
  have hrouteLe : (A.orientedRoute B.activatedState).length ≤ 2 * N :=
    Nat.le_trans (A.orientedRoute_length_le_travel B.activatedState)
      (A.travel_le_two_mul_switches hN)
  rcases A.repair_current_route_preserving_until_conflict
      B.baseState B.activatedState hA hB with hfacing | hrest
  · obtain ⟨before, p, x, after, contact, other,
        hsplit, hprefix, hBcontact, hp, hchange,
        hcontact, harrive, hother⟩ := hfacing
    rcases B.facing_exit_matches_activation_passage
        hchange hcontact hp harrive with hreturn | hexploration
    · left
      exact B.return_change_facing_within_twelve hN hrouteLe
        hsplit (A.orientedRoute_simple B.activatedState)
        hprefix hBcontact hp hreturn.1 hreturn.2
    · obtain ⟨oldApproach, fresh, oldSuffix, oldU, oldV, path,
          _holdSplit, _holdSwitch, _holdTrace, _holdArrive,
          hpath, hold, hotherFresh⟩ := hexploration
      have harriveFresh : arrive contact p = (fresh, contact) := by
        simpa [hotherFresh] using harrive
      rcases B.protected_facing_contact_within_or_forward hN hrouteLe
          hsplit (A.orientedRoute_simple B.activatedState)
          hprefix hBcontact hpath hold harriveFresh with
        hperiodic | hforward
      · exact Or.inl hperiodic
      · exact Or.inr (Or.inl ⟨before, p, x, after,
          contact, fresh, path, hsplit, hprefix, hBcontact, hp,
          hchange, by simpa [passageSwitch] using hcontact,
          hpath, hold, harriveFresh,
          by simpa [hotherFresh] using hother,
          hforward⟩)
  · rcases hrest with hchanged | hcomplete
    · obtain ⟨approach, p, x, suffix, u, v, path, old,
          hsplit, hprefix, hBu, harrive,
          hpath, hold, hswitch, hchange⟩ := hchanged
      rcases B.protected_changed_contact_within_or_forward hN hrouteLe
          hsplit (A.orientedRoute_simple B.activatedState)
          hprefix hBu harrive hpath hold hswitch hchange with
        hperiodic | hforward
      · exact Or.inl hperiodic
      · obtain ⟨oriented, repaired, horiented, horientedGroove,
            horientedSwitch, hforwardExit, hrepair,
            hgroove⟩ := hforward
        exact Or.inr (Or.inr (Or.inl
          ⟨approach, p, x, suffix, u, v, path, old,
            oriented, repaired, hsplit, hprefix, hBu, harrive,
            hpath, hold, hswitch, hchange, horiented,
            horientedGroove, horientedSwitch, hforwardExit,
            hrepair, hgroove⟩))
    · exact Or.inr (Or.inr (Or.inr hcomplete))

/-- **Quantitative protected-repair theorem.**  Damaged support is repaired
or absorbed into a forward splice within a lasso cap of `26*N`. -/
theorem manufactured_pair_protected_repair_within_twenty_six
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    EventuallyPeriodicWithin w (g, B.activatedState) (26 * N) := by
  rcases manufactured_pair_protected_repair_quantitative_outcomes
      hN A B hA hB with hperiodic | hrest
  · exact hperiodic.weaken (by omega)
  · rcases hrest with hfacing | hrest
    · exact (hfacing.within_twelve hN).weaken (by omega)
    · rcases hrest with hchanged | hcomplete
      · exact hchanged.within_twenty_six hN
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        exact (A.completed_route_with_pair_support_within hN B
          B.baseState B.activatedState finalState hA hrepair
          hAfinal hBfinal).weaken (by omega)

theorem long_run_eventually_periodic_within_thirty
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1) :
    EventuallyPeriodicWithin w start (30 * N + 2) := by
  rcases long_run_within_or_damaged_pair hN hlive hentry with
    hperiodic | hdamaged
  · exact hperiodic.weaken (by omega)
  · obtain ⟨A, B, stateA, stateB, firstTravel, secondTravel,
      hfirstLe, hsecondLe, _hbaseA, _hactivatedA,
      hreachA, hgroovesA, hbaseB, hactivatedB,
      hreachB, hgroovesB, _hpreservesB,
      _hnotGrooved, _hcontact⟩ := hdamaged
    have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
      simpa [hbaseB] using hgroovesA
    have hBatActivated :
        PathGrooves B.toSupported.paths B.activatedState := by
      simpa [← hactivatedB] using hgroovesB
    have hlocal := manufactured_pair_protected_repair_within_twenty_six
      hN A B hAatBase hBatActivated
    have hreach : stepN w (firstTravel + secondTravel) start =
        some (start.1, B.activatedState) := by
      rw [stepN_add, hreachA]
      simpa [hactivatedB] using hreachB
    exact (hlocal.prepend hreach).weaken (by omega)

theorem long_run_eventually_periodic_within_thirty_without_entry
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (3 * N + 3) start = some finish) :
    EventuallyPeriodicWithin w start (30 * N + 3) := by
  have hsplit : 3 * N + 3 = 1 + (3 * N + 2) := by omega
  rw [hsplit, stepN_add] at hlive
  cases hone : stepN w 1 start with
  | none =>
      rw [hone] at hlive
      contradiction
  | some middle =>
      rw [hone] at hlive
      simp only [Option.bind_some] at hlive
      rcases start with ⟨startPort, startState⟩
      have honeStep : stepN w 1 (startPort, startState) =
          some middle := hone
      simp only [stepN, step] at hone
      let localStep := arrive startState startPort
      cases hlink : w.link localStep.1 with
      | none =>
          simp [localStep, hlink] at hone
      | some entry =>
          have hmiddle : middle = (entry, localStep.2) := by
            simpa [localStep, hlink] using hone.symm
          subst middle
          have hlocal := long_run_eventually_periodic_within_thirty
            hN hlive hlink
          exact (hlocal.prepend honeStep).weaken (by omega)
end GeneralN
