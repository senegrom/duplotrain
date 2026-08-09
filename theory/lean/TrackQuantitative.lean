import TrackGlobalRepair
import StateLaw

/-!
# Quantitative extraction from the direct physical-track theorem

`TrackGlobalRepair` proves that every sufficiently long live lazy-point run
is eventually periodic.  Its qualitative predicate deliberately forgets the
size of the transient and period.  This file retains that information and
turns it into a count of observed configurations.

The final linear state law is still open: the remaining task is to propagate
a linear cap through every branch of the global repair theorem.  The basic
counting reduction and the disjoint two-reflector case below are unconditional
and general in `N`.
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

theorem EventuallyPeriodicWithin.toEventuallyPeriodic
    {w : Wiring} {start : Nat × Tongues} {cap : Nat}
    (h : EventuallyPeriodicWithin w start cap) :
    EventuallyPeriodic w start := by
  obtain ⟨lead, period, settled, hpos, _hcap, hlead, hperiod⟩ := h
  exact ⟨lead, period, settled, hpos, hlead, hperiod⟩

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

end GeneralN
