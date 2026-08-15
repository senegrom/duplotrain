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

/-- Same-exit cycle closure with the transient two-phase law retained. -/
theorem PhysicalTrace.simple_same_exit_cycle_traces_with_phase
    {w : Wiring} {p x q : Nat} {u₀ u v : Tongues}
    {rest : List Passage}
    (htrace : PhysicalTrace w (p, u₀) ((p, x) :: rest) (q, u))
    (hsimple : SwitchSimple ((p, x) :: rest))
    (hnext : arrive u q = (x, v)) :
    PhysicalTrace w (q, u) ((q, x) :: rest) (q, v) ∧
      PhysicalTrace w (q, v) ((q, x) :: rest) (q, v) ∧
      SwitchSimple ((q, x) :: rest) ∧
      (∀ d, d ≤ ((q, x) :: rest).length → ∃ port phase,
        stepN w d (q, u) = some (port, phase) ∧
          (phase = u ∨ phase = v)) := by
  have holdGrooved := htrace.grooved_of_switchSimple hsimple
  have holdLinked := htrace.linked
  have hfinal : w.link (lastPassageExit x rest) = some q :=
    htrace.last_link
  have hheadOld : arrive u x = (p, u) :=
    holdGrooved (p, x) (by simp)
  have hpx : p / 3 = x / 3 := by
    have hs := arrive_exit_switch u x
    rw [hheadOld] at hs
    exact hs
  have hqx : x / 3 = q / 3 := by
    have hs := arrive_exit_switch u q
    rw [hnext] at hs
    exact hs
  unfold SwitchSimple at hsimple
  simp only [List.map_cons, List.nodup_cons] at hsimple
  have hrestGrooved : PassagesGrooved v rest := by
    intro passage hp
    have hold := holdGrooved passage (List.mem_cons_of_mem _ hp)
    have hpassageSwitch : passageSwitch passage ≠ p / 3 := by
      intro hEq
      apply hsimple.1
      apply List.mem_map.mpr
      exact ⟨passage, hp, hEq⟩
    have hexitSwitch : passage.2 / 3 = passageSwitch passage := by
      have hs := arrive_exit_switch u passage.2
      rw [hold] at hs
      exact hs.symm
    have hforeign : passage.2 / 3 ≠ q / 3 := by
      rw [hexitSwitch, ← hqx, ← hpx]
      exact hpassageSwitch
    have hsame : v (passage.2 / 3) = u (passage.2 / 3) :=
      arrive_preserves_other hnext hforeign
    exact groove_transfer hold hsame
  have hheadNew : arrive v x = (q, v) := by
    have hb := arrive_back u q
    rw [hnext] at hb
    exact hb
  have hnewGrooved : PassagesGrooved v ((q, x) :: rest) := by
    intro passage hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadNew
    · exact hrestGrooved passage htail
  have hnewLinked : LinkedPassages w ((q, x) :: rest) := by
    cases rest with
    | nil => trivial
    | cons passage rest =>
        simpa [LinkedPassages] using holdLinked
  have hstable : PhysicalTrace w (q, v) ((q, x) :: rest) (q, v) :=
    physicalTrace_grooved_passages w v q x q rest
      hnewLinked hnewGrooved hfinal
  have htransient : PhysicalTrace w (q, u) ((q, x) :: rest) (q, v) := by
    cases rest with
    | nil =>
        exact PhysicalTrace.cons hnext
          (by simpa [lastPassageExit] using hfinal)
          (PhysicalTrace.nil (q, v))
    | cons passage rest =>
        rcases passage with ⟨r, y⟩
        have hxy : w.link x = some r := holdLinked.1
        have htailLinked : LinkedPassages w ((r, y) :: rest) :=
          hnewLinked.2
        have htailGrooved : PassagesGrooved v ((r, y) :: rest) := by
          intro passage hp
          exact hnewGrooved passage (List.mem_cons_of_mem _ hp)
        have htailFinal : w.link (lastPassageExit y rest) = some q := by
          simpa [lastPassageExit] using hfinal
        exact PhysicalTrace.cons hnext hxy
          (physicalTrace_grooved_passages w v r y q rest
            htailLinked htailGrooved htailFinal)
  have hsimpleCycle : SwitchSimple ((q, x) :: rest) := by
    unfold SwitchSimple
    simp only [List.map_cons, passageSwitch]
    have hpq : p / 3 = q / 3 := hpx.trans hqx
    constructor
    · intro a ha hEq
      apply hsimple.1
      have hheadEq : passageSwitch (p, x) = a := by
        calc
          passageSwitch (p, x) = p / 3 := rfl
          _ = q / 3 := hpq
          _ = a := hEq
      rw [hheadEq]
      exact ha
    · exact hsimple.2
  have hphase : ∀ d, d ≤ ((q, x) :: rest).length → ∃ port phase,
      stepN w d (q, u) = some (port, phase) ∧
        (phase = u ∨ phase = v) := by
    intro d hd
    cases d with
    | zero =>
        exact ⟨q, u, by simp [stepN], Or.inl rfl⟩
    | succ n =>
        have hn : n ≤ rest.length := by simp at hd; omega
        cases rest with
        | nil =>
            have hn0 : n = 0 := by simp at hn; omega
            subst n
            have hlink : w.link x = some q := by
              simpa [lastPassageExit] using hfinal
            refine ⟨q, v, ?_, Or.inr rfl⟩
            simp [stepN, step, hnext, hlink]
        | cons passage tail =>
            rcases passage with ⟨r, y⟩
            have hlink : w.link x = some r := holdLinked.1
            have hone : stepN w 1 (q, u) = some (r, v) := by
              simp [stepN, step, hnext, hlink]
            have htailTrace : PhysicalTrace w (r, v)
                ((r, y) :: tail) (q, v) := by
              cases htransient with
              | @cons _ _ q' _ v' _ _ harrive hlink' htail =>
                  have hq' : q' = r := by
                    have := Option.some.inj (hlink'.symm.trans hlink)
                    exact this
                  have hv' : v' = v := by
                    have hh := harrive.symm.trans hnext
                    exact congrArg Prod.snd hh
                  simpa [hq', hv'] using htail
            have htailGrooved : PassagesGrooved v ((r, y) :: tail) := by
              intro old hold
              exact hnewGrooved old (List.mem_cons_of_mem _ hold)
            obtain ⟨port, hrun⟩ :=
              htailTrace.grooved_prefix_tongues v htailGrooved hn
            refine ⟨port, v, ?_, Or.inr rfl⟩
            rw [show n + 1 = 1 + n by omega, stepN_add, hone]
            simpa using hrun
  exact ⟨htransient, hstable, hsimpleCycle, hphase⟩

/-- First-revisit fork retaining the two-phase transient-cycle certificate. -/
theorem first_revisit_cycle_phase_or_activated_reflector
    (w : Wiring) {start : Prod Nat Tongues}
    {runway path : List Passage}
    {p x q y e : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hsw : p / 3 = q / 3)
    (hrepeat : arrive u q = (y, v))
    (hentry : w.link e = some start.1) :
    (∃ cycle settled,
      cycle ≠ [] ∧
      PhysicalTrace w (q, u) cycle (q, settled) ∧
      PhysicalTrace w (q, settled) cycle (q, settled) ∧
      SwitchSimple cycle ∧
      (∀ d, d ≤ cycle.length → ∃ port phase,
        stepN w d (q, u) = some (port, phase) ∧
          (phase = u ∨ phase = settled))) ∨
    (∃ (A : ManufacturedReflector w start.1 e) (state : Tongues),
      PathGrooves A.toSupported.paths state ∧
      A.baseState = start.2 ∧
      state = A.activatedState ∧
      stepN w (runway.length + 1) (q, u) = some (e, state) ∧
      (∀ j, j ∉ A.exploration.map passageSwitch →
        state j = start.2 j)) := by
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
      refine ⟨(p, x), List.mem_append_right runway List.mem_cons_self, ?_⟩
      simp only [passageSwitch]
      omega
    exact (arrive_preserves_other hrepeat hjq).trans hu
  rcases hshare with hpq | hpy | hxq | hxy
  · subst q
    left
    have hgrooved := hexcursion.grooved_of_switchSimple hsimpleExcursion
    have hstable : PhysicalTrace w (p, u) ((p, x) :: path) (p, u) :=
      physicalTrace_grooved_passages w u p x p path
        hexcursion.linked hgrooved hexcursion.last_link
    have hphase : ∀ d, d ≤ ((p, x) :: path).length → ∃ port phase,
        stepN w d (p, u) = some (port, phase) ∧
          (phase = u ∨ phase = u) := by
      intro d hd
      obtain ⟨port, hrun⟩ :=
        hstable.grooved_prefix_tongues u hgrooved hd
      exact ⟨port, u, hrun, Or.inl rfl⟩
    exact ⟨(p, x) :: path, u, by simp,
      hstable, hstable, hsimpleExcursion, hphase⟩
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
    obtain ⟨htransient, hstable, hsimpleCycle, hphase⟩ :=
      hexcursion.simple_same_exit_cycle_traces_with_phase
        hsimpleExcursion hrepeat
    exact ⟨(q, x) :: path, v, by simp,
      htransient, hstable, hsimpleCycle, hphase⟩

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
  have hcount' : times.length ≤ history.length := by simpa using hcount
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
  have hfork := first_revisit_cycle_phase_or_activated_reflector w
    hrunway hexcursion hbeforeSimple hsw hrepeat hentry
  have hvisited :
      stepN w (runway ++ (p, x) :: path).length start =
        some (q, u) := hbeforeTrace.sound
  have hvisitedLe : (runway ++ (p, x) :: path).length ≤ N :=
    hbeforeTrace.simple_length_le hN hbeforeSimple
  rcases hfork with hcycle | hreflector
  · left
    obtain ⟨cycle, settled, hnonempty, htransient,
      hstable, hsimpleCycle, hphase⟩ := hcycle
    intro times hnd
    exact prefix_then_two_phase_cycle_distinct_le_succ_succ
      hvisited hvisitedLe hnonempty htransient hstable
      hsimpleCycle hphase times hnd
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
      have hlen : A.exploration.length + A.runway.length + 1 =
          A.exploration.length + (A.runway.length + 1) := by omega
      rw [hlen, stepN_add, A.exploration_trace.sound]
      exact hbackExact
    refine ⟨A, state, ?_, hgrooves, hbase, hactivated, ?_, hpreserves⟩
    · omega
    · simpa [hbase, hactivated] using hreachBase

end GeneralN
