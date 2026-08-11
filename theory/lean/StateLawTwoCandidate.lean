import StateLawThreeSharp
import FirstCycleCountSharp
import OneJourneyTailCount
import TwoJourneyBoundaryTailCount
import TrackEarlyRepairConstant
import EarlyFacingConstant
import ChangedStayCountConstant
import ChangedFlipCountConstant
import CompleteRepairConstant
import RepairLeadTwoPhase
import TwoPhasePrefixTailCount
import FacingMergeCount

/-!
# Constant tongue count for protected facing-forward repairs

The existing facing-forward theorem charged every position of the repair
approach.  Under the protected-repair hypotheses that approach has only its
activated and contact tongue phases.  The reverse-candy suffix and the whole
absorbing future use only the contact phase and its one-switch alternate.
The two pieces share the contact endpoint, so the complete branch has at most
three restricted tongue vectors.
-/

namespace GeneralN

private theorem facingconstant_twoPhase_concat
    {w : Wiring} {start middle : Nat × Tongues}
    {left right : Nat} {u v : Tongues}
    (hleft : stepN w left start = some middle)
    (hleftPhase : ∀ d, d ≤ left → ∃ port phase,
      stepN w d start = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (hrightPhase : ∀ d, d ≤ right → ∃ port phase,
      stepN w d middle = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (d : Nat) (hd : d ≤ left + right) :
    ∃ port phase, stepN w d start = some (port, phase) ∧
      (phase = u ∨ phase = v) := by
  by_cases hdl : d ≤ left
  · exact hleftPhase d hdl
  · let r := d - left
    have hr : r ≤ right := by
      dsimp [r]
      omega
    have hdecomp : d = left + r := by
      dsimp [r]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hrightPhase r hr
    refine ⟨port, phase, ?_, hphase⟩
    rw [hdecomp, stepN_add, hleft]
    simpa using hrun

/-- **Protected facing-forward count:** at most three distinct restricted
tongue vectors. -/
theorem ManufacturedReflector.FacingForwardMerge.distinct_le_three
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    (hmerge : A.FacingForwardMerge B)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 3 := by
  obtain ⟨R, before, p, x, after, contact, fresh,
      hB, hrouteSplit, hprefix, hpaths, _hp, _harrive,
      _hfreshNe, hcandyMem, hsecond, _hforward⟩ :=
    hmerge.flip_candy
  subst B
  obtain ⟨candyBefore, candyAfter, hcandySplit⟩ :=
    List.append_of_mem hcandyMem
  let alternate := flipAt contact R.actionSwitch
  obtain ⟨tailTravel, htailPositive, htailLe, htailContact,
      htailAlternate, htailContactPhase, htailAlternatePhase⟩ :=
    R.reverse_candy_suffix_absorbs_twoPhases contact hpaths hsecond
      hcandySplit
  have hrouteSimple :=
    A.orientedRoute_simple
      (ManufacturedReflector.flip R).activatedState
  rw [hrouteSplit] at hrouteSimple
  have hbeforeSimple : SwitchSimple before := by
    unfold SwitchSimple at hrouteSimple ⊢
    simp only [List.map_append, List.map_cons] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).1
  have hbeforeRoute : ∀ passage ∈ before,
      passage ∈ A.orientedRoute
        (ManufacturedReflector.flip R).activatedState := by
    intro passage hpassage
    rw [hrouteSplit]
    exact List.mem_append_left _ hpassage
  have hprefixPhase := A.repair_prefix_two_phase (.flip R) hA hBstart
    hprefix hbeforeSimple hbeforeRoute hpaths
  have hbeforeGrooved : PassagesGrooved contact before :=
    hprefix.grooved_of_switchSimple hbeforeSimple
  have hprefixContact :
      PhysicalTrace w (g, contact) before (p, contact) :=
    hprefix.replay_grooved contact hbeforeGrooved
  let loopSteps := before.length + tailTravel
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
  have hbeforePhase : ∀ d, d ≤ before.length → ∃ port phase,
      stepN w d (g, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, hrun⟩ :=
      hprefixContact.grooved_prefix_tongues contact hbeforeGrooved hd
    exact ⟨port, contact, hrun, Or.inr rfl⟩
  have htailContactPhase' : ∀ d, d ≤ tailTravel → ∃ port phase,
      stepN w d (p, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, phase, hrun, hphase⟩ :=
      htailContactPhase d hd
    exact ⟨port, phase, hrun, hphase.symm⟩
  have hcontactLoopPhase : ∀ d, d ≤ loopSteps → ∃ port phase,
      stepN w d (g, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    exact facingconstant_twoPhase_concat hprefixContact.sound
      hbeforePhase htailContactPhase' d
        (by simpa [loopSteps] using hd)
  have hallPhase : ∀ d, ∃ port phase,
      stepN w d (g, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    by_cases htouch : ∃ passage ∈ before,
        passageSwitch passage = R.actionSwitch
    · obtain ⟨passage, hpassage, hswitch⟩ := htouch
      obtain ⟨prior, later, hbeforeSplit⟩ :=
        List.append_of_mem hpassage
      have hprefixData := simple_grooved_trace_prefix_to_occurrence
        hprefixContact hbeforeSplit hbeforeGrooved hbeforeSimple
      rcases passage with ⟨a, b⟩
      simp only [passageSwitch] at hswitch
      have hstem := hprefixContact.passage_stem_endpoint (a, b) (by
        simpa using hpassage)
      change a = 3 * (a / 3) ∨ b = 3 * (a / 3) at hstem
      have hmouth : R.mouth = 3 * R.actionSwitch := by
        have hm := R.mouth_is_stem
        unfold ManufacturedFlipReflector.actionSwitch
        omega
      rcases hstem with haStem | hbStem
      · have haMouth : a = R.mouth := by omega
        subst a
        have hpriorContact :
            PhysicalTrace w (g, contact) prior (R.mouth, contact) :=
          hprefixData.1
        have hpriorForeign : ∀ old ∈ prior,
            passageSwitch old ≠ R.actionSwitch := by
          intro old hold
          have hne := hprefixData.2 old hold
          simpa [passageSwitch, hswitch] using hne
        have hpriorAlternate :
            PhysicalTrace w (g, alternate) prior
              (R.mouth, alternate) := by
          dsimp [alternate]
          exact hpriorContact.flip_unvisited hpriorForeign
        have hpriorGrooved : PassagesGrooved contact prior := by
          intro old hold
          exact hbeforeGrooved old (by
            rw [hbeforeSplit]
            exact List.mem_append_left _ hold)
        have hpriorAlternateGrooved :
            PassagesGrooved alternate prior := by
          dsimp [alternate]
          exact grooved_after_flip_other hpriorGrooved hpriorForeign
        have hpriorPhase : ∀ d, d ≤ prior.length → ∃ port phase,
            stepN w d (g, alternate) = some (port, phase) ∧
              (phase = alternate ∨ phase = contact) := by
          intro d hd
          obtain ⟨port, hrun⟩ :=
            hpriorAlternate.grooved_prefix_tongues alternate
              hpriorAlternateGrooved hd
          exact ⟨port, alternate, hrun, Or.inl rfl⟩
        let captureSteps := R.candy.length + 2 + R.runway.length
        have hcapture : stepN w captureSteps (R.mouth, alternate) =
            some (g, contact) := by
          dsimp [captureSteps, alternate]
          exact R.capture_from_mouth contact
            (pathGrooves_pair.mp hpaths).1
            (pathGrooves_pair.mp hpaths).2
        have hcapturePhase : ∀ d, d ≤ captureSteps → ∃ port phase,
            stepN w d (R.mouth, alternate) = some (port, phase) ∧
              (phase = alternate ∨ phase = contact) := by
          intro d hd
          exact R.capture_from_mouth_twoPhases contact hpaths hsecond d
            (by simpa [captureSteps] using hd)
        have htoContact :
            stepN w (prior.length + captureSteps) (g, alternate) =
              some (g, contact) := by
          rw [stepN_add, hpriorAlternate.sound]
          exact hcapture
        have htoContactPhase : ∀ d,
            d ≤ prior.length + captureSteps → ∃ port phase,
              stepN w d (g, alternate) = some (port, phase) ∧
                (phase = alternate ∨ phase = contact) := by
          intro d hd
          exact facingconstant_twoPhase_concat hpriorAlternate.sound
            hpriorPhase hcapturePhase d hd
        let period := prior.length + captureSteps + loopSteps
        have hperiod : stepN w period (g, alternate) =
            some (g, alternate) := by
          dsimp [period]
          rw [stepN_add, htoContact]
          exact hcontactToAlternate
        have hperiodPositive : 0 < period := by
          dsimp [period]
          omega
        have hperiodPhase : ∀ d, d ≤ period → ∃ port phase,
            stepN w d (g, alternate) = some (port, phase) ∧
              (phase = alternate ∨ phase = contact) := by
          intro d hd
          exact facingconstant_twoPhase_concat htoContact htoContactPhase
            hcontactLoopPhase d (by simpa [period] using hd)
        exact periodic_two_phase_prefix_tongues
          hperiodPositive hperiod hperiodPhase
      · have hbMouth : b = R.mouth := by omega
        rw [hbMouth] at hbeforeSplit
        have hpriorContact :
            PhysicalTrace w (g, contact) prior (a, contact) :=
          hprefixData.1
        have hpriorForeign : ∀ old ∈ prior,
            passageSwitch old ≠ R.actionSwitch := by
          intro old hold
          have hne := hprefixData.2 old hold
          simpa [passageSwitch, hswitch] using hne
        have hpriorAlternate :
            PhysicalTrace w (g, alternate) prior (a, alternate) := by
          dsimp [alternate]
          exact hpriorContact.flip_unvisited hpriorForeign
        have hpriorGrooved : PassagesGrooved contact prior := by
          intro old hold
          exact hbeforeGrooved old (by
            rw [hbeforeSplit]
            exact List.mem_append_left _ hold)
        have hpriorAlternateGrooved :
            PassagesGrooved alternate prior := by
          dsimp [alternate]
          exact grooved_after_flip_other hpriorGrooved hpriorForeign
        have hfull := hprefixContact
        rw [hbeforeSplit] at hfull
        obtain ⟨middle, hpriorRaw, hrest⟩ := hfull.split_append
        have hmiddle : middle = (a, contact) := by
          have h₁ := hpriorRaw.sound
          have h₂ := hpriorContact.sound
          rw [h₂] at h₁
          exact (Option.some.inj h₁).symm
        subst middle
        have hrest' : PhysicalTrace w (a, contact)
            ([(a, R.mouth)] ++ later) (p, contact) := by
          simpa using hrest
        obtain ⟨afterOne, honeRaw, hlater⟩ := hrest'.split_append
        have hforward : arrive contact a = (R.mouth, contact) := by
          have hback := hbeforeGrooved (a, R.mouth) (by
            rw [hbeforeSplit]
            exact List.mem_append_right prior List.mem_cons_self)
          exact groove_forward hback
        have hafterOneTongues : afterOne.2 = contact := by
          have hone : step w (a, contact) = some afterOne := by
            simpa [stepN] using honeRaw.sound
          have hparts := step_some_parts hone
          calc
            afterOne.2 = arrivedTongues (a, contact) := hparts.2
            _ = contact := by simp [arrivedTongues, hforward]
        have hafterOne : afterOne = (afterOne.1, contact) := by
          apply Prod.ext
          · rfl
          · exact hafterOneTongues
        rw [hafterOne] at honeRaw hlater
        have haBranch : a % 3 ≠ 0 := by
          intro haMod
          have hne := arrive_exit_ne contact a
          rw [hforward] at hne
          apply hne
          omega
        have hrepairArrive : arrive alternate a =
            (R.mouth, contact) := by
          have hrepair := flipped_passage_forward_trailing
            hforward haBranch
          dsimp [alternate]
          simpa [hswitch] using hrepair
        have hlink : w.link R.mouth = some afterOne.1 := by
          simpa [lastPassageExit] using honeRaw.last_link
        have hrepairChange : PhysicalTrace w (a, alternate)
            [(a, R.mouth)] (afterOne.1, contact) :=
          PhysicalTrace.cons hrepairArrive hlink (PhysicalTrace.nil _)
        have hlaterGrooved : PassagesGrooved contact later := by
          intro old hold
          exact hbeforeGrooved old (by
            rw [hbeforeSplit]
            exact List.mem_append_right prior
              (List.mem_cons_of_mem _ hold))
        have hrepairPrefix :
            PhysicalTrace w (g, alternate) before (p, contact) := by
          rw [hbeforeSplit]
          simpa using hpriorAlternate.append
            (hrepairChange.append hlater)
        have hrepairPrefixPhase : ∀ d, d ≤ before.length →
            ∃ port phase,
              stepN w d (g, alternate) = some (port, phase) ∧
                (phase = alternate ∨ phase = contact) := by
          intro d hd
          have hphase := PhysicalTrace.one_change_prefix_tongues
            hpriorAlternate hpriorAlternateGrooved hrepairChange
            hlater hlaterGrooved (d := d) (by
              rw [hbeforeSplit] at hd
              simp only [List.length_append, List.length_cons] at hd
              omega)
          exact hphase
        have hperiod : stepN w loopSteps (g, alternate) =
            some (g, alternate) := by
          dsimp [loopSteps]
          rw [stepN_add, hrepairPrefix.sound]
          exact htailContact
        have hperiodPhase : ∀ d, d ≤ loopSteps → ∃ port phase,
            stepN w d (g, alternate) = some (port, phase) ∧
              (phase = alternate ∨ phase = contact) := by
          intro d hd
          exact facingconstant_twoPhase_concat hrepairPrefix.sound
            hrepairPrefixPhase htailContactPhase' d
              (by simpa [loopSteps] using hd)
        exact periodic_two_phase_prefix_tongues
          hloopPositive hperiod hperiodPhase
    · have hforeign : ∀ passage ∈ before,
          passageSwitch passage ≠ R.actionSwitch := by
        intro passage hpassage hswitch
        exact htouch ⟨passage, hpassage, hswitch⟩
      have hprefixAlternate :
          PhysicalTrace w (g, alternate) before (p, alternate) := by
        dsimp [alternate]
        exact hprefixContact.flip_unvisited hforeign
      have hbeforeAlternateGrooved :
          PassagesGrooved alternate before := by
        dsimp [alternate]
        exact grooved_after_flip_other hbeforeGrooved hforeign
      have hbeforeAlternatePhase : ∀ d, d ≤ before.length →
          ∃ port phase,
            stepN w d (g, alternate) = some (port, phase) ∧
              (phase = alternate ∨ phase = contact) := by
        intro d hd
        obtain ⟨port, hrun⟩ :=
          hprefixAlternate.grooved_prefix_tongues alternate
            hbeforeAlternateGrooved hd
        exact ⟨port, alternate, hrun, Or.inl rfl⟩
      have hperiod : stepN w loopSteps (g, alternate) =
          some (g, alternate) := by
        dsimp [loopSteps]
        rw [stepN_add, hprefixAlternate.sound]
        exact htailAlternate
      have hperiodPhase : ∀ d, d ≤ loopSteps → ∃ port phase,
          stepN w d (g, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = contact) := by
        intro d hd
        have htailAlternatePhase' : ∀ r, r ≤ tailTravel →
            ∃ port phase,
              stepN w r (p, alternate) = some (port, phase) ∧
                (phase = alternate ∨ phase = contact) := by
          intro r hr
          obtain ⟨port, phase, hrun, hphase⟩ :=
            htailAlternatePhase r hr
          rcases hphase with hphase | hphase
          · exact ⟨port, phase, hrun, Or.inr hphase⟩
          · exact ⟨port, phase, hrun, Or.inl hphase⟩
        exact facingconstant_twoPhase_concat hprefixAlternate.sound
          hbeforeAlternatePhase htailAlternatePhase' d
            (by simpa [loopSteps] using hd)
      exact periodic_two_phase_prefix_tongues
        hloopPositive hperiod hperiodPhase
  have htailAll : ∀ d, ∃ port phase,
      stepN w d (p, contact) = some (port, phase) ∧
        (phase = contact ∨ phase = alternate) := by
    intro d
    by_cases hd : d ≤ tailTravel
    · exact htailContactPhase d hd
    · let r := d - tailTravel
      have hdEq : d = tailTravel + r := by
        dsimp [r]
        omega
      obtain ⟨port, phase, hrun, hphase⟩ := hallPhase r
      refine ⟨port, phase, ?_, hphase.symm⟩
      rw [hdEq, stepN_add, htailContact]
      simpa using hrun
  have htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes, (stepN w k (p, contact)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (p, contact))).Nodup →
      tailTimes.length ≤ 2 := by
    intro tailTimes _ htailNodup
    let history := [VectorCount.restrict N contact,
      VectorCount.restrict N alternate]
    have hcover : NoveltyCoverOn w N (p, contact) tailTimes [] 2 := by
      refine ⟨history, by simp [history], ?_⟩
      intro d hd
      simp only [List.nil_append]
      obtain ⟨port, phase, hrun, hphase⟩ := htailAll d
      have hvec : restrictedTonguesAt w N (p, contact) d =
          VectorCount.restrict N phase := by
        simp [restrictedTonguesAt, tonguesAt, hrun]
      rw [hvec]
      rcases hphase with h | h
      · simp [history, h]
      · simp [history, h]
    have hcount := noveltyCoverOn_distinct_count hcover htailNodup
    simpa using hcount
  exact two_phase_prefix_then_direct_tail_distinct_le_succ
    hprefix.sound hprefixPhase htail (by omega) times hlive hnd

end GeneralN

/-!
# Constant protected-repair classification

The existing classifier erased the physical witnesses of its early backward
branches and retained only an `N+2` count.  The two lemmas below keep those
witnesses: the protected approach has two phases, while the retrace/replay
tail has two phases and shares the contact boundary.  Hence each early branch
has at most three vectors.
-/

namespace GeneralN

private theorem twocand_protected_changed_contact_three_or_forward
    {w : Wiring} {N g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {u v : Tongues} {approach suffix path : List Passage}
    {old : Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix)
    (hrouteSimple : SwitchSimple (A.orientedRoute B.activatedState))
    (happroach : PhysicalTrace w (g, B.activatedState) approach (p, u))
    (hpaths : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      times.length ≤ 3) ∨
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
  · obtain ⟨recorded, tail, hBsplit⟩ := List.append_of_mem horiented
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
    have happroachRoute : ∀ passage ∈ approach,
        passage ∈ A.orientedRoute B.activatedState := by
      intro passage hp
      rw [hrouteSplit]
      exact List.mem_append_left _ hp
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
    have happroachGroovedU : PassagesGrooved u approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachReplayU : PhysicalTrace w
        (g, u) approach (p, u) :=
      happroach.replay_grooved u happroachGroovedU
    have happroachV : PhysicalTrace w
        (g, v) approach (p, v) := by
      rw [hflip]
      exact happroachReplayU.flip_unvisited happroachForeign
    have happroachGroovedV : PassagesGrooved v approach :=
      happroachV.grooved_of_switchSimple happroachSimple
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes, (stepN w k (p, u)).isSome) →
        (tailTimes.map (restrictedTonguesAt w N (p, u))).Nodup →
        tailTimes.length ≤ 2 := by
      intro tailTimes _ htailNodup
      exact backward_contact_tail_distinct_le_two
        hrecorded hrecordedGroovedV B.entryEdge
        (by simpa [hbackward] using harrive)
        happroachReplayU happroachGroovedV tailTimes htailNodup
    exact Or.inl (fun times hlive hnd =>
      two_phase_prefix_then_direct_tail_distinct_le_succ
        happroach.sound hphase htail (by omega) times hlive hnd)
  · obtain ⟨hforwardExit, repaired, hrepair, hgroove⟩ := hforward
    exact Or.inr ⟨oriented, repaired, horiented,
      horientedGroove, horientedSwitch,
      hforwardExit, hrepair, hgroove⟩

private theorem twocand_protected_facing_contact_three_or_forward
    {w : Wiring} {N g e p marker fresh : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {contact : Tongues} {approach suffix path : List Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, marker) :: suffix)
    (hrouteSimple : SwitchSimple (A.orientedRoute B.activatedState))
    (happroach : PhysicalTrace w
      (g, B.activatedState) approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hpath : path ∈ B.toSupported.paths)
    (hold : (fresh, p) ∈ path)
    (harrive : arrive contact p = (fresh, contact)) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      times.length ≤ 3) ∨
      (p, fresh) ∈ B.orientedRoute contact := by
  obtain ⟨oriented, horiented, horientation⟩ :=
    B.support_passage_on_orientedRoute contact hpath hold
  rcases horientation with hsame | hreverse
  · have horientedEq : oriented = (fresh, p) := hsame
    subst oriented
    obtain ⟨recorded, tail, hBsplit⟩ := List.append_of_mem horiented
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
    have happroachRoute : ∀ passage ∈ approach,
        passage ∈ A.orientedRoute B.activatedState := by
      intro passage hp
      rw [hrouteSplit]
      exact List.mem_append_left _ hp
    have happroachGrooved : PassagesGrooved contact approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachReplay : PhysicalTrace w
        (g, contact) approach (p, contact) :=
      happroach.replay_grooved contact happroachGrooved
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes,
          (stepN w k (p, contact)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (p, contact))).Nodup →
        tailTimes.length ≤ 2 := by
      intro tailTimes _ htailNodup
      exact backward_contact_tail_distinct_le_two
        hrecorded hrecordedGrooved B.entryEdge harrive
        happroachReplay happroachGrooved tailTimes htailNodup
    exact Or.inl (fun times hlive hnd =>
      two_phase_prefix_then_direct_tail_distinct_le_succ
        happroach.sound hphase htail (by omega) times hlive hnd)
  · exact Or.inr (by simpa [hreverse] using horiented)

end GeneralN

namespace GeneralN

/-- **Flat protected-repair bound.**  Once two opposite manufactured
reflectors have been built and their supports are protected, every repair
outcome visits at most six restricted tongue vectors. -/
theorem manufactured_pair_protected_repair_distinct_le_six_candidate
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 6 := by
  rcases A.repair_current_route_preserving_until_conflict
      B.baseState B.activatedState hA hB with hfacing | hrest
  · obtain ⟨before, p, x, after, contact, other,
        hsplit, hprefix, hBcontact, hp, hchange,
        hcontact, harrive, hother⟩ := hfacing
    rcases B.facing_exit_matches_activation_passage
        hchange hcontact hp harrive with hreturn | hexploration
    · have hc :=
        ManufacturedReflector.return_change_facing_distinct_le_three
          A B hA hB hsplit hprefix hBcontact hp
          hreturn.1 hreturn.2 times hlive hnd
      omega
    · obtain ⟨oldApproach, fresh, oldSuffix, oldU, oldV, path,
          _holdSplit, _holdSwitch, _holdTrace, _holdArrive,
          hpath, hold, hotherFresh⟩ := hexploration
      have harriveFresh : arrive contact p = (fresh, contact) := by
        simpa [hotherFresh] using harrive
      rcases twocand_protected_facing_contact_three_or_forward
          A B hA hB hsplit
          (A.orientedRoute_simple B.activatedState)
          hprefix hBcontact hpath hold harriveFresh with
        hcount | hforward
      · have hc := hcount times hlive hnd
        omega
      · have hmerge : A.FacingForwardMerge B :=
          ⟨before, p, x, after, contact, fresh, path,
            hsplit, hprefix, hBcontact, hp, hchange,
            by simpa [passageSwitch] using hcontact,
            hpath, hold, harriveFresh,
            by simpa [hotherFresh] using hother, hforward⟩
        have hc := hmerge.distinct_le_three hA hB times hlive hnd
        omega
  · rcases hrest with hchanged | hcomplete
    · obtain ⟨approach, p, x, suffix, u, v, path, old,
          hsplit, hprefix, hBu, harrive,
          hpath, hold, hswitch, hchange⟩ := hchanged
      rcases twocand_protected_changed_contact_three_or_forward
          A B hA hB hsplit
          (A.orientedRoute_simple B.activatedState)
          hprefix hBu harrive hpath hold hswitch hchange with
        hcount | hforward
      · have hc := hcount times hlive hnd
        omega
      · obtain ⟨oriented, repaired, horiented, horientedGroove,
            horientedSwitch, hforwardExit, hrepair,
            hgroove⟩ := hforward
        have hmerge : A.ChangedForwardMerge B :=
          ⟨approach, p, x, suffix, u, v, path, old,
            oriented, repaired, hsplit, hprefix, hBu, harrive,
            hpath, hold, hswitch, hchange, horiented,
            horientedGroove, horientedSwitch, hforwardExit,
            hrepair, hgroove⟩
        cases B with
        | stay R =>
            have hc := hmerge.stay_distinct_le_three
              hA hB times hlive hnd
            omega
        | flip R =>
            have hc := hmerge.flip_distinct_le_six hA hB times hnd
            omega
    · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
      have hc := A.completed_protected_route_with_pair_distinct_le_five
        B hA hB hrepair hAfinal hBfinal times hlive hnd
      omega

end GeneralN

namespace GeneralN

private theorem twocand_nodup_of_map_nodup
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

/-- If the train is already off by `horizon`, every live sample time lies
strictly before that horizon. -/
private theorem twocand_dead_tail_distinct_le
    {w : Wiring} {N horizon : Nat} {start : Nat × Tongues}
    (hdead : stepN w horizon start = none)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ horizon := by
  have htimesNodup : times.Nodup :=
    twocand_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  have hlt : ∀ k ∈ times, k < horizon := by
    intro k hk
    by_cases hsmall : k < horizon
    · exact hsmall
    · have hkge : horizon ≤ k := by omega
      have hkEq : k = horizon + (k - horizon) := by omega
      have hnone : stepN w k start = none := by
        rw [hkEq, stepN_add, hdead]
        simp
      have hkLive := hlive k hk
      simp [hnone] at hkLive
  exact nodup_nat_lt_length htimesNodup hlt

/-- **Known incoming edge, coefficient two.**  The first and second sharp
manufacturing histories contribute at most `2*N+2` after their shared
boundary is erased.  Every protected-repair suffix is flat at six vectors.
If either activation window ends off-track, its live suffix has at most
`N+1` positions, so no long-run hypothesis is needed. -/
theorem known_edge_distinct_le_two_mul_add_eight_candidate
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 8 := by
  cases hfirstLive : stepN w (N + 1) start with
  | none =>
      have hc := twocand_dead_tail_distinct_le
        (N := N) hfirstLive times hlive hnd
      omega
  | some firstFinish =>
      rcases first_activated_count_outcome_sharp
          hN hfirstLive hentry with hcycleA | hreflectorA
      · have hc := hcycleA times hnd
        omega
      · obtain ⟨A, stateA, hfirstLe, hgroovesA,
          hbaseA, hactivatedA, hreachA, _hpreservesA⟩ := hreflectorA
        let firstTravel :=
          A.exploration.length + A.runway.length + 1
        cases hsecondLive : stepN w (N + 1) (e, stateA) with
        | none =>
            have htail : ∀ tailTimes : List Nat,
                (∀ k ∈ tailTimes,
                  (stepN w k (e, stateA)).isSome) →
                (tailTimes.map
                  (restrictedTonguesAt w N (e, stateA))).Nodup →
                tailTimes.length ≤ N + 1 := by
              intro tailTimes htailLive htailNodup
              exact twocand_dead_tail_distinct_le
                (N := N) hsecondLive tailTimes
                  htailLive htailNodup
            have hcount :=
              one_manufacturing_journey_then_direct_tail_distinct_le
                (tailCap := N + 1)
                hN A stateA hbaseA hactivatedA hreachA hgroovesA
                htail times hlive hnd
            omega
        | some secondFinish =>
            have hentryB : w.link start.1 = some e :=
              w.symm _ _ A.entryEdge
            rcases first_activated_count_outcome_sharp
                (w := w) (N := N) (e := start.1)
                hN hsecondLive hentryB with
              hcycleB | hreflectorB
            · have htail : ∀ tailTimes : List Nat,
                  (∀ k ∈ tailTimes,
                    (stepN w k (e, stateA)).isSome) →
                  (tailTimes.map
                    (restrictedTonguesAt w N (e, stateA))).Nodup →
                  tailTimes.length ≤ N + 2 := by
                intro tailTimes _ htailNodup
                exact hcycleB tailTimes htailNodup
              have hcount :=
                one_manufacturing_journey_then_direct_tail_distinct_le
                  (tailCap := N + 2)
                  hN A stateA hbaseA hactivatedA hreachA hgroovesA
                  htail times hlive hnd
              omega
            · obtain ⟨B, stateB, hsecondLe, hgroovesB,
                  hbaseB, hactivatedB, hreachB,
                  _hpreservesB⟩ := hreflectorB
              have hAatBase :
                  PathGrooves A.toSupported.paths B.baseState := by
                simpa [hbaseB] using hgroovesA
              have hBatActivated :
                  PathGrooves B.toSupported.paths B.activatedState := by
                simpa [← hactivatedB] using hgroovesB
              have htail : ∀ tailTimes : List Nat,
                  (∀ k ∈ tailTimes,
                    (stepN w k (start.1, stateB)).isSome) →
                  (tailTimes.map
                    (restrictedTonguesAt w N
                      (start.1, stateB))).Nodup →
                  tailTimes.length ≤ 6 := by
                intro tailTimes htailLive htailNodup
                have htailLive' : ∀ k ∈ tailTimes,
                    (stepN w k
                      (start.1, B.activatedState)).isSome := by
                  simpa [← hactivatedB] using htailLive
                have htailNodup' :
                    (tailTimes.map
                      (restrictedTonguesAt w N
                        (start.1, B.activatedState))).Nodup := by
                  simpa [← hactivatedB] using htailNodup
                exact
                  manufactured_pair_protected_repair_distinct_le_six_candidate
                    A B hAatBase hBatActivated tailTimes
                      htailLive' htailNodup'
              have hcount :=
                two_manufacturing_journeys_then_boundary_tail_distinct_le
                  (tailCap := 6)
                  hN A B stateA stateB hbaseA hactivatedA
                  hreachA hgroovesA hbaseB hactivatedB
                  hreachB hgroovesB htail (by omega)
                  times hlive hnd
              omega

end GeneralN

namespace GeneralN

private theorem twocand_nodup_map_filter
    {α : Type} [BEq α] [LawfulBEq α]
    {f : Nat → α} (p : Nat → Bool) :
    ∀ {xs : List Nat},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
            apply hnd.1
            exact List.mem_map.mpr
              ⟨y, (List.mem_filter.mp hy).1, hfy⟩
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem twocand_nodup_filter_nat (p : Nat → Bool) :
    ∀ {xs : List Nat}, xs.Nodup → (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hm => hnd.1 (List.mem_filter.mp hm).1, ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem twocand_zero_positive_partition :
    ∀ xs : List Nat,
      (xs.filter (fun k => decide (k = 0))).length +
        (xs.filter (fun k => decide (0 < k))).length = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons k rest ih =>
      by_cases hk : k = 0
      · subst k
        simp
        omega
      · have hkPos : 0 < k := by omega
        simp [hk, hkPos]
        omega

private theorem twocand_zero_filter_length_le_one
    {xs : List Nat} (hnd : xs.Nodup) :
    (xs.filter (fun k => decide (k = 0))).length ≤ 1 := by
  have hfilterNodup :
      (xs.filter (fun k => decide (k = 0))).Nodup :=
    twocand_nodup_filter_nat _ hnd
  apply nodup_nat_lt_length hfilterNodup
  intro k hk
  have hk0 : k = 0 :=
    of_decide_eq_true (List.mem_filter.mp hk).2
  omega

/-- **Unconditional general-`N` coefficient-two state bound.**  A single
train on any `N`-switch lazy-point wiring visits at most `2*N+9`
pairwise-distinct restricted tongue vectors, whether it runs forever or
falls off.  This improves the verified coefficient-three theorem but does
not prove the open `N+6` `StateLaw`. -/
theorem state_law_linear_two_add_nine_candidate
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 9 := by
  have htimesNodup : times.Nodup :=
    twocand_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  cases hone : stepN w 1 start with
  | none =>
      have hc := twocand_dead_tail_distinct_le
        (N := N) hone times hlive hnd
      omega
  | some middle =>
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
          let positive := times.filter (fun k => decide (0 < k))
          let shifted := positive.map (fun k => k - 1)
          have hshiftVector : shifted.map
              (restrictedTonguesAt w N (entry, localStep.2)) =
              positive.map
                (restrictedTonguesAt w N (startPort, startState)) := by
            dsimp [shifted]
            rw [List.map_map]
            apply List.map_congr_left
            intro k hk
            have hkPos : 0 < k :=
              of_decide_eq_true (List.mem_filter.mp hk).2
            have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
            have hkEq : k = 1 + (k - 1) := by omega
            have hrun : stepN w k (startPort, startState) =
                stepN w (k - 1) (entry, localStep.2) := by
              rw [hkEq, stepN_add, honeStep]
              simp
            have hkLive := hlive k hkTimes
            cases htail : stepN w (k - 1) (entry, localStep.2) with
            | none =>
                rw [hrun, htail] at hkLive
                simp at hkLive
            | some localFinish =>
                have hglobal : stepN w k (startPort, startState) =
                    some localFinish := by rw [hrun, htail]
                simp [Function.comp_apply, restrictedTonguesAt,
                  tonguesAt, hglobal, htail]
          have hpositiveNodup :
              (positive.map (restrictedTonguesAt w N
                (startPort, startState))).Nodup := by
            dsimp [positive]
            exact twocand_nodup_map_filter _ hnd
          have hshiftedNodup :
              (shifted.map (restrictedTonguesAt w N
                (entry, localStep.2))).Nodup := by
            rw [hshiftVector]
            exact hpositiveNodup
          have hshiftedLive : ∀ d ∈ shifted,
              (stepN w d (entry, localStep.2)).isSome := by
            intro d hd
            obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
            have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
            have hkPos : 0 < k :=
              of_decide_eq_true (List.mem_filter.mp hk).2
            have hkEq : k = 1 + (k - 1) := by omega
            have hkLive := hlive k hkTimes
            rw [hkEq, stepN_add, honeStep] at hkLive
            exact hkLive
          have hshiftedBound : shifted.length ≤ 2 * N + 8 :=
            known_edge_distinct_le_two_mul_add_eight_candidate
              hN hlink shifted hshiftedLive hshiftedNodup
          have hpositiveLength : positive.length = shifted.length := by
            simp [shifted]
          have hzeroBound :
              (times.filter (fun k => decide (k = 0))).length ≤ 1 :=
            twocand_zero_filter_length_le_one htimesNodup
          have hpartition := twocand_zero_positive_partition times
          dsimp [positive] at hpositiveLength
          omega

end GeneralN

namespace GeneralN

/-
/-- Pointwise-best published form: never weaker than the previous `3*N+7`
theorem, and equal to the new coefficient-two bound from `N = 2` onward. -/
theorem state_law_linear_two_candidate
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ Nat.min (2 * N + 9) (3 * N + 7) := by
  apply Nat.le_min
  · exact state_law_linear_two_add_nine_candidate
      w N hN start times hlive hnd
  · exact state_law_linear_three_sharp
      w N hN start times hlive hnd

-/

namespace GeneralN

/-- Pointwise-best published form: never weaker than the previous `3*N+7`
theorem, and equal to the new coefficient-two bound from `N = 2` onward. -/
theorem state_law_linear_two_candidate
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ Nat.min (2 * N + 9) (3 * N + 7) := by
  exact Nat.le_min.mpr ⟨
    state_law_linear_two_add_nine_candidate
      w N hN start times hlive hnd,
    state_law_linear_three_sharp
      w N hN start times hlive hnd⟩

end GeneralN
end GeneralN
