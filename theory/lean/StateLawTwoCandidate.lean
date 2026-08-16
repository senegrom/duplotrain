import KnownEdgeLift
import FirstCycleCountSharp
import TrackEarlyRepairConstant
import EarlyFacingConstant
import TrackGlobalRepair
import StateLaw
import RepairLeadTwoPhase
import TwoPhasePrefixTailCount
import TrackStayContactAllTime
import RunwayHistoricalThree
import TrackThetaAllTime
import TwoJourneyTailCountSharp
import ShortSuffixCount

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
      hB, hrouteSplit, hprefix, hpaths,
      hcandyMem, hsecond⟩ :=
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
    exact stay_twoPhase_concat hprefixContact.sound
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
          exact stay_twoPhase_concat hpriorAlternate.sound
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
          exact stay_twoPhase_concat htoContact htoContactPhase
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
          exact stay_twoPhase_concat hrepairPrefix.sound
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
        exact stay_twoPhase_concat hprefixAlternate.sound
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

end GeneralN
