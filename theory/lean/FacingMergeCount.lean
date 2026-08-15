import TrackEarlyRepairCount
import FacingForwardNovelty

/-!
# Tongue count for the facing-forward merge

The facing-forward tail was counted through its full bounded lead window
(`4*N+1` positions).  Its actual vector content is far smaller: the lead is
the route prefix (at most `N` passages, hence an `N+1` position window)
followed by the absorbing reverse-candy suffix, which — like the infinite
tail after it — shows only the two phases `contact`/`alternate`.  The
whole merge therefore exposes at most `N+2` distinct restricted tongue
vectors, with no liveness hypothesis.
-/

namespace GeneralN

/-- **Facing-forward merge count.**  The route prefix window plus the single
`alternate` phase: at most `N+2` distinct restricted tongue vectors. -/
theorem ManufacturedReflector.FacingForwardMerge.distinct_le_succ_succ
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.FacingForwardMerge B)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ N + 2 := by
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
  have hbeforeLeN : before.length ≤ N :=
    hprefix.simple_length_le hN hbeforeSimple
  have hcontactWindow :
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState)
          before.length = VectorCount.restrict N contact := by
    simp [restrictedTonguesAt, tonguesAt, hprefix.sound]
  have hcover : NoveltyCoverOn w N
      (g, (ManufacturedReflector.flip R).activatedState) times []
      (N + 2) := by
    refine ⟨((List.range (before.length + 1)).map
      (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState))) ++
        [VectorCount.restrict N alternate], by simp; omega, ?_⟩
    intro k hk
    simp only [List.nil_append]
    by_cases hkpre : k ≤ before.length
    · exact List.mem_append_left _
        (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩)
    · have hmem : ∀ {port : Nat} {phase : Tongues},
          stepN w k
            (g, (ManufacturedReflector.flip R).activatedState) =
              some (port, phase) →
          (phase = alternate ∨ phase = contact) →
          restrictedTonguesAt w N
            (g, (ManufacturedReflector.flip R).activatedState) k ∈
            ((List.range (before.length + 1)).map
              (restrictedTonguesAt w N
                (g, (ManufacturedReflector.flip R).activatedState))) ++
              [VectorCount.restrict N alternate] := by
        intro port phase hrun hphase
        have hvec : restrictedTonguesAt w N
            (g, (ManufacturedReflector.flip R).activatedState) k =
              VectorCount.restrict N phase := by
          simp [restrictedTonguesAt, tonguesAt, hrun]
        rcases hphase with h | h
        · apply List.mem_append_right
          simp [hvec, h]
        · apply List.mem_append_left
          refine List.mem_map.mpr
            ⟨before.length, List.mem_range.mpr (by omega), ?_⟩
          rw [hcontactWindow, hvec, h]
      by_cases hkloop : k ≤ loopSteps
      · let r := k - before.length
        have hr : r ≤ tailTravel := by
          dsimp [r]
          dsimp [loopSteps] at hkloop
          omega
        have hkEq : k = before.length + r := by
          dsimp [r]
          omega
        obtain ⟨port, phase, hrun, hphase⟩ :=
          htailContactPhase' r hr
        have hrunGlobal : stepN w k
            (g, (ManufacturedReflector.flip R).activatedState) =
              some (port, phase) := by
          rw [hkEq, stepN_add, hprefix.sound]
          simpa using hrun
        exact hmem hrunGlobal hphase
      · let r := k - loopSteps
        have hkEq : k = loopSteps + r := by
          dsimp [r]
          omega
        obtain ⟨port, phase, hrun, hphase⟩ := hallPhase r
        have hrunGlobal : stepN w k
            (g, (ManufacturedReflector.flip R).activatedState) =
              some (port, phase) := by
          rw [hkEq, stepN_add, hlead]
          simpa using hrun
        exact hmem hrunGlobal hphase
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

end GeneralN
