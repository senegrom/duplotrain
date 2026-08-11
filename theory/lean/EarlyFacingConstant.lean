import RepairLeadTwoPhase
import TwoPhasePrefixTailCount
import TrackEarlyRepairCount

/-!
# Constant count for the protected final-mouth facing exit

At the final mouth of a flip reflector, capture and replay alternate between
exactly two tongue phases.  Starting the tail at the mouth/contact endpoint
makes this a direct two-vector tail.  The protected repair approach ending at
that endpoint is itself two-phase, so boundary overlap gives three vectors in
total.
-/

namespace GeneralN

private theorem earlyfacing_twoPhase_concat
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

/-- From a flip reflector's final mouth/contact state, every future tongue
vector is either the contact phase or its action-switch flip. -/
theorem ManufacturedFlipReflector.facing_mouth_tail_two_phase
    {w : Wiring} {g e : Nat}
    (B : ManufacturedFlipReflector w e g)
    {contact : Tongues} {approach : List Passage}
    (happroachContact : PhysicalTrace w
      (g, contact) approach (B.mouth, contact))
    (happroachSimple : SwitchSimple approach)
    (hforeign : ∀ passage ∈ approach,
      passageSwitch passage ≠ B.actionSwitch)
    (hpaths : PathGrooves [B.runway, B.candy] contact) :
    ∀ d, ∃ port phase,
      stepN w d (B.mouth, contact) = some (port, phase) ∧
      (phase = flipAt contact B.actionSwitch ∨ phase = contact) := by
  let alternate := flipAt contact B.actionSwitch
  have happroachGrooved : PassagesGrooved contact approach :=
    happroachContact.grooved_of_switchSimple happroachSimple
  have happroachAlternate : PhysicalTrace w
      (g, alternate) approach (B.mouth, alternate) := by
    dsimp [alternate]
    exact happroachContact.flip_unvisited hforeign
  have happroachAlternateGrooved : PassagesGrooved alternate approach := by
    dsimp [alternate]
    exact grooved_after_flip_other happroachGrooved hforeign
  have hpathsAlternate : PathGrooves [B.runway, B.candy] alternate := by
    dsimp [alternate]
    change PathGrooves [B.runway, B.candy]
      ((LocalAction.flip B.actionSwitch).apply contact)
    exact hpaths.after_avoiding_action B.support_foreign
  let cap := B.candy.length + 2 + B.runway.length
  have hcapContact : stepN w cap (B.mouth, contact) =
      some (g, alternate) := by
    have hcapture := B.capture_from_mouth alternate
      (pathGrooves_pair.mp hpathsAlternate).1
      (pathGrooves_pair.mp hpathsAlternate).2
    simpa [cap, alternate, flipAt_flipAt] using hcapture
  have hcapAlternate : stepN w cap (B.mouth, alternate) =
      some (g, contact) := by
    dsimp [cap, alternate]
    exact B.capture_from_mouth contact
      (pathGrooves_pair.mp hpaths).1
      (pathGrooves_pair.mp hpaths).2
  have hcapContactPhase : ∀ d, d ≤ cap → ∃ port phase,
      stepN w d (B.mouth, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, phase, hrun, hphase⟩ :=
      B.capture_from_mouth_two_phase alternate
        (pathGrooves_pair.mp hpathsAlternate).1
        (pathGrooves_pair.mp hpathsAlternate).2 (d := d) (by
          dsimp [cap] at hd
          omega)
    have hstart : flipAt alternate B.actionSwitch = contact := by
      dsimp [alternate]
      exact flipAt_flipAt contact B.actionSwitch
    rw [hstart] at hrun hphase
    refine ⟨port, phase, hrun, ?_⟩
    rcases hphase with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hcapAlternatePhase : ∀ d, d ≤ cap → ∃ port phase,
      stepN w d (B.mouth, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, phase, hrun, hphase⟩ :=
      B.capture_from_mouth_two_phase contact
        (pathGrooves_pair.mp hpaths).1
        (pathGrooves_pair.mp hpaths).2 (d := d) (by
          dsimp [cap] at hd
          omega)
    refine ⟨port, phase, hrun, ?_⟩
    rcases hphase with h | h
    · exact Or.inl h
    · exact Or.inr h
  have happroachContactPhase : ∀ d, d ≤ approach.length →
      ∃ port phase, stepN w d (g, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, hrun⟩ :=
      happroachContact.grooved_prefix_tongues contact
        happroachGrooved hd
    exact ⟨port, contact, hrun, Or.inr rfl⟩
  have happroachAlternatePhase : ∀ d, d ≤ approach.length →
      ∃ port phase, stepN w d (g, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, hrun⟩ :=
      happroachAlternate.grooved_prefix_tongues alternate
        happroachAlternateGrooved hd
    exact ⟨port, alternate, hrun, Or.inl rfl⟩
  let half := cap + approach.length
  have hhalfContact : stepN w half (B.mouth, contact) =
      some (B.mouth, alternate) := by
    dsimp [half]
    rw [stepN_add, hcapContact]
    exact happroachAlternate.sound
  have hhalfAlternate : stepN w half (B.mouth, alternate) =
      some (B.mouth, contact) := by
    dsimp [half]
    rw [stepN_add, hcapAlternate]
    exact happroachContact.sound
  have hhalfContactPhase : ∀ d, d ≤ half → ∃ port phase,
      stepN w d (B.mouth, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    exact earlyfacing_twoPhase_concat hcapContact hcapContactPhase
      happroachAlternatePhase d (by simpa [half] using hd)
  have hhalfAlternatePhase : ∀ d, d ≤ half → ∃ port phase,
      stepN w d (B.mouth, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    exact earlyfacing_twoPhase_concat hcapAlternate hcapAlternatePhase
      happroachContactPhase d (by simpa [half] using hd)
  let period := half + half
  have hperiod : stepN w period (B.mouth, contact) =
      some (B.mouth, contact) := by
    dsimp [period]
    rw [stepN_add, hhalfContact]
    exact hhalfAlternate
  have hwindow : ∀ d, d ≤ period → ∃ port phase,
      stepN w d (B.mouth, contact) = some (port, phase) ∧
        (phase = contact ∨ phase = alternate) := by
    intro d hd
    obtain ⟨port, phase, hrun, hphase⟩ :=
      earlyfacing_twoPhase_concat hhalfContact hhalfContactPhase
        hhalfAlternatePhase d (by simpa [period] using hd)
    exact ⟨port, phase, hrun, hphase.symm⟩
  have hpositive : 0 < period := by
    dsimp [period, half, cap]
    omega
  intro d
  obtain ⟨port, phase, hrun, hphase⟩ :=
    periodic_two_phase_prefix_tongues hpositive hperiod hwindow d
  refine ⟨port, phase, hrun, ?_⟩
  have hphase' := hphase.symm
  simpa [alternate] using hphase'

/-- Protected final-return facing exit: at most three restricted tongue
vectors. -/
theorem ManufacturedReflector.return_change_facing_distinct_le_three
    {w : Wiring} {N g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {contact : Tongues} {approach suffix : List Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState) approach
      (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hp : p % 3 = 0)
    (hswitch : p / 3 = B.preReturn.1 / 3)
    (hreturnChange : B.activatedState (p / 3) ≠
      B.preReturn.2 (p / 3))
    (times : List Nat)
    (hlive : ∀ d ∈ times,
      (stepN w d (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 3 := by
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
      have hrouteSimple :=
        A.orientedRoute_simple (ManufacturedReflector.flip R).activatedState
      have happroachSimple : SwitchSimple approach := by
        unfold SwitchSimple at hrouteSimple ⊢
        rw [hrouteSplit] at hrouteSimple
        simp only [List.map_append, List.map_cons] at hrouteSimple
        exact (List.nodup_append.mp hrouteSimple).1
      have hrouteMembership : ∀ passage ∈ approach,
          passage ∈ A.orientedRoute
            (ManufacturedReflector.flip R).activatedState := by
        intro passage hpassage
        rw [hrouteSplit]
        exact List.mem_append_left _ hpassage
      have hphase := A.repair_prefix_two_phase (.flip R) hA hBstart
        happroach happroachSimple hrouteMembership hpaths
      have happroachGrooved : PassagesGrooved contact approach :=
        happroach.grooved_of_switchSimple happroachSimple
      have happroachContact : PhysicalTrace w
          (g, contact) approach (R.mouth, contact) :=
        happroach.replay_grooved contact happroachGrooved
      have hforeign : ∀ passage ∈ approach,
          passageSwitch passage ≠ R.actionSwitch := by
        have hsimple :=
          A.orientedRoute_simple
            (ManufacturedReflector.flip R).activatedState
        unfold SwitchSimple at hsimple
        rw [hrouteSplit] at hsimple
        simp only [List.map_append, List.map_cons] at hsimple
        have hparts := List.nodup_append.mp hsimple
        intro passage hpassage hEq
        have hne := hparts.2.2 (passageSwitch passage)
          (List.mem_map.mpr ⟨passage, hpassage, rfl⟩)
          (passageSwitch (R.mouth, x)) (by simp)
        apply hne
        simpa [passageSwitch,
          ManufacturedFlipReflector.actionSwitch] using hEq
      have hall := R.facing_mouth_tail_two_phase
        happroachContact happroachSimple hforeign hpaths
      have htail : ∀ tailTimes : List Nat,
          (∀ d ∈ tailTimes,
            (stepN w d (R.mouth, contact)).isSome) →
          (tailTimes.map
            (restrictedTonguesAt w N (R.mouth, contact))).Nodup →
          tailTimes.length ≤ 2 := by
        intro tailTimes _ htailNodup
        let history := [VectorCount.restrict N contact,
          VectorCount.restrict N (flipAt contact R.actionSwitch)]
        have hcover : NoveltyCoverOn w N (R.mouth, contact)
            tailTimes [] 2 := by
          refine ⟨history, by simp [history], ?_⟩
          intro d hd
          simp only [List.nil_append]
          obtain ⟨port, phase, hrun, hphaseTail⟩ := hall d
          have hvec : restrictedTonguesAt w N (R.mouth, contact) d =
              VectorCount.restrict N phase := by
            simp [restrictedTonguesAt, tonguesAt, hrun]
          rw [hvec]
          rcases hphaseTail with h | h
          · simp [history, h]
          · simp [history, h]
        have hcount := noveltyCoverOn_distinct_count hcover htailNodup
        simpa using hcount
      exact two_phase_prefix_then_direct_tail_distinct_le_succ
        happroach.sound hphase htail (by omega) times hlive hnd

end GeneralN
