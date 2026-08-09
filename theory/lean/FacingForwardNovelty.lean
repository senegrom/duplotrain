import ForeignSpliceNovelty

/-!
# Sharp novelty for the facing-forward repair branch

The no-change forward merge is stronger than merely eventually periodic.  Its
actual construction lead reaches the action-flipped state of the protected
reflector, and every later tongue vector is one of exactly two phases: that
`alternate` state or the pre-flip `contact` state.  Consequently, if every
state on the actual lead is already historical, the complete infinite future
contributes at most one new restricted tongue vector.

Everything below is over the raw `Wiring` / `stepN` dynamics, for arbitrary
`N`.  No finiteness argument or bounded-switch exhaustion is used.
-/

namespace GeneralN

private theorem twoPhase_concat
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
    exact hrun

private theorem groovedTrace_twoPhase
    {w : Wiring} {startPort finishPort : Nat}
    {u v : Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (startPort, u) passages (finishPort, u))
    (hgrooved : PassagesGrooved u passages)
    (d : Nat) (hd : d ≤ passages.length) :
    ∃ port phase,
      stepN w d (startPort, u) = some (port, phase) ∧
        (phase = u ∨ phase = v) := by
  obtain ⟨port, hrun⟩ :=
    htrace.grooved_prefix_tongues u hgrooved hd
  exact ⟨port, u, hrun, Or.inl rfl⟩

/-- Pointwise strengthening of mouth capture.  The capture starts in the
action-flipped state, traverses the candy in that state, pins the action tongue
on the return arm, and retraces the runway in the original state.  There are
therefore only the two endpoint tongue vectors at every intermediate time. -/
theorem ManufacturedFlipReflector.capture_from_mouth_twoPhases
    {w : Wiring} {e g : Nat}
    (R : ManufacturedFlipReflector w e g)
    (contact : Tongues)
    (hpaths : PathGrooves [R.runway, R.candy] contact)
    (hsecond : contact R.actionSwitch = bval R.secondArm) :
    let alternate := flipAt contact R.actionSwitch
    ∀ d, d ≤ R.candy.length + 2 + R.runway.length →
      ∃ port phase,
        stepN w d (R.mouth, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = contact) := by
  let alternate := flipAt contact R.actionSwitch
  have hopp : bval R.secondArm = !(bval R.firstArm) :=
    branch_values_opposite R.firstArm_branch R.secondArm_branch
      (R.firstArm_switch.trans R.secondArm_switch.symm) R.arms_ne
  have hfirstAlternate :
      alternate R.actionSwitch = bval R.firstArm := by
    simp [alternate, flipAt, hsecond, hopp]
  have hpathsAlternate :
      PathGrooves [R.runway, R.candy] alternate := by
    dsimp [alternate]
    change PathGrooves [R.runway, R.candy]
      ((LocalAction.flip R.actionSwitch).apply contact)
    exact hpaths.after_avoiding_action R.support_foreign
  have hcandyForward := R.candy_forward_trace alternate
    hfirstAlternate (pathGrooves_pair.mp hpathsAlternate).2
  have hcandyForwardGrooved : PassagesGrooved alternate
      ((R.mouth, R.firstArm) :: R.candy) := by
    exact hcandyForward.grooved_of_switchSimple (by
      have hs := R.simple
      unfold SwitchSimple at hs ⊢
      simp only [List.map_append] at hs
      exact (List.nodup_append.mp hs).2.1)

  have hsecondGrooveContact :
      arrive contact R.secondArm = (R.mouth, contact) :=
    R.secondArm_groove_of_selected contact hsecond
  have hsecondAlternate :
      arrive alternate R.secondArm = (R.mouth, contact) := by
    have hrepair := flipped_passage_forward_trailing
      hsecondGrooveContact R.secondArm_branch
    simpa [alternate, R.secondArm_switch] using hrepair
  have hback := physicalTrace_contact_retraces_prefix
    R.runwayTrace (pathGrooves_pair.mp hpaths).1 R.entryEdge
      hsecondAlternate
  have hback' : PhysicalTrace w (R.secondArm, alternate)
      ([(R.secondArm, R.mouth)] ++ reversePassages R.runway)
      (g, contact) := by
    simpa using hback
  obtain ⟨middle, hchange, hafter⟩ := hback'.split_append
  have hmiddleTongues : middle.2 = contact := by
    have hone : step w (R.secondArm, alternate) = some middle := by
      simpa [stepN] using hchange.sound
    have hparts := step_some_parts hone
    calc
      middle.2 = arrivedTongues (R.secondArm, alternate) := hparts.2
      _ = contact := by simp [arrivedTongues, hsecondAlternate]
  have hmiddle : middle = (middle.1, contact) := by
    apply Prod.ext
    · rfl
    · exact hmiddleTongues
  rw [hmiddle] at hchange hafter
  have hafterGrooved :
      PassagesGrooved contact (reversePassages R.runway) :=
    reversePassages_grooved (pathGrooves_pair.mp hpaths).1

  change ∀ d, d ≤ R.candy.length + 2 + R.runway.length →
    ∃ port phase,
      stepN w d (R.mouth, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact)
  intro d hd
  have hphase := PhysicalTrace.one_change_prefix_tongues
    hcandyForward hcandyForwardGrooved hchange hafter hafterGrooved
    (d := d) (by
      simp only [List.length_cons, reversePassages_length]
      omega)
  simpa [alternate] using hphase

/-- Pointwise strengthening of `reverse_candy_suffix_absorbs`.  Both possible
starting phases follow the same physical suffix.  Starting in `contact` makes
exactly the action-tongue repair at `firstArm`; starting in `alternate` makes
no change.  Thus every intermediate tongue vector is `contact` or
`alternate`, not merely the final endpoint. -/
theorem ManufacturedFlipReflector.reverse_candy_suffix_absorbs_twoPhases
    {w : Wiring} {e g : Nat}
    (R : ManufacturedFlipReflector w e g)
    (contact : Tongues)
    (hpaths : PathGrooves [R.runway, R.candy] contact)
    (hsecond : contact R.actionSwitch = bval R.secondArm)
    {before after : List Passage} {fresh p : Nat}
    (hoccurs : R.candy = before ++ (fresh, p) :: after) :
    let alternate := flipAt contact R.actionSwitch
    ∃ travel, 0 < travel ∧ travel ≤ R.toSupported.travel ∧
      stepN w travel (p, contact) = some (g, alternate) ∧
      stepN w travel (p, alternate) = some (g, alternate) ∧
      (∀ d, d ≤ travel → ∃ port phase,
        stepN w d (p, contact) = some (port, phase) ∧
          (phase = contact ∨ phase = alternate)) ∧
      (∀ d, d ≤ travel → ∃ port phase,
        stepN w d (p, alternate) = some (port, phase) ∧
          (phase = contact ∨ phase = alternate)) := by
  have hopp : bval R.secondArm = !(bval R.firstArm) :=
    branch_values_opposite R.firstArm_branch R.secondArm_branch
      (R.firstArm_switch.trans R.secondArm_switch.symm) R.arms_ne
  have hnotFirst : contact R.actionSwitch ≠ bval R.firstArm := by
    intro hfirst
    have heq : bval R.firstArm = bval R.secondArm :=
      hfirst.symm.trans hsecond
    rw [hopp] at heq
    cases hvalue : bval R.firstArm <;> simp [hvalue] at heq
  let alternate := flipAt contact R.actionSwitch
  have hfirstAlternate :
      alternate R.actionSwitch = bval R.firstArm := by
    simp [alternate, flipAt, hsecond, hopp]
  have hpathsAlternate :
      PathGrooves [R.runway, R.candy] alternate := by
    dsimp [alternate]
    change PathGrooves [R.runway, R.candy]
      ((LocalAction.flip R.actionSwitch).apply contact)
    exact hpaths.after_avoiding_action R.support_foreign

  let lead := R.runway ++
    (R.mouth, R.secondArm) :: reversePassages after
  let candyTail := reversePassages (before ++ [(fresh, p)])
  have hrouteSplit :
      (ManufacturedReflector.flip R).orientedRoute contact =
        lead ++ candyTail := by
    dsimp [lead, candyTail]
    simp [ManufacturedReflector.orientedRoute, hnotFirst,
      hoccurs, reversePassages_append, reversePassages,
      List.append_assoc]
  have hroute :=
    (ManufacturedReflector.flip R).orientedRoute_trace contact hpaths
  rw [hrouteSplit] at hroute
  obtain ⟨middle, _hlead, htail⟩ := hroute.split_append
  have hprefixData := R.reverse_prefix_to_candy_occurrence
    contact hpaths hsecond hoccurs
  have hleadExpected :
      PhysicalTrace w (e, contact) lead (p, contact) := by
    simpa [lead] using hprefixData.1
  have hmiddle : middle = (p, contact) := by
    have h₁ := _hlead.sound
    have h₂ := hleadExpected.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  have htailContact :
      PhysicalTrace w (p, contact) candyTail (R.firstArm, contact) := by
    simpa [ManufacturedReflector.orientedFinish, hnotFirst] using htail
  have htailForeign : ∀ passage ∈ candyTail,
      passageSwitch passage ≠ R.actionSwitch := by
    intro passage hpassage
    dsimp [candyTail] at hpassage
    obtain ⟨old, holdSegment, hpassageEq⟩ :=
      source_of_mem_reversePassages hpassage
    subst passage
    have holdCandy : old ∈ R.candy := by
      rw [hoccurs]
      rcases List.mem_append.mp holdSegment with holdBefore | holdLast
      · exact List.mem_append_left ((fresh, p) :: after) holdBefore
      · simp only [List.mem_singleton] at holdLast
        subst old
        exact List.mem_append_right before List.mem_cons_self
    have havoid := R.support_foreign R.candy (by simp) old holdCandy
    have hexit := R.candyTrace.passage_exit_switch old
      (List.mem_cons_of_mem _ holdCandy)
    have hswitch :
        passageSwitch (old.2, old.1) = passageSwitch old := by
      simp only [passageSwitch]
      exact hexit
    rw [hswitch]
    exact havoid
  have htailAlternate :
      PhysicalTrace w (p, alternate) candyTail
        (R.firstArm, alternate) :=
    htailContact.flip_unvisited htailForeign

  have hcandySourceGrooved :
      PassagesGrooved contact (before ++ [(fresh, p)]) := by
    intro passage hp
    apply (pathGrooves_pair.mp hpaths).2 passage
    rw [hoccurs]
    rcases List.mem_append.mp hp with hp | hp
    · exact List.mem_append_left ((fresh, p) :: after) hp
    · simp only [List.mem_singleton] at hp
      subst passage
      exact List.mem_append_right before List.mem_cons_self
  have htailContactGrooved : PassagesGrooved contact candyTail := by
    dsimp [candyTail]
    exact reversePassages_grooved hcandySourceGrooved
  have htailAlternateGrooved : PassagesGrooved alternate candyTail := by
    exact grooved_after_flip_other htailContactGrooved htailForeign

  have hfirstGrooveAlternate :
      arrive alternate R.firstArm = (R.mouth, alternate) :=
    R.firstArm_groove_of_selected alternate hfirstAlternate
  have hrunwayAlternate : PassagesGrooved alternate R.runway :=
    (pathGrooves_pair.mp hpathsAlternate).1
  have hflipBack : flipAt alternate R.actionSwitch = contact := by
    dsimp [alternate]
    exact flipAt_flipAt contact R.actionSwitch
  have hfirstContact :
      arrive contact R.firstArm = (R.mouth, alternate) := by
    have hrepair := flipped_passage_forward_trailing
      hfirstGrooveAlternate R.firstArm_branch
    rw [R.firstArm_switch, hflipBack] at hrepair
    exact hrepair
  have hreturnContact := physicalTrace_contact_retraces_prefix
    R.runwayTrace hrunwayAlternate R.entryEdge hfirstContact
  have hreturnContact' : PhysicalTrace w (R.firstArm, contact)
      ([(R.firstArm, R.mouth)] ++ reversePassages R.runway)
      (g, alternate) := by
    simpa using hreturnContact
  obtain ⟨contactMiddle, hcontactChange, hcontactAfter⟩ :=
    hreturnContact'.split_append
  have hcontactMiddleTongues : contactMiddle.2 = alternate := by
    have hone : step w (R.firstArm, contact) = some contactMiddle := by
      simpa [stepN] using hcontactChange.sound
    have hparts := step_some_parts hone
    calc
      contactMiddle.2 = arrivedTongues (R.firstArm, contact) := hparts.2
      _ = alternate := by simp [arrivedTongues, hfirstContact]
  have hcontactMiddle : contactMiddle = (contactMiddle.1, alternate) := by
    apply Prod.ext
    · rfl
    · exact hcontactMiddleTongues
  rw [hcontactMiddle] at hcontactChange hcontactAfter
  have hreturnAfterGrooved :
      PassagesGrooved alternate (reversePassages R.runway) :=
    reversePassages_grooved hrunwayAlternate

  have hreturnAlternate :
      PhysicalTrace w (R.firstArm, alternate)
        ((R.firstArm, R.mouth) :: reversePassages R.runway)
        (g, alternate) :=
    physicalTrace_contact_retraces_prefix R.runwayTrace
      hrunwayAlternate R.entryEdge hfirstGrooveAlternate
  have hreturnAlternate' : PhysicalTrace w (R.firstArm, alternate)
      ([(R.firstArm, R.mouth)] ++ reversePassages R.runway)
      (g, alternate) := by
    simpa using hreturnAlternate
  obtain ⟨alternateMiddle, halternateChange, halternateAfter⟩ :=
    hreturnAlternate'.split_append
  have halternateMiddleTongues : alternateMiddle.2 = alternate := by
    have hone : step w (R.firstArm, alternate) = some alternateMiddle := by
      simpa [stepN] using halternateChange.sound
    have hparts := step_some_parts hone
    calc
      alternateMiddle.2 = arrivedTongues (R.firstArm, alternate) := hparts.2
      _ = alternate := by simp [arrivedTongues, hfirstGrooveAlternate]
  have halternateMiddle : alternateMiddle =
      (alternateMiddle.1, alternate) := by
    apply Prod.ext
    · rfl
    · exact halternateMiddleTongues
  rw [halternateMiddle] at halternateChange halternateAfter

  let journey := candyTail ++
    (R.firstArm, R.mouth) :: reversePassages R.runway
  have hjourneyContact :
      PhysicalTrace w (p, contact) journey (g, alternate) := by
    simpa [journey] using htailContact.append hreturnContact
  have hjourneyAlternate :
      PhysicalTrace w (p, alternate) journey (g, alternate) := by
    simpa [journey] using htailAlternate.append hreturnAlternate
  refine ⟨journey.length, ?_, ?_, hjourneyContact.sound,
    hjourneyAlternate.sound, ?_, ?_⟩
  · dsimp [journey]
    simp only [List.length_append, List.length_cons]
    omega
  · change journey.length ≤ 2 * R.runway.length + R.candy.length + 2
    have hcandyLen : R.candy.length =
        before.length + 1 + after.length := by
      rw [hoccurs]
      simp
      omega
    have hjourneyLen : journey.length =
        before.length + 2 + R.runway.length := by
      dsimp [journey, candyTail]
      simp only [List.length_append, List.length_cons,
        List.length_nil, reversePassages_length]
      omega
    rw [hjourneyLen]
    omega
  · intro d hd
    have hlen : journey.length =
        candyTail.length + 1 + (reversePassages R.runway).length := by
      dsimp [journey]
      simp only [List.length_append, List.length_cons]
      omega
    have hphase := PhysicalTrace.one_change_prefix_tongues
      htailContact htailContactGrooved hcontactChange hcontactAfter
        hreturnAfterGrooved (d := d) (by
          rw [← hlen]
          exact hd)
    exact hphase
  · intro d hd
    have hlen : journey.length =
        candyTail.length + 1 + (reversePassages R.runway).length := by
      dsimp [journey]
      simp only [List.length_append, List.length_cons]
      omega
    have hphase := PhysicalTrace.one_change_prefix_tongues
      htailAlternate htailAlternateGrooved halternateChange
        halternateAfter hreturnAfterGrooved (d := d) (by
          rw [← hlen]
          exact hd)
    obtain ⟨port, phase, hrun, hphase⟩ := hphase
    rcases hphase with hphase | hphase
    · exact ⟨port, phase, hrun, Or.inr hphase⟩
    · exact ⟨port, phase, hrun, Or.inr hphase⟩

/-- The bounded pointwise certificate exposed by a facing-forward merge.  The
lead is the route prefix actually traversed by the train followed by the
absorbing reverse-candy suffix; it is bounded by the two reflector travels.
The complete infinite suffix has exactly the two named tongue phases. -/
structure FacingForwardPointwiseTail
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g) where
  contact : Tongues
  alternate : Tongues
  leadSteps : Nat
  lead_le : leadSteps ≤ A.toSupported.travel + B.toSupported.travel
  reached : stepN w leadSteps (g, B.activatedState) =
    some (g, alternate)
  tail_twoPhase : ∀ d, ∃ port phase,
    stepN w d (g, alternate) = some (port, phase) ∧
      (phase = alternate ∨ phase = contact)

/-- A facing-forward merge produces the bounded pointwise certificate
directly.  The proof replays the actual physical construction and separates
the only three possibilities for its approach: no action-switch contact,
mouth capture, or trailing self-repair. -/
theorem ManufacturedReflector.FacingForwardMerge.has_pointwiseTail
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.FacingForwardMerge B) :
    Nonempty (FacingForwardPointwiseTail A B) := by
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
    exact twoPhase_concat hprefixContact.sound hbeforePhase
      htailContactPhase' d (by simpa [loopSteps] using hd)

  have hbeforeLeRoute : before.length ≤
      (A.orientedRoute (ManufacturedReflector.flip R).activatedState).length := by
    rw [hrouteSplit]
    simp only [List.length_append, List.length_cons]
    omega
  have hbeforeLe : before.length ≤ A.toSupported.travel :=
    Nat.le_trans hbeforeLeRoute
      (A.orientedRoute_length_le_travel
        (ManufacturedReflector.flip R).activatedState)
  have hleadLe : loopSteps ≤
      A.toSupported.travel + (ManufacturedReflector.flip R).toSupported.travel := by
    dsimp [loopSteps]
    change before.length + tailTravel ≤
      A.toSupported.travel + R.toSupported.travel
    omega

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
      have hpriorAlternateGrooved : PassagesGrooved alternate prior := by
        dsimp [alternate]
        exact grooved_after_flip_other hpriorGrooved hpriorForeign
      have hpriorPhase : ∀ d, d ≤ prior.length → ∃ port phase,
          stepN w d (g, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = contact) :=
        groovedTrace_twoPhase hpriorAlternate hpriorAlternateGrooved

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
        exact twoPhase_concat hpriorAlternate.sound hpriorPhase
          hcapturePhase d hd
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
        exact twoPhase_concat htoContact htoContactPhase
          hcontactLoopPhase d (by simpa [period] using hd)
      have hallPhase := periodic_two_phase_prefix_tongues
        hperiodPositive hperiod hperiodPhase
      exact ⟨{
        contact := contact
        alternate := alternate
        leadSteps := loopSteps
        lead_le := hleadLe
        reached := hlead
        tail_twoPhase := hallPhase
      }⟩
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
      have hpriorAlternateGrooved : PassagesGrooved alternate prior := by
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
        exact twoPhase_concat hrepairPrefix.sound hrepairPrefixPhase
          htailContactPhase' d (by simpa [loopSteps] using hd)
      have hallPhase := periodic_two_phase_prefix_tongues
        hloopPositive hperiod hperiodPhase
      exact ⟨{
        contact := contact
        alternate := alternate
        leadSteps := loopSteps
        lead_le := hleadLe
        reached := hlead
        tail_twoPhase := hallPhase
      }⟩
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
            (phase = alternate ∨ phase = contact) :=
      groovedTrace_twoPhase hprefixAlternate hbeforeAlternateGrooved
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
      exact twoPhase_concat hprefixAlternate.sound
        hbeforeAlternatePhase htailAlternatePhase' d
          (by simpa [loopSteps] using hd)
    have hallPhase := periodic_two_phase_prefix_tongues
      hloopPositive hperiod hperiodPhase
    exact ⟨{
      contact := contact
      alternate := alternate
      leadSteps := loopSteps
      lead_le := hleadLe
      reached := hlead
      tail_twoPhase := hallPhase
    }⟩

/-- **StateLaw-facing charge theorem.**  If the concrete bounded lead of a
facing-forward tail has already been entered in the construction history,
then every sampled time in its entire infinite future is historical or is the
single `contact` vector.  The exceptional budget is exactly one. -/
theorem FacingForwardPointwiseTail.one_novelty_charge
    {w : Wiring} {g e N : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (S : FacingForwardPointwiseTail A B)
    (history : List (List Bool))
    (hleadHistorical : ∀ j, j ≤ S.leadSteps →
      restrictedTonguesAt w N (g, B.activatedState) j ∈ history)
    (times : List Nat) :
    NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
  have halternateHistorical :
      VectorCount.restrict N S.alternate ∈ history := by
    have hlead := hleadHistorical S.leadSteps (Nat.le_refl _)
    simpa [restrictedTonguesAt, tonguesAt, S.reached] using hlead
  refine ⟨[VectorCount.restrict N S.contact], by simp, ?_⟩
  intro k hk
  by_cases hklead : k ≤ S.leadSteps
  · exact List.mem_append_left _ (hleadHistorical k hklead)
  · let d := k - S.leadSteps
    have hdecomp : k = S.leadSteps + d := by
      dsimp [d]
      omega
    obtain ⟨port, phase, htail, hphase⟩ := S.tail_twoPhase d
    have hrun : stepN w k (g, B.activatedState) =
        some (port, phase) := by
      rw [hdecomp, stepN_add, S.reached]
      exact htail
    have hvector :
        restrictedTonguesAt w N (g, B.activatedState) k =
          VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hrun]
    rw [hvector]
    rcases hphase with rfl | rfl
    · exact List.mem_append_left _ halternateHistorical
    · exact List.mem_append_right _ (by simp)

/-- Distinct-vector form of the charge theorem, ready for the final StateLaw
bookkeeping: samples taken anywhere in the facing-forward future contribute at
most one vector beyond the supplied construction history. -/
theorem FacingForwardPointwiseTail.distinct_samples_le_history_add_one
    {w : Wiring} {g e N : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (S : FacingForwardPointwiseTail A B)
    (history : List (List Bool))
    (hleadHistorical : ∀ j, j ≤ S.leadSteps →
      restrictedTonguesAt w N (g, B.activatedState) j ∈ history)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ history.length + 1 := by
  exact noveltyCoverOn_distinct_count
    (S.one_novelty_charge history hleadHistorical times) hnd

/-- Direct public extraction: every facing-forward merge supplies both the
bounded pointwise tail and its one-vector charge law.  There is no residual
eventual-periodicity or novelty hypothesis in this theorem. -/
theorem ManufacturedReflector.FacingForwardMerge.bounded_pointwise_charge
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.FacingForwardMerge B) :
    ∃ S : FacingForwardPointwiseTail A B,
      ∀ (N : Nat) (history : List (List Bool)),
        (∀ j, j ≤ S.leadSteps →
          restrictedTonguesAt w N (g, B.activatedState) j ∈ history) →
        ∀ times : List Nat,
          NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
  obtain ⟨S⟩ := hmerge.has_pointwiseTail
  exact ⟨S, fun _N history hlead times =>
    S.one_novelty_charge history hlead times⟩

end GeneralN
