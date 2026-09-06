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
    rcases hphase with hphase | hphase <;>
      exact ⟨port, phase, hrun, Or.inr hphase⟩

end GeneralN
