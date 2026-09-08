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
/-- The reverse candy suffix absorbs a fault pointwise.  Both possible
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
    ∃ travel, 0 < travel ∧
      ∀ current, (current = contact ∨ current = alternate) →
        stepN w travel (p, current) = some (g, alternate) ∧
        ∀ d, d ≤ travel → ∃ port phase,
          stepN w d (p, current) = some (port, phase) ∧
            (phase = contact ∨ phase = alternate) := by
  let alternate := flipAt contact R.actionSwitch
  have hopp := branch_values_opposite R.firstArm_branch R.secondArm_branch
    (R.firstArm_switch.trans R.secondArm_switch.symm) R.arms_ne
  have hfirst : alternate R.actionSwitch = bval R.firstArm := by
    simp [alternate, flipAt, hsecond, hopp]
  have hpathsAlternate : PathGrooves [R.runway, R.candy] alternate := by
    change PathGrooves [R.runway, R.candy] ((LocalAction.flip R.actionSwitch).apply contact)
    exact hpaths.after_avoiding_action R.support_foreign
  have hfirstAlternate := R.firstArm_groove_of_selected alternate hfirst
  have hfirstContact : arrive contact R.firstArm = (R.mouth, alternate) := by
    simpa [alternate, R.firstArm_switch, flipAt_flipAt] using
      flipped_passage_forward_trailing hfirstAlternate R.firstArm_branch
  let candyTail := (p, fresh) :: reversePassages before
  have hsplit : (R.mouth, R.secondArm) :: reversePassages R.candy =
      ((R.mouth, R.secondArm) :: reversePassages after) ++ candyTail := by
    simp [candyTail, hoccurs, reversePassages, List.append_assoc]
  have hreverse := R.candy_reverse_trace contact hsecond (pathGrooves_pair.mp hpaths).2
  rw [hsplit] at hreverse
  obtain ⟨middle, _, htail⟩ := hreverse.split_append
  have hstart : middle.1 = p := htail.head_arrive.1
  have hgrooved : ∀ current, (current = contact ∨ current = alternate) →
      PassagesGrooved current candyTail := by
    intro current hc
    have hg : PassagesGrooved current R.candy := by
      rcases hc with rfl | rfl
      · exact (pathGrooves_pair.mp hpaths).2
      · exact (pathGrooves_pair.mp hpathsAlternate).2
    have hprefix : PassagesGrooved current (before ++ [(fresh, p)]) := by
      intro passage hp
      apply hg passage
      rw [hoccurs]
      grind
    simpa [candyTail, reversePassages] using reversePassages_grooved hprefix
  let travel := candyTail.length + (R.runway.length + 1)
  refine ⟨travel, by simp [travel]; omega, ?_⟩
  intro current hc
  have hg := hgrooved current hc
  have ht : PhysicalTrace w (p, current) candyTail (R.firstArm, current) := by
    simpa only [hstart] using htail.replay_grooved current hg
  have ha : arrive current R.firstArm = (R.mouth, alternate) := by
    rcases hc with rfl | rfl
    · exact hfirstContact
    · exact hfirstAlternate
  have hrunway := (pathGrooves_pair.mp hpathsAlternate).1
  have hb := physicalTrace_contact_retraces_prefix R.runwayTrace hrunway R.entryEdge ha
  constructor
  · simpa [travel, reversePassages_length] using (ht.append hb).sound
  · apply stepN_cover_append ht.sound
    · intro d hd
      obtain ⟨port, hr⟩ := ht.grooved_prefix_tongues current hg hd
      exact ⟨port, current, hr, hc⟩
    · intro d hd
      obtain ⟨port, hr⟩ := (physicalTrace_contact_retraces_prefix_pointwise
        R.runwayTrace hrunway R.entryEdge ha) d hd
      refine ⟨port, _, hr, ?_⟩
      split
      · exact hc
      · exact Or.inr rfl


end GeneralN
