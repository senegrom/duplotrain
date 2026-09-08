import ManufacturedPairNovelty
import TrackGlobalRepair

/-!
# A one-bit invariant for candy splices

After the new splice tongue is latched, only the old reflector action can
change. The closed spatial route never faces that variable switch, so either
of its values follows the same route. Replaying the route in this invariant
proves the all-time two-vector cover without separating approaches that miss
the old action from approaches that repair it, or computing either period.

Everything is over raw `Wiring` / `stepN`; no finite-switch bound is needed.
-/

namespace GeneralN

/-- A grooved route that never faces the variable switch preserves its
one-bit family. Branch entries may set that bit but cannot select a different
exit; all other passages leave the entire tongue vector unchanged. -/
theorem passages_preserve_flip_pair
    {base : Tongues} {j : Nat} {route : List Passage}
    (hgrooved : PassagesGrooved base route)
    (hnoFacing : ∀ passage ∈ route, passageSwitch passage = j →
      passage.1 % 3 ≠ 0) :
    ∀ passage ∈ route, ∀ phase, (phase = base ∨ phase = flipAt base j) →
      ∃ next, arrive phase passage.1 = (passage.2, next) ∧
        (next = base ∨ next = flipAt base j) := by
  intro passage hp phase hphase
  have hforward := groove_forward (hgrooved passage hp)
  rcases hphase with heq | heq <;> subst phase
  · exact ⟨base, hforward, Or.inl rfl⟩
  · by_cases hj : passageSwitch passage = j
    · rw [← hj]
      exact ⟨base, flipped_passage_forward_trailing hforward (hnoFacing passage hp hj),
        Or.inl rfl⟩
    · exact ⟨flipAt base j, arrive_flip_other hforward hj, Or.inr rfl⟩

/-- A strict candy splice repeats a spatial route with only the old action
coordinate free. That coordinate is never entered facing, so its value cannot
change the route. Whether the approach misses it or repairs it is irrelevant:
every lap stays in the same two-vector family. No period is computed. -/
theorem manufactured_flip_candy_splice_all_two_phases
    {w : Wiring} {g e outside entry mouth returnPort : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {oldPrefix oldTail approach : List Passage}
    (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (htail : PhysicalTrace w (outside, state) oldTail
      ((ManufacturedReflector.flip R).orientedFinish state, state))
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (hentryBranch : entry % 3 ≠ 0)
    {old : Passage} (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨ (entry, mouth) = (old.2, old.1))
    (hentryGrooved : arrive state entry = (mouth, state))
    (happroach : PhysicalTrace w (g, state) approach (returnPort, state))
    (happroachGrooved : PassagesGrooved state approach)
    (happroachForeignNew : ∀ passage ∈ approach, passageSwitch passage ≠ mouth / 3)
    (hcrossed : arrive state returnPort = (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (harms : entry ≠ returnPort) :
    ∀ d, ∃ port phase,
      stepN w d (outside, flipAt state (mouth / 3)) = some (port, phase) ∧
        (phase = flipAt state (mouth / 3) ∨
          phase = flipAt (flipAt state (mouth / 3)) R.actionSwitch) := by
  let finish := (ManufacturedReflector.flip R).orientedFinish state
  let completion := oldTail ++ ((finish, R.mouth) :: reversePassages R.runway)
  let newState := flipAt state (mouth / 3)
  let bothState := flipAt newState R.actionSwitch
  let allowed := fun phase => phase = newState ∨ phase = bothState
  have hentryNew : entry / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state entry
    rw [hentryGrooved] at hs
    exact hs.symm
  have hnewOld : mouth / 3 ≠ R.actionSwitch := by
    intro heq
    exact R.candy_entry_foreign_action hold horientation (hentryNew.trans heq)
  have hreturnNew : returnPort / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state returnPort
    rw [hcrossed] at hs
    exact hs.symm
  have hcomm : flipAt (flipAt state R.actionSwitch) (mouth / 3) = bothState :=
    flipAt_comm (Ne.symm hnewOld)
  have hcompletionData := R.candy_completion_foreign state hpaths
    hsplit htail hnotRunway hold horientation
  have hforeignNew : ∀ passage ∈ completion, passageSwitch passage ≠ mouth / 3 := by
    intro passage hp heq
    exact hcompletionData.2 passage hp (heq.trans hentryNew.symm)
  have htailForeign := R.candy_tail_foreign_action state hsplit hnotRunway hentryBranch
  have hroute := (ManufacturedReflector.flip R).orientedRoute_trace state hpaths
  have hrouteGrooved := hroute.grooved_of_switchSimple
    ((ManufacturedReflector.flip R).orientedRoute_simple state)
  have htailGrooved : PassagesGrooved state oldTail := by
    intro passage hp
    apply hrouteGrooved passage
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  have hrunwayGrooved : PassagesGrooved state R.runway := (pathGrooves_pair.mp hpaths).1
  have hrunwayForeign := R.support_foreign R.runway (by simp)
  have hreverseForeign : ∀ passage ∈ reversePassages R.runway,
      passageSwitch passage ≠ R.actionSwitch := by
    intro passage hp
    obtain ⟨old, hold, rfl⟩ := source_of_mem_reversePassages hp
    rw [show passageSwitch (old.2, old.1) = passageSwitch old from
      R.runwayTrace.passage_exit_switch old hold]
    exact hrunwayForeign old hold
  have hreturn := R.oriented_finish_arrive state
  have hfinishSwitch : finish / 3 = R.actionSwitch := by
    have hs := arrive_exit_switch state finish
    rw [hreturn] at hs
    exact hs.symm
  have hfinishBranch : finish % 3 ≠ 0 :=
    (changed_arrival_is_trailing hreturn (by
      rw [hfinishSwitch]
      simp [flipAt])).1
  have hreturnGroove := arrive_back state finish
  rw [hreturn] at hreturnGroove
  have hlatchedGrooved : PassagesGrooved (flipAt state R.actionSwitch) completion := by
    intro passage hp
    rcases List.mem_append.mp hp with ht | hr
    · exact grooved_after_flip_other htailGrooved htailForeign passage ht
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hreturnGroove
      · exact reversePassages_grooved
          (grooved_after_flip_other hrunwayGrooved hrunwayForeign) passage hr
  have hcompletionGrooved : PassagesGrooved bothState completion := by
    rw [← hcomm]
    exact grooved_after_flip_other hlatchedGrooved hforeignNew
  have hcompletionNoFacing : ∀ passage ∈ completion,
      passageSwitch passage = R.actionSwitch → passage.1 % 3 ≠ 0 := by
    intro passage hp heq
    rcases List.mem_append.mp hp with ht | hr
    · exact (htailForeign passage ht heq).elim
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hfinishBranch
      · exact (hreverseForeign passage hr heq).elim
  have hcompletionLocal : ∀ passage ∈ completion, ∀ phase, allowed phase →
      ∃ next, arrive phase passage.1 = (passage.2, next) ∧ allowed next := by
    simpa only [allowed, bothState, flipAt_flipAt, or_comm] using
      passages_preserve_flip_pair hcompletionGrooved hcompletionNoFacing
  have hcompletionTrace : PhysicalTrace w (outside, bothState) completion (g, bothState) :=
    hcompletionData.1.replay_grooved bothState hcompletionGrooved

  have happroachNew := happroach.flip_unvisited happroachForeignNew
  have happroachGroovedNew := grooved_after_flip_other happroachGrooved happroachForeignNew
  have hback := arrive_back state returnPort
  rw [hcrossed] at hback
  have hcontactNew : arrive newState returnPort = (mouth, newState) := groove_forward hback
  have hcontact := PhysicalTrace.cons hcontactNew hmouthLink (PhysicalTrace.nil _)
  have happroachContact := happroachNew.append hcontact
  have hrightGrooved : PassagesGrooved newState (approach ++ [(returnPort, mouth)]) := by
    intro passage hp
    rcases List.mem_append.mp hp with ha | hc
    · exact happroachGroovedNew passage ha
    · have : passage = (returnPort, mouth) := List.mem_singleton.mp hc
      subst passage
      exact hback
  have hrightNoFacing : ∀ passage ∈ approach ++ [(returnPort, mouth)],
      passageSwitch passage = R.actionSwitch → passage.1 % 3 ≠ 0 := by
    intro passage hp heq hface
    rcases List.mem_append.mp hp with ha | hc
    · exact R.facing_approach_to_candy_splice_impossible state hpaths
        hsplit hnotRunway hentryBranch happroach happroachGrooved
        happroachForeignNew hcrossed harms ha heq hface
    · have : passage = (returnPort, mouth) := List.mem_singleton.mp hc
      subst passage
      exact hnewOld (hreturnNew.symm.trans heq)
  have hrightLocal := passages_preserve_flip_pair hrightGrooved hrightNoFacing
  obtain ⟨last, hright, _, _⟩ := happroachContact.replay_preserving allowed
    hrightLocal (u := bothState) (Or.inr rfl)
  have hloop := hcompletionTrace.append hright
  apply hloop.spatial_loop_invariant allowed (by
    simp only [List.length_append, List.length_singleton]
    omega)
  · intro passage hp
    rcases List.mem_append.mp hp with hc | ha
    · exact hcompletionLocal passage hc
    · exact hrightLocal passage ha
  · exact Or.inl rfl


end GeneralN
