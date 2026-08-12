import StateLawCoefficientOneTop
import OldContactContinuation
import OneReflectorContinuation

/-!
# Partial second-run contact dichotomy

This file treats an arbitrary switch-simple continuation after one completed
manufactured reflector.  It does not assume that the continuation completes a
second reflector.  The canonical contact is selected against the union of the
old exploration and the fresh continuation.

Everything is symbolic in `N`; no finite enumeration is used.
-/

namespace GeneralN

/-- The forward-contact splice uses only a simple partial approach.  The
completed second reflector in the older API supplied no additional dynamic
information: its only uses were simplicity of the approach and the trace to
the contact. -/
theorem partial_forward_contact_active_lead
    {w : Wiring} {g e p x : Nat} {base : Tongues}
    {A : ManufacturedReflector w g e}
    {approach suffix : List Passage} {u v : Tongues}
    {oriented : Passage} {repaired : Tongues}
    (hsimple : SwitchSimple (approach ++ (p, x) :: suffix))
    (happroach : PhysicalTrace w (e, base) approach (p, u))
    (hpaths : PathGrooves A.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3))
    (horiented : oriented ∈ A.orientedRoute u)
    (horientedGroove : arrive u oriented.2 = (oriented.1, u))
    (horientedSwitch : passageSwitch oriented = p / 3)
    (hforward : x = oriented.2)
    (hrepair : arrive v oriented.1 = (oriented.2, repaired))
    (hrestored : arrive repaired oriented.2 = (oriented.1, repaired)) :
    ∃ (entry mouth returnPort outside : Nat)
        (oldPrefix oldTail candy : List Passage) (tailSteps : Nat),
      (entry, mouth) ∈ A.orientedRoute u ∧
      A.orientedRoute u = oldPrefix ++ (entry, mouth) :: oldTail ∧
      PhysicalTrace w (outside, u) oldTail (A.orientedFinish u, u) ∧
      PhysicalTrace w (e, u) approach (returnPort, u) ∧
      SwitchSimple approach ∧
      PassagesGrooved u approach ∧
      (∀ passage ∈ approach, passageSwitch passage ≠ mouth / 3) ∧
      candy = reversePassages oldPrefix ++ approach ∧
      entry % 3 ≠ 0 ∧ mouth % 3 = 0 ∧
      w.link mouth = some outside ∧ entry ≠ returnPort ∧
      PassagesGrooved u ((mouth, entry) :: candy) ∧
      PhysicalTrace w (mouth, u) ((mouth, entry) :: candy)
        (returnPort, u) ∧
      arrive u returnPort = (mouth, flipAt u (mouth / 3)) ∧
      PathGrooves A.toSupported.paths u ∧
      PassagesGrooved u candy ∧
      (∀ passage ∈ candy, passageSwitch passage ≠ mouth / 3) ∧
      IsReflector w mouth outside (candy.length + 2)
        (fun state => PassagesGrooved state candy)
        (fun state => flipAt state (mouth / 3)) ∧
      stepN w (approach.length + 1) (e, base) =
        some (outside, flipAt u (mouth / 3)) ∧
      stepN w tailSteps (outside, u) =
        some (e, A.toSupported.action.apply u) := by
  rcases oriented with ⟨a, s⟩
  simp only at horiented horientedGroove hforward hrepair hrestored
  subst x
  obtain ⟨hpBranch, hsEq, _hv, _hback⟩ :=
    changed_arrival_is_trailing harrive hchanged
  have hsStem : s % 3 = 0 := by
    rw [hsEq]
    omega
  have hsp : s / 3 = p / 3 := by
    rw [hsEq]
    omega
  have hsa : s / 3 = a / 3 := by
    have hswitch := arrive_exit_switch u s
    rw [horientedGroove] at hswitch
    exact hswitch.symm
  have haBranch : a % 3 ≠ 0 := by
    have haEq : branchPort (s / 3) (u (s / 3)) = a := by
      unfold arrive at horientedGroove
      rw [if_pos hsStem] at horientedGroove
      exact congrArg Prod.fst horientedGroove
    intro haStem
    cases hu : u (s / 3) <;>
      simp [branchPort, hu] at haEq <;> omega
  have hap : a ≠ p := by
    intro hEq
    subst p
    have holdForward := groove_forward horientedGroove
    rw [harrive] at holdForward
    have huv : v = u := congrArg Prod.snd holdForward
    apply hchanged
    rw [huv]
  obtain ⟨oldPrefix, oldTail, hrouteSplit⟩ :=
    List.append_of_mem horiented
  have hroute := A.orientedRoute_trace u hpaths
  have hrouteSimple := A.orientedRoute_simple u
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  have hOldPrefixData := simple_grooved_trace_prefix_to_occurrence
    hroute hrouteSplit hrouteGrooved hrouteSimple
  have hOldPrefixGrooved : PassagesGrooved u oldPrefix := by
    intro passage hp
    exact hrouteGrooved passage (by
      rw [hrouteSplit]
      exact List.mem_append_left _ hp)
  have hApproachSimple : SwitchSimple approach := by
    unfold SwitchSimple at hsimple ⊢
    simp only [List.map_append, List.map_cons] at hsimple
    exact (List.nodup_append.mp hsimple).1
  have hApproachGrooved : PassagesGrooved u approach :=
    happroach.grooved_of_switchSimple hApproachSimple
  have hApproachForeign :
      ∀ passage ∈ approach, passageSwitch passage ≠ p / 3 := by
    unfold SwitchSimple at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    have hparts := List.nodup_append.mp hsimple
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (p, s)) (by simp)
    exact hne (by simpa [passageSwitch] using hEq)
  let candy := reversePassages oldPrefix ++ approach
  have hCandyGrooved : PassagesGrooved u candy := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    · exact reversePassages_grooved hOldPrefixGrooved passage hold
    · exact hApproachGrooved passage hnew
  have hCandyForeign :
      ∀ passage ∈ candy, passageSwitch passage ≠ s / 3 := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    · have hmapped : passageSwitch passage ∈
          (reversePassages oldPrefix).map passageSwitch :=
        List.mem_map.mpr ⟨passage, hold, rfl⟩
      have hmap := map_passageSwitch_reversePassages hOldPrefixData.1
      rw [hmap] at hmapped
      have horiginal : passageSwitch passage ∈
          oldPrefix.map passageSwitch := List.mem_reverse.mp hmapped
      obtain ⟨old, holdMem, holdEq⟩ := List.mem_map.mp horiginal
      intro hmouth
      apply hOldPrefixData.2 old holdMem
      exact holdEq.trans (hmouth.trans hsa)
    · intro hmouth
      apply hApproachForeign passage hnew
      exact hmouth.trans hsp
  have hback := physicalTrace_contact_retraces_prefix
    hOldPrefixData.1 hOldPrefixGrooved A.entryEdge horientedGroove
  have hforwardTrace := happroach.replay_grooved u hApproachGrooved
  have hsplice :
      PhysicalTrace w (s, u) ((s, a) :: candy) (p, u) := by
    simpa [candy, List.append_assoc] using
      hback.append hforwardTrace
  have hSpliceGrooved : PassagesGrooved u ((s, a) :: candy) := by
    intro passage hpassage
    rcases List.mem_cons.mp hpassage with hhead | htail
    · simpa [hhead] using groove_forward horientedGroove
    · exact hCandyGrooved passage htail
  have hroute' := hroute
  rw [hrouteSplit] at hroute'
  obtain ⟨middle, hOldBefore, hOldAfter⟩ := hroute'.split_append
  have hMiddle : middle = (a, u) := by
    have h1 := hOldBefore.sound
    have h2 := hOldPrefixData.1.sound
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  subst middle
  cases hOldAfter with
  | @cons _ _ outside _ oldAfter _ _ hOldArrive hmouth hOldRest =>
      have hOldAfterState : oldAfter = u := by
        have hforwardOld := groove_forward horientedGroove
        rw [hOldArrive] at hforwardOld
        exact congrArg Prod.snd hforwardOld
      subst oldAfter
      have hcontactTrace :
          PhysicalTrace w (a, u) [(a, s)] (outside, u) :=
        PhysicalTrace.cons (groove_forward horientedGroove)
          hmouth (PhysicalTrace.nil _)
      have hlead := hOldPrefixData.1.append hcontactTrace
      have hleadSplit : A.orientedRoute u =
          (oldPrefix ++ [(a, s)]) ++ oldTail := by
        rw [hrouteSplit]
        simp [List.append_assoc]
      obtain ⟨tailSteps, _hlen, hcomplete⟩ :=
        A.complete_after_oriented_prefix u hpaths hleadSplit hlead
      have hflip : v = flipAt u (s / 3) := by
        have hv := changed_arrival_eq_flipAt harrive hchanged
        simpa [hsp] using hv
      have hone : stepN w 1 (p, u) = some (outside, v) := by
        simp [stepN, step, harrive, hmouth]
      have hreach :
          stepN w (approach.length + 1) (e, base) =
            some (outside, flipAt u (s / 3)) := by
        rw [stepN_add, happroach.sound]
        simp only [Option.bind_some]
        rw [hone, hflip]
      have hcrossed : arrive u p = (s, flipAt u (s / 3)) := by
        rw [harrive, hflip]
      refine ⟨a, s, p, outside, oldPrefix, oldTail,
        candy, tailSteps, horiented, hrouteSplit, hOldRest,
        hforwardTrace, hApproachSimple, hApproachGrooved,
        (by
          intro passage hpassage
          simpa [hsp] using hApproachForeign passage hpassage),
        rfl, haBranch, hsStem, hmouth, hap, hSpliceGrooved,
        hsplice, hcrossed, hpaths, hCandyGrooved,
        hCandyForeign, ?_, hreach, hcomplete⟩
      exact stem_lobe_isReflector_foreign w candy
        hsStem haBranch hpBranch hsa hsp hap hCandyForeign
        hsplice.linked hsplice.last_link hmouth

/-- A forward first-changing contact into a flip reflector has at most two
new restricted vectors after the coefficient-one contact history.  This is
the partial-continuation analogue of the completed-second-reflector theorem.
-/
theorem SimpleContinuationChangedContact.forward_flip_two_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair : arrive C.nextState C.oriented.1 =
      (C.oriented.2, repaired))
    (hrestored : arrive repaired C.oriented.2 =
      (C.oriented.1, repaired))
    (times : List Nat) :
    NoveltyCoverOn w N
      (e, (ManufacturedReflector.flip R).activatedState)
      times (C.compressedLead N) 2 := by
  have hsimple :
      SwitchSimple (C.approach ++ (C.p, C.x) :: C.suffix) := by
    rw [← C.split]
    exact C.full_simple
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, _hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeignNew, hLobe, hreach,
      _hcomplete⟩ :=
    partial_forward_contact_active_lead
      (A := ManufacturedReflector.flip R) hsimple
      C.approach_trace C.old_grooves C.arrive_eq C.changed
      C.oriented_mem C.oriented_groove C.oriented_switch
      hforward hrepair hrestored
  let K := C.approach.length + 1
  let state := C.contactState
  let alternate := flipAt state (mouth / 3)
  have hreach' :
      stepN w K
        (e, (ManufacturedReflector.flip R).activatedState) =
        some (outside, alternate) := by
    simpa [K, state, alternate] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.compressedLead N := by
    simpa [hnextAlternate] using C.next_mem_compressedLead (N := N)
  have hstateHistorical :
      VectorCount.restrict N state ∈ C.compressedLead N := by
    simpa [state] using C.contact_mem_compressedLead (N := N)
  have hleadHistorical : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N
        (e, (ManufacturedReflector.flip R).activatedState) j ∈
          C.compressedLead N := by
    intro j _hj hjK
    exact C.mem_compressedLead_of_approach (N := N) (by
      dsimp [K] at hjK
      omega)
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ := List.append_of_mem hrunway
    obtain ⟨D, _hDAction, hEntryOldNe, hDpaths,
        hNewAvoidsDRaw, _htravel⟩ :=
      R.suffix_after_runway_passage_with_travel state hRpaths
        hrunwaySplit hmouthLink
    have hentrySwitch : entry / 3 = mouth / 3 := by
      have hheadGroove : arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hswitch := arrive_exit_switch state entry
      rw [hheadGroove] at hswitch
      exact hswitch.symm
    have hActionsNe : mouth / 3 ≠ D.actionSwitch := by
      rw [← hentrySwitch]
      exact hEntryOldNe
    have hNewAvoidsD :
        (LocalAction.flip (mouth / 3)).Avoids D.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsDRaw
    by_cases hcontact : ∃ passage ∈ candy,
        passageSwitch passage = D.actionSwitch
    · apply manufactured_flip_arbitrary_lobe_absolute_two_novelty
        D state hDpaths hNewAvoidsD hentryBranch hentrySwitch
        hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
        hmouthLink hcontact hreach' times (C.compressedLead N)
        hentryHistorical hstateHistorical
      exact hleadHistorical
    · have hCandyForeignOld : ∀ passage ∈ candy,
          passageSwitch passage ≠ D.actionSwitch := by
        intro passage hp hEq
        exact hcontact ⟨passage, hp, hEq⟩
      apply manufactured_suffix_explicit_lobe_absolute_two_novelty
        D state hDpaths hNewAvoidsD hActionsNe hentryBranch
        hentrySwitch hfullGrooved hfullTrace hcrossed
        hCandyForeignNew hCandyForeignOld hLobe hmouthLink
        hreach' times (C.compressedLead N) hentryHistorical
        hstateHistorical
      exact hleadHistorical
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        hentryOld hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    have hone := manufactured_flip_candy_splice_absolute_one_novelty
      R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
      hold horientation hentryGrooved hApproachReplay
      hApproachGrooved hApproachForeign hcrossed hmouthLink harms
      hreach' N (C.compressedLead N) hentryHistorical times
      hleadHistorical
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩

private theorem partialContact_twoPhase_concat
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

/-- A forward first-changing contact into a stay reflector is trapped in a
literal two-phase orbit. -/
theorem SimpleContinuationChangedContact.forward_stay_two_phase_tail
    {w : Wiring} {g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.stay R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair : arrive C.nextState C.oriented.1 =
      (C.oriented.2, repaired))
    (hrestored : arrive repaired C.oriented.2 =
      (C.oriented.1, repaired)) :
    ∃ outside mouth,
      stepN w (C.approach.length + 1)
        (e, (ManufacturedReflector.stay R).activatedState) =
          some (outside,
            flipAt C.contactState (mouth / 3)) ∧
      ∀ d, ∃ port phase,
        stepN w d
          (outside, flipAt C.contactState (mouth / 3)) =
            some (port, phase) ∧
        (phase = flipAt C.contactState (mouth / 3) ∨
          phase = C.contactState) := by
  have hsimple :
      SwitchSimple (C.approach ++ (C.p, C.x) :: C.suffix) := by
    rw [← C.split]
    exact C.full_simple
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, _hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete⟩ :=
    partial_forward_contact_active_lead
      (A := ManufacturedReflector.stay R) hsimple
      C.approach_trace C.old_grooves C.arrive_eq C.changed
      C.oriented_mem C.oriented_groove C.oriented_switch
      hforward hrepair hrestored
  let k := mouth / 3
  let alternate := flipAt C.contactState k
  have hCandyFlip : PassagesGrooved alternate candy := by
    dsimp [alternate, k]
    exact grooved_after_flip_other hCandy hCandyForeign
  have hOldRoute :=
    (ManufacturedReflector.stay R).orientedRoute_trace
      C.contactState hRpaths
  have hOldSimple :=
    (ManufacturedReflector.stay R).orientedRoute_simple C.contactState
  have hOldGrooved := hOldRoute.grooved_of_switchSimple hOldSimple
  have hOldForward : arrive C.contactState entry =
      (mouth, C.contactState) :=
    groove_forward (hOldGrooved (entry, mouth) hentryOld)
  have hentryMouthSwitch : entry / 3 = mouth / 3 := by
    have hswitch := arrive_exit_switch C.contactState entry
    rw [hOldForward] at hswitch
    exact hswitch.symm
  have hallAfter : ∀ d, ∃ port phase,
      stepN w d (outside, alternate) = some (port, phase) ∧
      (phase = alternate ∨ phase = C.contactState) := by
    change (entry, mouth) ∈ R.runway ++ [(R.mouth, R.arm)] at hentryOld
    rcases List.mem_append.mp hentryOld with hrunway | hcore
    · obtain ⟨before, after, hsplit⟩ := List.append_of_mem hrunway
      obtain ⟨D, hDpaths, hAvoid⟩ :=
        R.suffix_after_runway_passage C.contactState hRpaths
          hsplit hmouthLink
      have hAvoid' :
          (LocalAction.flip k).Avoids D.toSupported.paths := by
        dsimp [k]
        simpa [hentryMouthSwitch] using hAvoid
      have hDalt : PathGrooves D.toSupported.paths alternate := by
        dsimp [alternate]
        exact hDpaths.after_avoiding_action hAvoid'
      let dTravel := D.toSupported.travel
      let lTravel := candy.length + 2
      have hDaltEnd :
          stepN w dTravel (outside, alternate) =
            some (mouth, alternate) := by
        dsimp [dTravel]
        exact (D.toSupported.run alternate hDalt).1
      have hDstateEnd :
          stepN w dTravel (outside, C.contactState) =
            some (mouth, C.contactState) := by
        dsimp [dTravel]
        exact (D.toSupported.run C.contactState hDpaths).1
      have hDaltPhase : ∀ d, d ≤ dTravel → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, hrun⟩ := D.travel_state_stepN alternate hDalt (by
          simpa [dTravel, ManufacturedReflector.toSupported,
            ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, alternate, hrun, Or.inl rfl⟩
      have hDstatePhase : ∀ d, d ≤ dTravel → ∃ port phase,
          stepN w d (outside, C.contactState) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, hrun⟩ :=
          D.travel_state_stepN C.contactState hDpaths (by
            simpa [dTravel, ManufacturedReflector.toSupported,
              ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, C.contactState, hrun, Or.inr rfl⟩
      have hReverseEnd :
          stepN w lTravel (mouth, alternate) =
            some (outside, C.contactState) := by
        have h := (hLobe alternate hCandyFlip).1
        change stepN w lTravel (mouth, alternate) =
          some (outside, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd :
          stepN w lTravel (mouth, C.contactState) =
            some (outside, alternate) := by
        have h := (hLobe C.contactState hCandy).1
        simpa [lTravel, alternate, k] using h
      have hReversePhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (mouth, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          hentryBranch hentryMouthSwitch hfullGrooved hfullTrace
          hcrossed hCandyForeign hmouthLink
          (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (mouth, C.contactState) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, phase, hrun, hphase⟩ :=
          explicit_lobe_travel_two_phase
            hfullGrooved hfullTrace hcrossed hmouthLink
            (by simpa [lTravel] using hd)
        refine ⟨port, phase, hrun, ?_⟩
        dsimp [alternate, k]
        rcases hphase with h | h
        · exact Or.inr h
        · exact Or.inl h
      let half := dTravel + lTravel
      have hHalfAlt : stepN w half (outside, alternate) =
          some (outside, C.contactState) := by
        dsimp [half]
        rw [stepN_add, hDaltEnd]
        exact hReverseEnd
      have hHalfState : stepN w half (outside, C.contactState) =
          some (outside, alternate) := by
        dsimp [half]
        rw [stepN_add, hDstateEnd]
        exact hForwardEnd
      have hHalfAltPhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact partialContact_twoPhase_concat
          hDaltEnd hDaltPhase hReversePhase d
          (by simpa [half] using hd)
      have hHalfStatePhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, C.contactState) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact partialContact_twoPhase_concat
          hDstateEnd hDstatePhase hForwardPhase d
          (by simpa [half] using hd)
      let period := half + half
      have hperiod : stepN w period (outside, alternate) =
          some (outside, alternate) := by
        dsimp [period]
        rw [stepN_add, hHalfAlt]
        exact hHalfState
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact partialContact_twoPhase_concat
          hHalfAlt hHalfAltPhase hHalfStatePhase d
          (by simpa [period] using hd)
      have hpositive : 0 < period := by
        have hdpos := (ManufacturedReflector.stay D).travel_pos
        dsimp [period, half, dTravel, lTravel]
        omega
      exact periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow
    · simp only [List.mem_singleton] at hcore
      have hentryEq : entry = R.mouth := congrArg Prod.fst hcore
      have hmouthEq : mouth = R.arm := congrArg Prod.snd hcore
      subst entry
      subst mouth
      have houtsideEq : outside = R.arm := by
        rw [R.selfLink] at hmouthLink
        exact (Option.some.inj hmouthLink).symm
      subst outside
      let lTravel := candy.length + 2
      have hReverseEnd :
          stepN w lTravel (R.arm, alternate) =
            some (R.arm, C.contactState) := by
        have h := (hLobe alternate hCandyFlip).1
        change stepN w lTravel (R.arm, alternate) =
          some (R.arm, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd :
          stepN w lTravel (R.arm, C.contactState) =
            some (R.arm, alternate) := by
        have h := (hLobe C.contactState hCandy).1
        simpa [lTravel, alternate, k] using h
      have hReversePhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (R.arm, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          hentryBranch hentryMouthSwitch hfullGrooved hfullTrace
          hcrossed hCandyForeign hmouthLink
          (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (R.arm, C.contactState) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, phase, hrun, hphase⟩ :=
          explicit_lobe_travel_two_phase
            hfullGrooved hfullTrace hcrossed hmouthLink
            (by simpa [lTravel] using hd)
        refine ⟨port, phase, hrun, ?_⟩
        dsimp [alternate, k]
        rcases hphase with h | h
        · exact Or.inr h
        · exact Or.inl h
      let period := lTravel + lTravel
      have hperiod : stepN w period (R.arm, alternate) =
          some (R.arm, alternate) := by
        dsimp [period]
        rw [stepN_add, hReverseEnd]
        exact hForwardEnd
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (R.arm, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact partialContact_twoPhase_concat
          hReverseEnd hReversePhase hForwardPhase d
          (by simpa [period] using hd)
      have hpositive : 0 < period := by
        dsimp [period, lTravel]
        omega
      exact periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow
  refine ⟨outside, mouth, ?_, ?_⟩
  · simpa [alternate, k] using hreach
  · simpa [alternate] using hallAfter

/-- The stay-forward branch contributes no vector beyond the contact pre/post
vectors already stored in `compressedLead`. -/
theorem SimpleContinuationChangedContact.forward_stay_zero_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.stay R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair : arrive C.nextState C.oriented.1 =
      (C.oriented.2, repaired))
    (hrestored : arrive repaired C.oriented.2 =
      (C.oriented.1, repaired))
    (times : List Nat) :
    NoveltyCoverOn w N
      (e, (ManufacturedReflector.stay R).activatedState)
      times (C.compressedLead N) 0 := by
  obtain ⟨outside, mouth, hreach, hall⟩ :=
    C.forward_stay_two_phase_tail hforward hrepair hrestored
  let K := C.approach.length + 1
  let alternate := flipAt C.contactState (mouth / 3)
  have hreach' : stepN w K
      (e, (ManufacturedReflector.stay R).activatedState) =
        some (outside, alternate) := by
    simpa [K, alternate] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.compressedLead N := by
    simpa [hnextAlternate] using C.next_mem_compressedLead (N := N)
  have hstateHistorical :
      VectorCount.restrict N C.contactState ∈ C.compressedLead N :=
    C.contact_mem_compressedLead
  refine ⟨[], by simp, ?_⟩
  intro j _hj
  simp only [List.append_nil]
  by_cases hjK : j < K
  · exact C.mem_compressedLead_of_approach (N := N) (by
      dsimp [K] at hjK
      omega)
  · let d := j - K
    have hjEq : j = K + d := by
      dsimp [d]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hall d
    have hglobal : stepN w j
        (e, (ManufacturedReflector.stay R).activatedState) =
          some (port, phase) := by
      rw [hjEq, stepN_add, hreach']
      exact hrun
    have hvector : restrictedTonguesAt w N
        (e, (ManufacturedReflector.stay R).activatedState) j =
          VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    rw [hvector]
    rcases hphase with h | h
    · simpa [alternate, h] using hentryHistorical
    · simpa [h] using hstateHistorical

/-- Every first-changing contact of an arbitrary simple continuation has at
most two post-contact novelty vectors.  Backward contacts are exact retrace
lassos; forward contacts are the stay/flip splices above. -/
theorem SimpleContinuationChangedContact.changed_two_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
    (times : List Nat) :
    NoveltyCoverOn w N (e, A.activatedState)
      times (C.compressedLead N) 2 := by
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · obtain ⟨fresh, hfresh, hmem⟩ :=
      C.backward_all_time_zero_novelty
        (N := N) hbackward times
    exact ⟨fresh, by omega, hmem⟩
  · cases A with
    | stay R =>
        obtain ⟨fresh, hfresh, hmem⟩ :=
          C.forward_stay_zero_novelty
            hforward hrepair hrestored times
        exact ⟨fresh, by omega, hmem⟩
    | flip R =>
        exact C.forward_flip_two_novelty
          hforward hrepair hrestored times

/-- Absolute coefficient-one bound once a partial simple continuation first
damages the old reflector support. -/
theorem SimpleContinuationChangedContact.changed_all_run_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localTimes := times.map (fun k => k - firstTravel)
  have hreach : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  obtain ⟨fresh, hfresh, hlocal⟩ :=
    C.changed_two_novelty (N := N) localTimes
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times (C.compressedLead N) 2 := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hfirst : k ≤ firstTravel
    · unfold SimpleContinuationChangedContact.compressedLead
      apply List.mem_append_left
      apply List.mem_append_left
      apply A.mem_sharpHistoryCore_of_mem
      exact A.manufacturing_journey_mem_sharpHistory hA (by
        simpa [firstTravel] using hfirst)
    · let d := k - firstTravel
      have hdMem : d ∈ localTimes := by
        dsimp [d, localTimes]
        exact List.mem_map.mpr ⟨k, hk, rfl⟩
      have hm := hlocal d hdMem
      have hshift := restrictedTonguesAt_sub_of_reach
        (N := N) hreach (by omega) (hlive k hk)
      rw [hshift]
      exact hm
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hlength := C.compressedLead_length_le hN hA
  omega

/-- Any simple partial continuation whose final configuration is included in
the finite lead costs at most `N+5`, whether or not it preserved the first
reflector support. -/
theorem ManufacturedReflector.simple_partial_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, A.activatedState) passages finish)
    (hsimple : SwitchSimple passages)
    (times : List Nat)
    (htimes : ∀ k ∈ times,
      k ≤ A.exploration.length + A.runway.length + 1 + passages.length)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  by_cases hend : PathGrooves A.toSupported.paths finish.2
  · have hsharp := A.journey_then_preserved_simple_distinct_le_N_add_two
      hN hA htrace hsimple hend times htimes hnd
    omega
  · obtain ⟨C⟩ := A.simpleContinuationChangedContact
      hA htrace hsimple hend
    exact C.changed_all_run_distinct_le_N_add_five
      hN hA times hlive hnd

/-- Unconditional fall-off branch after one reflector.  The final simple
continuation may damage the old support; no support-disjointness or completed
second reflector is assumed. -/
theorem ManufacturedReflector.simple_fall_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, A.activatedState) passages finish)
    (hsimple : SwitchSimple passages)
    (hfall : step w finish = none)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  let lastLive := A.exploration.length + A.runway.length + 1 +
    passages.length
  have hreachA : stepN w
      (A.exploration.length + A.runway.length + 1)
      (g, A.baseState) = some (e, A.activatedState) :=
    A.manufacturing_journey_reaches_activated hA
  have hlocalDead : stepN w (passages.length + 1)
      (e, A.activatedState) = none := by
    rw [stepN_add, htrace.sound]
    simpa [stepN] using hfall
  have hglobalDead : stepN w (lastLive + 1)
      (g, A.baseState) = none := by
    dsimp [lastLive]
    rw [show A.exploration.length + A.runway.length + 1 +
        passages.length + 1 =
      (A.exploration.length + A.runway.length + 1) +
        (passages.length + 1) by omega,
      stepN_add, hreachA]
    exact hlocalDead
  have htimes : ∀ k ∈ times, k ≤ lastLive := by
    intro k hk
    by_cases hle : k ≤ lastLive
    · exact hle
    · have hnone : stepN w k (g, A.baseState) = none :=
        stepN_none_of_none_at_le hglobalDead (by omega)
      have hsome := hlive k hk
      rw [hnone] at hsome
      simp at hsome
  exact A.simple_partial_distinct_le_N_add_five
    hN hA htrace hsimple times (by
      intro k hk
      simpa [lastLive] using htimes k hk)
    hlive hnd

/-- One-reflector simple lead followed by a one-vector settled tail, without
assuming that the lead preserved the old support. -/
theorem ManufacturedReflector.simple_one_vector_cycle_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {atRepeat : Nat × Tongues} {lead : List Passage}
    (hlead : PhysicalTrace w (e, A.activatedState) lead atRepeat)
    (hleadSimple : SwitchSimple lead)
    {settled : Tongues}
    (htail : ∀ d, 0 < d → ∃ port,
      stepN w d atRepeat = some (port, settled))
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  by_cases hend : PathGrooves A.toSupported.paths atRepeat.2
  · have hsharp := simple_lead_one_vector_tail_distinct_le_N_add_three
      hN A hA hlead hleadSimple hend htail times hlive hnd
    omega
  · obtain ⟨C⟩ := A.simpleContinuationChangedContact
      hA hlead hleadSimple hend
    exact C.changed_all_run_distinct_le_N_add_five
      hN hA times hlive hnd

/-- The exact residual certificate exported by the coefficient-one top-level
reduction is closed by the partial-contact theorem, with one constant to
spare. -/
theorem OneReflectorForwardContact.all_run_distinct_le_N_add_five
    {w : Wiring} {N e : Nat} {start : Nat × Tongues}
    (D : OneReflectorForwardContact w N e start)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 5 := by
  have hliveA : ∀ k ∈ times,
      (stepN w k (start.1, D.A.baseState)).isSome := by
    simpa [D.base] using hlive
  have hndA : (times.map
      (restrictedTonguesAt w N
        (start.1, D.A.baseState))).Nodup := by
    simpa [D.base] using hnd
  exact D.contact.changed_all_run_distinct_le_N_add_five
    hN D.grooves times hliveA hndA

/-- **Closed known-edge coefficient-one theorem.**  The former forward-contact
residual is discharged by `all_run_distinct_le_N_add_five`; no completed
second reflector or support-preservation premise remains. -/
theorem known_edge_N_add_six_closed
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  rcases known_edge_N_add_six_or_forward_contact
      hN hentry times hlive hnd with hclosed | hforward
  · exact hclosed
  · obtain ⟨D⟩ := hforward
    have hfive := D.all_run_distinct_le_N_add_five
      hN times hlive hnd
    omega

end GeneralN
