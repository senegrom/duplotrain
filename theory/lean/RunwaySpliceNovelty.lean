import ForeignSpliceNovelty
import ManufacturedPairNovelty

/-!
# Pointwise novelty of the runway splice

This file treats the branch left explicit by
`ManufacturedReflector.ChangedForwardMerge.runway_or_candy_absolute_one_novelty`.
The selected old passage lies on the runway of a manufactured flip reflector.
The untouched strict suffix is therefore itself a manufactured reflector,
while the changed-forward splice supplies an opposite explicit lobe.

All statements below concern the raw `Wiring`/`stepN` dynamics.  Endpoint
periodicity alone is never used as a substitute for a pointwise tongue-state
bound.
-/

namespace GeneralN

/-- One traversal of the explicit lobe created by a changed-forward splice
has only its incoming vector and the vector obtained by pinning the lobe
mouth.  This is the pointwise fact hidden by the older `IsReflector`
endpoint interface. -/
theorem explicit_lobe_travel_two_phase
    {w : Wiring} {mouth entry returnPort outside : Nat}
    {state : Tongues} {candy : List Passage}
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    {d : Nat} (hd : d <= candy.length + 2) :
    exists port phase,
      stepN w d (mouth, state) = some (port, phase) /\
        (phase = state \/ phase = flipAt state (mouth / 3)) := by
  by_cases hroute : d <= ((mouth, entry) :: candy).length
  · obtain ⟨port, hrun⟩ :=
      htrace.grooved_prefix_tongues state hgrooved hroute
    exact ⟨port, state, hrun, Or.inl rfl⟩
  · have hrouteLength : ((mouth, entry) :: candy).length =
        candy.length + 1 := by simp
    have hdEq : d = ((mouth, entry) :: candy).length + 1 := by
      rw [hrouteLength] at hroute ⊢
      omega
    have hone : stepN w 1 (returnPort, state) =
        some (outside, flipAt state (mouth / 3)) := by
      simp [stepN, step, hcrossed, hmouthLink]
    have hrun : stepN w d (mouth, state) =
        some (outside, flipAt state (mouth / 3)) := by
      rw [hdEq, stepN_add, htrace.sound]
      exact hone
    exact ⟨outside, flipAt state (mouth / 3), hrun, Or.inr rfl⟩

/-- The opposite orientation of the same explicit lobe is pointwise
two-phase as well.  The second phase restores the original mouth tongue. -/
theorem explicit_lobe_reverse_travel_two_phase
    {w : Wiring} {mouth entry returnPort outside : Nat}
    {state : Tongues} {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hmouthLink : w.link mouth = some outside)
    {d : Nat} (hd : d <= candy.length + 2) :
    exists port phase,
      stepN w d (mouth, flipAt state (mouth / 3)) =
          some (port, phase) /\
        (phase = flipAt state (mouth / 3) \/ phase = state) := by
  obtain ⟨hreverseTrace, hreverseGrooved, hrestore⟩ :=
    arbitrary_lobe_reverse_trace hentryBranch hentrySwitch
      hgrooved htrace hcrossed hCandyForeign
  have hrestore' : arrive (flipAt state (mouth / 3)) entry =
      (mouth,
        flipAt (flipAt state (mouth / 3)) (mouth / 3)) := by
    simpa [flipAt_flipAt] using hrestore
  have hd' : d <= (reversePassages candy).length + 2 := by
    simpa [reversePassages_length] using hd
  obtain ⟨port, phase, hrun, hphase⟩ :=
    explicit_lobe_travel_two_phase hreverseGrooved hreverseTrace
      hrestore' hmouthLink hd'
  refine ⟨port, phase, hrun, ?_⟩
  rcases hphase with hphase | hphase
  · exact Or.inl hphase
  · right
    simpa [flipAt_flipAt] using hphase

/-- Rebase the reverse orientation after flipping one switch which is foreign
to the whole explicit lobe.  This is the form needed after the old runway
suffix has applied its own action. -/
theorem explicit_lobe_reverse_two_phase_after_foreign_flip
    {w : Wiring} {mouth entry returnPort outside k : Nat}
    {state : Tongues} {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeignMouth : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hRouteForeignK : ∀ passage ∈ (mouth, entry) :: candy,
      passageSwitch passage ≠ k)
    (hreturnForeignK : returnPort / 3 ≠ k)
    (hmouthLink : w.link mouth = some outside)
    {d : Nat} (hd : d <= candy.length + 2) :
    exists port phase,
      stepN w d
          (mouth, flipAt (flipAt state k) (mouth / 3)) =
        some (port, phase) /\
      (phase = flipAt (flipAt state k) (mouth / 3) \/
        phase = flipAt state k) := by
  have hgroovedK : PassagesGrooved (flipAt state k)
      ((mouth, entry) :: candy) :=
    grooved_after_flip_other hgrooved hRouteForeignK
  have htraceK : PhysicalTrace w (mouth, flipAt state k)
      ((mouth, entry) :: candy) (returnPort, flipAt state k) :=
    htrace.flip_unvisited hRouteForeignK
  have hcrossedK : arrive (flipAt state k) returnPort =
      (mouth, flipAt (flipAt state k) (mouth / 3)) := by
    have h := arrive_flip_other hcrossed hreturnForeignK
    rw [flipAt_comm (by
      intro hEq
      exact hreturnForeignK (by
        have hswitch := arrive_exit_switch state returnPort
        rw [hcrossed] at hswitch
        omega))] at h
    exact h
  exact explicit_lobe_reverse_travel_two_phase
    hentryBranch hentrySwitch hgroovedK htraceK hcrossedK
    hCandyForeignMouth hmouthLink hd

/-- Entering a manufactured flip reflector at its mouth with the action
tongue already flipped exposes only the flipped vector and the restored base
vector.  This is the pointwise strengthening of `capture_from_mouth`. -/
theorem ManufacturedFlipReflector.capture_from_mouth_two_phase
    {w : Wiring} {g e : Nat}
    (C : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hrunway : PassagesGrooved state C.runway)
    (hcandy : PassagesGrooved state C.candy)
    {d : Nat}
    (hd : d <= C.candy.length + 2 + C.runway.length) :
    exists port phase,
      stepN w d (C.mouth, flipAt state C.actionSwitch) =
          some (port, phase) /\
        (phase = flipAt state C.actionSwitch \/ phase = state) := by
  have hCandyForeign : ∀ passage ∈ C.candy,
      passageSwitch passage ≠ C.actionSwitch := by
    exact C.support_foreign C.candy (by simp)
  have hcandyFlip : PassagesGrooved (flipAt state C.actionSwitch)
      C.candy := grooved_after_flip_other hcandy hCandyForeign
  rcases C.selected_arm state with hfirst | hsecond
  · have hselectedFlip :
        (flipAt state C.actionSwitch) C.actionSwitch =
          bval C.secondArm := by
      have hopp := branch_values_opposite C.firstArm_branch
        C.secondArm_branch
        (C.firstArm_switch.trans C.secondArm_switch.symm)
        C.arms_ne
      simp [flipAt, hfirst, hopp]
    have hbefore := C.candy_reverse_trace
      (flipAt state C.actionSwitch) hselectedFlip hcandyFlip
    have hbeforeSimple : SwitchSimple
        ((C.mouth, C.secondArm) :: reversePassages C.candy) := by
      have hs := C.reverse_support_simple
      unfold SwitchSimple at hs ⊢
      simp only [List.map_append] at hs
      exact (List.nodup_append.mp hs).2.1
    have hbeforeGrooved : PassagesGrooved
        (flipAt state C.actionSwitch)
        ((C.mouth, C.secondArm) :: reversePassages C.candy) :=
      hbefore.grooved_of_switchSimple hbeforeSimple
    have hfirstGroove : arrive state C.firstArm = (C.mouth, state) := by
      have htrace := C.candy_forward_trace state hfirst hcandy
      have hsimple : SwitchSimple
          ((C.mouth, C.firstArm) :: C.candy) := by
        have hs := C.simple
        unfold SwitchSimple at hs ⊢
        simp only [List.map_append] at hs
        exact (List.nodup_append.mp hs).2.1
      exact (htrace.grooved_of_switchSimple hsimple)
        (C.mouth, C.firstArm) List.mem_cons_self
    have hcontact : arrive (flipAt state C.actionSwitch) C.firstArm =
        (C.mouth, state) := by
      have hrepair := flipped_passage_forward_trailing
        hfirstGroove C.firstArm_branch
      simpa [C.firstArm_switch] using hrepair
    have hback := physicalTrace_contact_retraces_prefix_pointwise
      C.runwayTrace hrunway C.entryEdge hcontact
    have hbeforeLen :
        ((C.mouth, C.secondArm) ::
          reversePassages C.candy).length = C.candy.length + 1 := by
      simp [reversePassages_length]
    by_cases hbeforeDepth :
        d <= ((C.mouth, C.secondArm) ::
          reversePassages C.candy).length
    · obtain ⟨port, hrun⟩ := hbefore.grooved_prefix_tongues
        (flipAt state C.actionSwitch) hbeforeGrooved hbeforeDepth
      exact ⟨port, flipAt state C.actionSwitch, hrun, Or.inl rfl⟩
    · rw [hbeforeLen] at hbeforeDepth
      let q := d - (C.candy.length + 1)
      have hqPos : 1 <= q := by
        dsimp [q]
        omega
      have hq : q <= C.runway.length + 1 := by
        dsimp [q]
        omega
      have hdq : d = ((C.mouth, C.secondArm) ::
          reversePassages C.candy).length + q := by
        rw [hbeforeLen]
        dsimp [q]
        omega
      obtain ⟨port, hrun⟩ := hback.2 q hq
      have hq0 : q ≠ 0 := by omega
      have hrun' : stepN w q
          (C.firstArm, flipAt state C.actionSwitch) =
            some (port, state) := by
        simpa [hq0] using hrun
      refine ⟨port, state, ?_, Or.inr rfl⟩
      rw [hdq, stepN_add, hbefore.sound]
      exact hrun'
  · have hselectedFlip :
        (flipAt state C.actionSwitch) C.actionSwitch =
          bval C.firstArm := by
      have hopp := branch_values_opposite C.secondArm_branch
        C.firstArm_branch
        (C.secondArm_switch.trans C.firstArm_switch.symm)
        (Ne.symm C.arms_ne)
      simp [flipAt, hsecond, hopp]
    have hbefore := C.candy_forward_trace
      (flipAt state C.actionSwitch) hselectedFlip hcandyFlip
    have hbeforeSimple : SwitchSimple
        ((C.mouth, C.firstArm) :: C.candy) := by
      have hs := C.simple
      unfold SwitchSimple at hs ⊢
      simp only [List.map_append] at hs
      exact (List.nodup_append.mp hs).2.1
    have hbeforeGrooved : PassagesGrooved
        (flipAt state C.actionSwitch)
        ((C.mouth, C.firstArm) :: C.candy) :=
      hbefore.grooved_of_switchSimple hbeforeSimple
    have hsecondGroove : arrive state C.secondArm =
        (C.mouth, state) := by
      have htrace := C.candy_reverse_trace state hsecond hcandy
      have hsimple : SwitchSimple
          ((C.mouth, C.secondArm) :: reversePassages C.candy) := by
        have hs := C.reverse_support_simple
        unfold SwitchSimple at hs ⊢
        simp only [List.map_append] at hs
        exact (List.nodup_append.mp hs).2.1
      exact (htrace.grooved_of_switchSimple hsimple)
        (C.mouth, C.secondArm) List.mem_cons_self
    have hcontact : arrive (flipAt state C.actionSwitch) C.secondArm =
        (C.mouth, state) := by
      have hrepair := flipped_passage_forward_trailing
        hsecondGroove C.secondArm_branch
      simpa [C.secondArm_switch] using hrepair
    have hback := physicalTrace_contact_retraces_prefix_pointwise
      C.runwayTrace hrunway C.entryEdge hcontact
    have hbeforeLen :
        ((C.mouth, C.firstArm) :: C.candy).length =
          C.candy.length + 1 := by
      simp
    by_cases hbeforeDepth :
        d <= ((C.mouth, C.firstArm) :: C.candy).length
    · obtain ⟨port, hrun⟩ := hbefore.grooved_prefix_tongues
        (flipAt state C.actionSwitch) hbeforeGrooved hbeforeDepth
      exact ⟨port, flipAt state C.actionSwitch, hrun, Or.inl rfl⟩
    · rw [hbeforeLen] at hbeforeDepth
      let q := d - (C.candy.length + 1)
      have hqPos : 1 <= q := by
        dsimp [q]
        omega
      have hq : q <= C.runway.length + 1 := by
        dsimp [q]
        omega
      have hdq : d = ((C.mouth, C.firstArm) :: C.candy).length + q := by
        rw [hbeforeLen]
        dsimp [q]
        omega
      obtain ⟨port, hrun⟩ := hback.2 q hq
      have hq0 : q ≠ 0 := by omega
      have hrun' : stepN w q
          (C.secondArm, flipAt state C.actionSwitch) =
            some (port, state) := by
        simpa [hq0] using hrun
      refine ⟨port, state, ?_, Or.inr rfl⟩
      rw [hdq, stepN_add, hbefore.sound]
      exact hrun'

/-- Pointwise strengthening of the arbitrary-lobe theta half.  The old
manufactured reflector first exposes `state` and its own action state.  The
first old-action contact on the new lobe then either captures through the old
mouth or repairs trailing-first; in both cases every remaining intermediate
vector is `state` or the new lobe state.  Thus the complete half has exactly
the three advertised possible phases. -/
theorem manufactured_flip_arbitrary_lobe_theta_half_three_phase
    {w : Wiring} {outside mouth entry returnPort : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    {candy : List Passage}
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (hnormal : stepN w (candy.length + 2) (mouth, state) =
      some (outside, flipAt state (mouth / 3)))
    (hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch) :
    ∃ travel, 0 < travel ∧
      travel ≤ 2 * (C.toSupported.travel + (candy.length + 2)) ∧
      stepN w travel (outside, state) =
        some (outside, flipAt state (mouth / 3)) ∧
      ∀ d, d ≤ travel →
        ∃ port phase,
          stepN w d (outside, state) = some (port, phase) ∧
          phase ∈
            [state, flipAt state C.actionSwitch,
              flipAt state (mouth / 3)] := by
  let oldState := flipAt state C.actionSwitch
  let newState := flipAt state (mouth / 3)
  let route := (mouth, entry) :: candy
  have hrouteContact : ∃ passage ∈ route,
      passageSwitch passage = C.actionSwitch := by
    obtain ⟨passage, hpassage, hswitch⟩ := hcontact
    exact ⟨passage, List.mem_cons_of_mem _ hpassage, hswitch⟩
  obtain ⟨before, target, after, hsplit, hbeforeForeign,
      htargetSwitch⟩ :=
    exists_first_satisfying_split
      (fun passage => passageSwitch passage = C.actionSwitch)
      route hrouteContact
  have htrace' := htrace
  change route = before ++ target :: after at hsplit
  change PhysicalTrace w (mouth, state) route
    (returnPort, state) at htrace'
  rw [hsplit] at htrace'
  obtain ⟨middle, hbeforeRaw, hrest⟩ := htrace'.split_append
  have hmiddlePort : middle.1 = target.1 := hrest.head_arrive.1
  have hbeforeGrooved : PassagesGrooved state before := by
    intro passage hpassage
    exact hgrooved passage (by
      change passage ∈ route
      rw [hsplit]
      exact List.mem_append_left _ hpassage)
  have hprefix : PhysicalTrace w (mouth, state) before
      (target.1, state) := by
    have hreplay := hbeforeRaw.replay_grooved state hbeforeGrooved
    simpa [hmiddlePort] using hreplay
  have hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ C.actionSwitch := by
    intro passage hpassage
    exact hbeforeForeign passage hpassage
  have hbeforeGroovedOld : PassagesGrooved oldState before := by
    dsimp [oldState]
    exact grooved_after_flip_other hbeforeGrooved hforeign
  have hprefixOld : PhysicalTrace w (mouth, oldState) before
      (target.1, oldState) := by
    dsimp [oldState]
    exact hprefix.flip_unvisited hforeign
  have htargetMem : target ∈ route := by
    rw [hsplit]
    exact List.mem_append_right before List.mem_cons_self
  have hstem := htrace.passage_stem_endpoint target htargetMem
  rcases target with ⟨p, x⟩
  simp only [passageSwitch] at htargetSwitch
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  have hOldMouth : C.mouth = 3 * C.actionSwitch := by
    have hm := C.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch
    omega
  have hExplicit (depth : Nat) (hdepth : depth ≤ candy.length + 2) :
      ∃ port phase,
        stepN w depth (mouth, state) = some (port, phase) ∧
        (phase = state ∨ phase = newState) := by
    obtain ⟨port, phase, hrun, hphase⟩ :=
      explicit_lobe_travel_two_phase hgrooved htrace hcrossed
        hmouthLink hdepth
    refine ⟨port, phase, hrun, ?_⟩
    simpa [newState] using hphase
  have hfault : ∃ faultTravel,
      faultTravel ≤ C.toSupported.travel + 2 * (candy.length + 2) ∧
      stepN w faultTravel (mouth, oldState) =
        some (outside, newState) ∧
      ∀ d, d ≤ faultTravel →
        ∃ port phase,
          stepN w d (mouth, oldState) = some (port, phase) ∧
          phase ∈ [oldState, state, newState] := by
    rcases hstem with hpStem | hxStem
    · have hpMouth : p = C.mouth := by omega
      clear hpStem
      subst p
      have hCRunway := (pathGrooves_pair.mp hCpaths).1
      have hCCandy := (pathGrooves_pair.mp hCpaths).2
      have hcapture := C.capture_from_mouth state hCRunway hCCandy
      have hcaptured := theta_capture_after_unvisited_prefix
        hprefix hforeign hcapture
      let captureTravel := C.candy.length + 2 + C.runway.length
      let lobeTravel := candy.length + 2
      let faultTravel := before.length + captureTravel + lobeTravel
      have hfaultEnd : stepN w faultTravel (mouth, oldState) =
          some (outside, newState) := by
        dsimp [faultTravel, captureTravel, lobeTravel, oldState, newState]
        rw [stepN_add, hcaptured]
        exact hnormal
      refine ⟨faultTravel, ?_, hfaultEnd, ?_⟩
      · dsimp [faultTravel, captureTravel, lobeTravel]
        have hbeforeLe : before.length ≤ candy.length + 1 := by
          have hlen := congrArg List.length hsplit
          dsimp [route] at hlen
          simp only [List.length_cons, List.length_append] at hlen
          omega
        have hcaptureLe : C.candy.length + 2 + C.runway.length ≤
            C.toSupported.travel := by
          simp [ManufacturedFlipReflector.toSupported]
          omega
        omega
      · intro d hd
        by_cases hprefixDepth : d ≤ before.length
        · obtain ⟨port, hrun⟩ := hprefixOld.grooved_prefix_tongues
            oldState hbeforeGroovedOld hprefixDepth
          exact ⟨port, oldState, hrun, by simp⟩
        · by_cases hcaptureDepth :
              d ≤ before.length + captureTravel
          · let q := d - before.length
            have hqPos : 1 ≤ q := by
              dsimp [q]
              omega
            have hq : q ≤ C.candy.length + 2 + C.runway.length := by
              dsimp [q, captureTravel] at hcaptureDepth ⊢
              omega
            have hdq : d = before.length + q := by
              dsimp [q]
              omega
            obtain ⟨port, phase, hrun, hphase⟩ :=
              C.capture_from_mouth_two_phase state hCRunway hCCandy hq
            refine ⟨port, phase, ?_, ?_⟩
            · rw [hdq, stepN_add, hprefixOld.sound]
              exact hrun
            · rcases hphase with rfl | rfl
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ List.mem_cons_self
          · let q := d - (before.length + captureTravel)
            have hq : q ≤ candy.length + 2 := by
              dsimp [q, faultTravel, lobeTravel] at hd ⊢
              omega
            have hdq : d = (before.length + captureTravel) + q := by
              dsimp [q]
              omega
            obtain ⟨port, phase, hrun, hphase⟩ := hExplicit q hq
            refine ⟨port, phase, ?_, ?_⟩
            · rw [hdq, stepN_add]
              dsimp [captureTravel]
              rw [hcaptured]
              exact hrun
            · rcases hphase with rfl | rfl
              · exact List.mem_cons_of_mem _ List.mem_cons_self
              · simp
    · have hxMouth : x = C.mouth := by omega
      clear hxStem
      subst x
      have htargetGroove : arrive state C.mouth = (p, state) :=
        hgrooved (p, C.mouth) (by
          change (p, C.mouth) ∈ route
          rw [hsplit]
          exact List.mem_append_right before List.mem_cons_self)
      have hforward : arrive state p = (C.mouth, state) :=
        groove_forward htargetGroove
      have hpbranch : p % 3 ≠ 0 := by
        intro hpmod
        have hne := arrive_exit_ne state p
        rw [hforward] at hne
        apply hne
        omega
      obtain ⟨q, hlink⟩ : ∃ q, w.link C.mouth = some q := by
        cases after with
        | nil =>
            exact ⟨returnPort, by
              simpa [lastPassageExit] using hrest.last_link⟩
        | cons passage rest =>
            rcases passage with ⟨q, y⟩
            exact ⟨q, hrest.linked.1⟩
      have hone : PhysicalTrace w (p, state) [(p, C.mouth)]
          (q, state) :=
        PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
      have hlead := hprefix.append hone
      have hrepair : arrive oldState p = (C.mouth, state) := by
        dsimp [oldState]
        rw [← htargetSwitch]
        exact flipped_passage_forward_trailing hforward hpbranch
      have honeRepair : stepN w 1 (p, oldState) = some (q, state) := by
        simp [stepN, step, hrepair, hlink]
      have hprefixRepair : stepN w (before.length + 1)
          (mouth, oldState) = some (q, state) := by
        rw [stepN_add, hprefixOld.sound]
        exact honeRepair
      let tailSteps := after.length + 1
      have hrouteLength : candy.length + 1 =
          before.length + 1 + after.length := by
        have hlen := congrArg List.length hsplit
        dsimp [route] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      have htotal : candy.length + 2 =
          before.length + 1 + tailSteps := by
        dsimp [tailSteps]
        omega
      have hsuffix : stepN w tailSteps (q, state) =
          some (outside, newState) := by
        dsimp [newState]
        apply suffix_after_physical_prefix hlead
        · simpa using htotal
        · exact hnormal
      let faultTravel := before.length + 1 + tailSteps
      have hfaultEnd : stepN w faultTravel (mouth, oldState) =
          some (outside, newState) := by
        dsimp [faultTravel]
        rw [stepN_add, hprefixRepair]
        exact hsuffix
      refine ⟨faultTravel, ?_, hfaultEnd, ?_⟩
      · dsimp [faultTravel, tailSteps]
        have hbeforeLe : before.length ≤ candy.length + 1 := by omega
        omega
      · intro d hd
        by_cases hprefixDepth : d ≤ before.length
        · obtain ⟨port, hrun⟩ := hprefixOld.grooved_prefix_tongues
            oldState hbeforeGroovedOld hprefixDepth
          exact ⟨port, oldState, hrun, by simp⟩
        · let r := d - (before.length + 1)
          have hr : r ≤ tailSteps := by
            dsimp [r, faultTravel] at hd ⊢
            omega
          have hdr : d = (before.length + 1) + r := by
            dsimp [r]
            omega
          have hnormalDepth : before.length + 1 + r ≤
              candy.length + 2 := by
            omega
          obtain ⟨port, phase, hwhole, hphase⟩ :=
            hExplicit (before.length + 1 + r) hnormalDepth
          have hleadSound : stepN w (before.length + 1)
              (mouth, state) = some (q, state) := by
            simpa using hlead.sound
          have htailPoint : stepN w r (q, state) =
              some (port, phase) := by
            rw [stepN_add, hleadSound] at hwhole
            exact hwhole
          refine ⟨port, phase, ?_, ?_⟩
          · rw [hdr, stepN_add, hprefixRepair]
            exact htailPoint
          · rcases hphase with rfl | rfl
            · exact List.mem_cons_of_mem _ List.mem_cons_self
            · simp
  obtain ⟨faultTravel, hfaultLe, hfaultEnd, hfaultPointwise⟩ := hfault
  have hCrun := (C.toSupported.run state hCpaths).1
  change stepN w C.toSupported.travel (outside, state) =
      some (mouth, oldState) at hCrun
  let travel := C.toSupported.travel + faultTravel
  refine ⟨travel, ?_, ?_, ?_, ?_⟩
  · have hCpos : 0 < C.toSupported.travel := by
      change 0 < 2 * C.runway.length + C.candy.length + 2
      omega
    dsimp [travel]
    omega
  · dsimp [travel]
    omega
  · dsimp [travel]
    rw [stepN_add, hCrun]
    exact hfaultEnd
  · intro d hd
    by_cases hCdepth : d ≤ C.toSupported.travel
    · obtain ⟨middle, hrun⟩ := stepN_prefix_some hCdepth hCrun
      have htwo :=
        (ManufacturedReflector.flip C).travel_two_phase_tongues
          state hCpaths hCdepth
      have hphase : tonguesAt w (outside, state) d = middle.2 := by
        simp [tonguesAt, hrun]
      refine ⟨middle.1, middle.2, ?_, ?_⟩
      · simpa using hrun
      · rcases htwo with hbase | hold
        · have hm : middle.2 = state := hphase.symm.trans hbase
          simpa [hm]
        · have hm : middle.2 = oldState := by
            change tonguesAt w (outside, state) d = oldState at hold
            exact hphase.symm.trans hold
          simpa [oldState, hm]
    · let q := d - C.toSupported.travel
      have hq : q ≤ faultTravel := by
        dsimp [q, travel] at hd ⊢
        omega
      have hdq : d = C.toSupported.travel + q := by
        dsimp [q]
        omega
      obtain ⟨port, phase, hrun, hphase⟩ := hfaultPointwise q hq
      refine ⟨port, phase, ?_, ?_⟩
      · rw [hdq, stepN_add, hCrun]
        exact hrun
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hphase
        rcases hphase with hold | hbase | hnew
        · subst phase
          simp [oldState]
        · subst phase
          simp
        · subst phase
          simp [newState]

/-- The intersecting-action theta construction has a genuine period whose
*entire* timeline lies in the four Gray corners.  This is the pointwise fact
missing from the endpoint-only arbitrary-lobe period theorem. -/
theorem manufactured_flip_arbitrary_lobe_four_phase_period
    {w : Wiring} {outside mouth entry returnPort : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    (hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
      C.toSupported.paths)
    {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch) :
    ∃ period, 0 < period ∧
      stepN w period (outside, flipAt state (mouth / 3)) =
        some (outside, flipAt state (mouth / 3)) ∧
      ∀ d, d ≤ period →
        tonguesAt w (outside, flipAt state (mouth / 3)) d ∈
          [flipAt state (mouth / 3),
           flipAt (flipAt state (mouth / 3)) C.actionSwitch,
           state,
           flipAt state C.actionSwitch] := by
  let newState := flipAt state (mouth / 3)
  let oldState := flipAt state C.actionSwitch
  let oldNewState := flipAt newState C.actionSwitch
  have hCandy : PassagesGrooved state candy := by
    intro passage hpassage
    exact hgrooved passage (List.mem_cons_of_mem _ hpassage)
  have hnormal := (hLobe state hCandy).1
  obtain ⟨forwardTravel, hforwardPositive, _hforwardLe,
      hforward, hforwardPointwise⟩ :=
    manufactured_flip_arbitrary_lobe_theta_half_three_phase
      C state hCpaths hgrooved htrace hcrossed hmouthLink hnormal hcontact
  have hCNew : PathGrooves C.toSupported.paths newState := by
    dsimp [newState]
    exact hCpaths.after_avoiding_action hNewAvoidsC
  have hCandyNew : PassagesGrooved newState candy := by
    dsimp [newState]
    exact grooved_after_flip_other hCandy hCandyForeign
  obtain ⟨hreverseTrace, hreverseGrooved, hrestore⟩ :=
    arbitrary_lobe_reverse_trace hentryBranch hentrySwitch
      hgrooved htrace hcrossed hCandyForeign
  have hreverseCrossed : arrive newState entry =
      (mouth, flipAt newState (mouth / 3)) := by
    dsimp [newState]
    simpa [flipAt_flipAt] using hrestore
  have hmap :
      (reversePassages candy).map passageSwitch =
        (candy.map passageSwitch).reverse := by
    cases htrace with
    | @cons _ _ _ _ _ _ _ _ _ tail =>
        exact map_passageSwitch_reversePassages tail
  have hcontactReverse : ∃ passage ∈ reversePassages candy,
      passageSwitch passage = C.actionSwitch := by
    obtain ⟨old, hold, holdSwitch⟩ := hcontact
    have hkeyMem : C.actionSwitch ∈ candy.map passageSwitch :=
      List.mem_map.mpr ⟨old, hold, holdSwitch⟩
    have hreverseKey : C.actionSwitch ∈
        (reversePassages candy).map passageSwitch := by
      rw [hmap]
      exact List.mem_reverse.mpr hkeyMem
    obtain ⟨passage, hpassage, hswitch⟩ :=
      List.mem_map.mp hreverseKey
    exact ⟨passage, hpassage, hswitch⟩
  have hnormalReverse :
      stepN w ((reversePassages candy).length + 2)
        (mouth, newState) =
          some (outside, flipAt newState (mouth / 3)) := by
    have hrun := (hLobe newState hCandyNew).1
    simpa [reversePassages_length, newState] using hrun
  obtain ⟨reverseTravel, hreversePositive, _hreverseLe,
      hreverse, hreversePointwise⟩ :=
    manufactured_flip_arbitrary_lobe_theta_half_three_phase C
      newState hCNew hreverseGrooved hreverseTrace hreverseCrossed
      hmouthLink hnormalReverse hcontactReverse
  have hreverse' : stepN w reverseTravel (outside, newState) =
      some (outside, state) := by
    change stepN w reverseTravel (outside, newState) =
      some (outside, flipAt newState (mouth / 3)) at hreverse
    dsimp [newState] at hreverse ⊢
    rw [flipAt_flipAt state (mouth / 3)] at hreverse
    exact hreverse
  let period := reverseTravel + forwardTravel
  have hperiod : stepN w period (outside, newState) =
      some (outside, newState) := by
    dsimp [period]
    rw [stepN_add, hreverse']
    change stepN w forwardTravel (outside, state) =
      some (outside, newState)
    exact hforward
  refine ⟨period, by dsimp [period]; omega, ?_, ?_⟩
  · simpa [newState] using hperiod
  · intro d hd
    change tonguesAt w (outside, newState) d ∈
      [newState, oldNewState, state, oldState]
    by_cases hreverseDepth : d ≤ reverseTravel
    · obtain ⟨port, phase, hrun, hphase⟩ :=
        hreversePointwise d hreverseDepth
      have htongues : tonguesAt w (outside, newState) d = phase := by
        simp [tonguesAt, hrun]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hphase
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hphase with hnew | hboth | hbase
      · exact Or.inl (htongues.trans hnew)
      · exact Or.inr (Or.inl (htongues.trans hboth))
      · have hbase' : phase = state := by
          rw [hbase]
          dsimp [newState]
          exact flipAt_flipAt state (mouth / 3)
        exact Or.inr (Or.inr (Or.inl (htongues.trans hbase')))
    · let q := d - reverseTravel
      have hq : q ≤ forwardTravel := by
        dsimp [q, period] at hd ⊢
        omega
      have hdq : d = reverseTravel + q := by
        dsimp [q]
        omega
      obtain ⟨port, phase, hrun, hphase⟩ :=
        hforwardPointwise q hq
      have hrun' : stepN w d (outside, newState) =
          some (port, phase) := by
        rw [hdq, stepN_add, hreverse']
        exact hrun
      have htongues : tonguesAt w (outside, newState) d = phase := by
        simp [tonguesAt, hrun']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hphase
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hphase with hbase | hold | hnew
      · exact Or.inr (Or.inr (Or.inl (htongues.trans hbase)))
      · exact Or.inr (Or.inr (Or.inr (htongues.trans hold)))
      · exact Or.inl (htongues.trans hnew)

/-- The four-corner bound for an intersecting-action runway splice holds at
every future time, not just during one theta period. -/
theorem manufactured_flip_arbitrary_lobe_all_time_four_phase_tongues
    {w : Wiring} {outside mouth entry returnPort : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    (hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
      C.toSupported.paths)
    {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch)
    (d : Nat) :
    tonguesAt w (outside, flipAt state (mouth / 3)) d ∈
      [flipAt state (mouth / 3),
       flipAt (flipAt state (mouth / 3)) C.actionSwitch,
       state,
       flipAt state C.actionSwitch] := by
  obtain ⟨period, hperiodPositive, hperiod, hwindow⟩ :=
    manufactured_flip_arbitrary_lobe_four_phase_period C state hCpaths
      hNewAvoidsC hentryBranch hentrySwitch hgrooved htrace hcrossed
      hCandyForeign hLobe hmouthLink hcontact
  let q := d / period
  let r := d % period
  have hr : r < period := by
    dsimp [r]
    exact Nat.mod_lt d hperiodPositive
  have hdEq : d = q * period + r := by
    dsimp [q, r]
    have hdiv := Nat.div_add_mod d period
    rw [Nat.mul_comm period (d / period)] at hdiv
    omega
  have hsame :
      tonguesAt w (outside, flipAt state (mouth / 3)) d =
        tonguesAt w (outside, flipAt state (mouth / 3)) r := by
    have hrun : stepN w d (outside, flipAt state (mouth / 3)) =
        stepN w r (outside, flipAt state (mouth / 3)) := by
      rw [hdEq, stepN_add,
        stepN_mul_period_pair_novelty hperiod q]
      simp
    simp [tonguesAt, hrun]
  rw [hsame]
  exact hwindow r (Nat.le_of_lt hr)

/-- **Four pointwise phases for the compatible runway suffix and splice
lobe.**  This is the arbitrary-candy analogue of
`manufactured_pair_four_phase_tongues`: the old side is the manufactured
strict runway suffix, while the new side is the explicit lobe exported by
`spliced_lobe_reflector`.

The only compatibility premise not already supplied by the suffix theorem is
`hCandyForeignOld`: the new candy must avoid the old suffix's action switch.
-/
theorem manufactured_suffix_explicit_lobe_four_phase_tongues
    {w : Wiring} {outside mouth entry returnPort : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    (hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
      C.toSupported.paths)
    (hActionsNe : mouth / 3 ≠ C.actionSwitch)
    {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeignNew : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hCandyForeignOld : ∀ passage ∈ candy,
      passageSwitch passage ≠ C.actionSwitch)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    {d : Nat}
    (hd : d <= 2 * (C.toSupported.travel + (candy.length + 2))) :
    tonguesAt w (outside, flipAt state (mouth / 3)) d ∈
      [flipAt state (mouth / 3),
       flipAt (flipAt state (mouth / 3)) C.actionSwitch,
       flipAt state C.actionSwitch,
       state] := by
  let newState := flipAt state (mouth / 3)
  let oldNewState := flipAt newState C.actionSwitch
  let oldState := flipAt state C.actionSwitch
  let lobeTravel := candy.length + 2

  have hCandy : PassagesGrooved state candy := by
    intro passage hp
    exact hgrooved passage (List.mem_cons_of_mem _ hp)
  have hCNew : PathGrooves C.toSupported.paths newState := by
    dsimp [newState]
    exact hCpaths.after_avoiding_action hNewAvoidsC
  have hCrunNew : stepN w C.toSupported.travel
      (outside, newState) = some (mouth, oldNewState) := by
    have hrun := (C.toSupported.run newState hCNew).1
    change stepN w C.toSupported.travel (outside, newState) =
      some (mouth, flipAt newState C.actionSwitch) at hrun
    simpa [oldNewState] using hrun

  have hCandyNew : PassagesGrooved newState candy := by
    dsimp [newState]
    exact grooved_after_flip_other hCandy hCandyForeignNew
  have hCandyOldNew : PassagesGrooved oldNewState candy := by
    dsimp [oldNewState]
    exact grooved_after_flip_other hCandyNew hCandyForeignOld
  have hLobeReverse := (hLobe oldNewState hCandyOldNew).1
  have hOldNewAfter : flipAt oldNewState (mouth / 3) = oldState := by
    dsimp [oldNewState, newState, oldState]
    rw [flipAt_comm (Ne.symm hActionsNe)]
    rw [flipAt_flipAt]
  have hLobeReverseRun : stepN w lobeTravel
      (mouth, oldNewState) = some (outside, oldState) := by
    change stepN w (candy.length + 2) (mouth, oldNewState) =
      some (outside, flipAt oldNewState (mouth / 3)) at hLobeReverse
    rw [hOldNewAfter] at hLobeReverse
    exact hLobeReverse
  have hHalfRun : stepN w (C.toSupported.travel + lobeTravel)
      (outside, newState) = some (outside, oldState) := by
    rw [stepN_add, hCrunNew]
    exact hLobeReverseRun

  have hCOld : PathGrooves C.toSupported.paths oldState := by
    dsimp [oldState]
    exact hCpaths.after_avoiding_action
      (ManufacturedReflector.flip C).action_avoids_own_support
  have hCrunOldRaw := (C.toSupported.run oldState hCOld).1
  have hOldAfter : flipAt oldState C.actionSwitch = state := by
    dsimp [oldState]
    exact flipAt_flipAt state C.actionSwitch
  have hCrunOld : stepN w C.toSupported.travel
      (outside, oldState) = some (mouth, state) := by
    change stepN w C.toSupported.travel (outside, oldState) =
      some (mouth, flipAt oldState C.actionSwitch) at hCrunOldRaw
    rw [hOldAfter] at hCrunOldRaw
    exact hCrunOldRaw
  have hThreeRun : stepN w
      ((C.toSupported.travel + lobeTravel) + C.toSupported.travel)
      (outside, newState) = some (mouth, state) := by
    rw [stepN_add, hHalfRun]
    exact hCrunOld
  have hLobeForwardRun := (hLobe state hCandy).1
  have hLobeForwardRun' : stepN w lobeTravel (mouth, state) =
      some (outside, newState) := by
    simpa [lobeTravel, newState] using hLobeForwardRun
  have hPeriod : stepN w
      (2 * (C.toSupported.travel + lobeTravel))
      (outside, newState) = some (outside, newState) := by
    have hlen : 2 * (C.toSupported.travel + lobeTravel) =
        ((C.toSupported.travel + lobeTravel) + C.toSupported.travel) +
          lobeTravel := by omega
    rw [hlen, stepN_add, hThreeRun]
    exact hLobeForwardRun'

  by_cases hFirstC : d <= C.toSupported.travel
  · rcases (ManufacturedReflector.flip C).travel_two_phase_tongues
        newState hCNew hFirstC with hnew | holdNew
    · rw [hnew]
      simp [newState]
    · change tonguesAt w (outside, newState) d = oldNewState at holdNew
      rw [holdNew]
      simp [newState, oldNewState]
  · by_cases hFirstLobe :
        d <= C.toSupported.travel + lobeTravel
    · let q := d - C.toSupported.travel
      have hq : q <= candy.length + 2 := by
        dsimp [q, lobeTravel] at hFirstLobe ⊢
        omega
      have hdq : d = C.toSupported.travel + q := by
        dsimp [q]
        omega
      have hRouteForeignOld : ∀ passage ∈ (mouth, entry) :: candy,
          passageSwitch passage ≠ C.actionSwitch := by
        intro passage hp
        rcases List.mem_cons.mp hp with hhead | htail
        · subst passage
          simpa [passageSwitch] using hActionsNe
        · exact hCandyForeignOld passage htail
      have hreturnSwitch : returnPort / 3 = mouth / 3 := by
        have hs := arrive_exit_switch state returnPort
        rw [hcrossed] at hs
        exact hs.symm
      have hreturnForeignOld : returnPort / 3 ≠ C.actionSwitch := by
        rw [hreturnSwitch]
        exact hActionsNe
      obtain ⟨port, phase, hqrun, hphase⟩ :=
        explicit_lobe_reverse_two_phase_after_foreign_flip
          hentryBranch hentrySwitch hgrooved htrace hcrossed
          hCandyForeignNew hRouteForeignOld hreturnForeignOld
          hmouthLink hq
      have hstartEq :
          flipAt (flipAt state C.actionSwitch) (mouth / 3) =
            oldNewState := by
        dsimp [oldNewState, newState]
        exact flipAt_comm (Ne.symm hActionsNe)
      rw [hstartEq] at hqrun hphase
      have hrun : stepN w d (outside, newState) = some (port, phase) := by
        rw [hdq, stepN_add, hCrunNew]
        exact hqrun
      have htongues : tonguesAt w (outside, newState) d = phase := by
        simp [tonguesAt, hrun]
      rw [htongues]
      rcases hphase with rfl | rfl
      · simp [newState, oldNewState]
      · simp [newState, oldState]
    · by_cases hSecondC :
          d <= (C.toSupported.travel + lobeTravel) +
            C.toSupported.travel
      · let q := d - (C.toSupported.travel + lobeTravel)
        have hq : q <= C.toSupported.travel := by
          dsimp [q]
          omega
        have hdq : d = (C.toSupported.travel + lobeTravel) + q := by
          dsimp [q]
          omega
        rcases (ManufacturedReflector.flip C).travel_two_phase_tongues
            oldState hCOld hq with hold | hrestored
        · have hlive : ∃ finish,
              stepN w q (outside, oldState) = some finish :=
            stepN_prefix_some hq hCrunOld
          have hshift := tonguesAt_add_of_reaches hHalfRun hlive
          rw [← hdq] at hshift
          rw [hshift, hold]
          simp [newState, oldState]
        · have hlive : ∃ finish,
              stepN w q (outside, oldState) = some finish :=
            stepN_prefix_some hq hCrunOld
          have hshift := tonguesAt_add_of_reaches hHalfRun hlive
          rw [← hdq] at hshift
          change tonguesAt w (outside, oldState) q =
            flipAt oldState C.actionSwitch at hrestored
          rw [hshift, hrestored, hOldAfter]
          simp
      · let q := d -
          ((C.toSupported.travel + lobeTravel) + C.toSupported.travel)
        have hq : q <= candy.length + 2 := by
          dsimp [q, lobeTravel] at hd ⊢
          omega
        have hdq : d =
            ((C.toSupported.travel + lobeTravel) +
              C.toSupported.travel) + q := by
          dsimp [q]
          omega
        obtain ⟨port, phase, hqrun, hphase⟩ :=
          explicit_lobe_travel_two_phase hgrooved htrace hcrossed
            hmouthLink hq
        have hrun : stepN w d (outside, newState) =
            some (port, phase) := by
          rw [hdq, stepN_add, hThreeRun]
          exact hqrun
        have htongues : tonguesAt w (outside, newState) d = phase := by
          simp [tonguesAt, hrun]
        rw [htongues]
        rcases hphase with rfl | rfl
        · simp [newState]
        · simp [newState]

/-- The compatible four-phase window repeats forever.  The endpoint period
comes from the old supported-reflector API; every intermediate vector is
controlled separately by `manufactured_suffix_explicit_lobe_four_phase_tongues`.
-/
theorem manufactured_suffix_explicit_lobe_all_time_four_phase_tongues
    {w : Wiring} {outside mouth entry returnPort : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    (hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
      C.toSupported.paths)
    (hActionsNe : mouth / 3 ≠ C.actionSwitch)
    {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeignNew : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hCandyForeignOld : ∀ passage ∈ candy,
      passageSwitch passage ≠ C.actionSwitch)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (d : Nat) :
    tonguesAt w (outside, flipAt state (mouth / 3)) d ∈
      [flipAt state (mouth / 3),
       flipAt (flipAt state (mouth / 3)) C.actionSwitch,
       flipAt state C.actionSwitch,
       state] := by
  let L : SupportedReflector w mouth outside := {
    travel := candy.length + 2
    paths := [candy]
    action := .flip (mouth / 3)
    run := by
      intro current hpaths
      have hCandyCurrent : PassagesGrooved current candy :=
        hpaths candy (by simp)
      obtain ⟨hstep, hnext⟩ := hLobe current hCandyCurrent
      constructor
      · exact hstep
      · intro path hp
        simp only [List.mem_singleton] at hp
        subst path
        exact hnext
  }
  have hOldAvoidsL : C.toSupported.action.Avoids L.paths := by
    change (LocalAction.flip C.actionSwitch).Avoids [candy]
    intro path hp passage hpassage
    simp only [List.mem_singleton] at hp
    subst path
    exact hCandyForeignOld passage hpassage
  have hCNew : PathGrooves C.toSupported.paths
      (flipAt state (mouth / 3)) :=
    hCpaths.after_avoiding_action hNewAvoidsC
  have hCandy : PassagesGrooved state candy := by
    intro passage hp
    exact hgrooved passage (List.mem_cons_of_mem _ hp)
  have hCandyNew : PassagesGrooved
      (flipAt state (mouth / 3)) candy :=
    grooved_after_flip_other hCandy hCandyForeignNew
  have hLNew : PathGrooves L.paths
      (flipAt state (mouth / 3)) := by
    intro path hp
    simp only [L, List.mem_singleton] at hp
    subst path
    exact hCandyNew
  let period := 2 * (C.toSupported.travel + L.travel)
  have hperiodPos : 0 < period := by
    have hCpos := (ManufacturedReflector.flip C).travel_pos
    dsimp [period, L]
    omega
  have hperiod : stepN w period
      (outside, flipAt state (mouth / 3)) =
        some (outside, flipAt state (mouth / 3)) := by
    dsimp [period]
    exact C.toSupported.paired_period L hOldAvoidsL hNewAvoidsC
      (flipAt state (mouth / 3)) hCNew hLNew
  let q := d / period
  let r := d % period
  have hr : r < period := by
    dsimp [r]
    exact Nat.mod_lt d hperiodPos
  have hdEq : d = q * period + r := by
    dsimp [q, r]
    have hdiv := Nat.div_add_mod d period
    rw [Nat.mul_comm period (d / period)] at hdiv
    omega
  have hsame :
      tonguesAt w (outside, flipAt state (mouth / 3)) d =
        tonguesAt w (outside, flipAt state (mouth / 3)) r := by
    have hrun : stepN w d
        (outside, flipAt state (mouth / 3)) =
      stepN w r (outside, flipAt state (mouth / 3)) := by
      rw [hdEq, stepN_add,
        stepN_mul_period_pair_novelty hperiod q]
      simp
    simp [tonguesAt, hrun]
  rw [hsame]
  apply manufactured_suffix_explicit_lobe_four_phase_tongues
    C state hCpaths hNewAvoidsC hActionsNe hentryBranch
    hentrySwitch hgrooved htrace hcrossed hCandyForeignNew
    hCandyForeignOld hLobe hmouthLink
  dsimp [period, L] at hr
  exact Nat.le_of_lt hr
end GeneralN
