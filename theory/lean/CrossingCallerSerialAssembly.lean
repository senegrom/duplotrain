import CrossingCallerSharpTail

/-!
# Exact serial timing for the crossing-caller tail

The generic changed-forward theorem deliberately forgets which concrete
route prefix reached its productive contact and retains only a bound by the
old reflector's complete macro travel.  A serial caller certificate contains
the concrete prefix.  The lemmas below preserve it: the splice orbit starts
after exactly `approach.length + 1` steps.
-/

namespace GeneralN

/-- Specialized splice construction which retains the concrete approach from
the forward contact.  This is the proof-relevant version needed for raw-time
assembly: its lead is definitionally `approach.length + 1`, rather than an
existential bounded by the whole reflector travel. -/
theorem ManufacturedReflector.forward_contact_spliced_lobe_reflector
    {w : Wiring} {g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    {approach suffix path : List Passage}
    {u v : Tongues} {old : Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix)
    (happroach :
      PhysicalTrace w (g, B.activatedState) approach (p, u))
    (hpaths : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (_hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (holdOriented : old ∈ B.orientedRoute u)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3))
    (holdGroove : arrive u old.2 = (old.1, u))
    (hforward : x = old.2) :
    ∃ (entry mouth returnPort outside : Nat)
        (oldPrefix oldTail candy : List Passage)
        (state : Tongues) (tailSteps : Nat),
      (entry, mouth) ∈ B.orientedRoute state ∧
      B.orientedRoute state =
        oldPrefix ++ (entry, mouth) :: oldTail ∧
      PhysicalTrace w (outside, state) oldTail
        (B.orientedFinish state, state) ∧
      PhysicalTrace w (g, state) approach (returnPort, state) ∧
      PassagesGrooved state approach ∧
      (∀ passage ∈ approach,
        passageSwitch passage ≠ mouth / 3) ∧
      candy = reversePassages oldPrefix ++ approach ∧
      entry % 3 ≠ 0 ∧ mouth % 3 = 0 ∧
      w.link mouth = some outside ∧
      entry ≠ returnPort ∧
      PassagesGrooved state ((mouth, entry) :: candy) ∧
      PhysicalTrace w (mouth, state) ((mouth, entry) :: candy)
        (returnPort, state) ∧
      arrive state returnPort =
        (mouth, flipAt state (mouth / 3)) ∧
      PathGrooves B.toSupported.paths state ∧
      PassagesGrooved state candy ∧
      (∀ passage ∈ candy,
        passageSwitch passage ≠ mouth / 3) ∧
      IsReflector w mouth outside (candy.length + 2)
        (fun state => PassagesGrooved state candy)
        (fun state => flipAt state (mouth / 3)) ∧
      stepN w (approach.length + 1) (g, B.activatedState) =
        some (outside, flipAt state (mouth / 3)) ∧
      stepN w tailSteps (outside, state) =
        some (g, B.toSupported.action.apply state) ∧
      B.toSupported.travel = oldPrefix.length + 1 + tailSteps ∧
      approach.length + 1 ≤ A.toSupported.travel := by
  obtain ⟨repaired, hrepair, hrestored⟩ :=
    forward_contact_repairs_old_passage holdGroove
      (by simpa [hforward] using harrive)
      (by simpa [passageSwitch] using hswitch) hchanged
  rcases old with ⟨a, s⟩
  simp only at holdOriented holdGroove hforward hrepair hrestored
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
    have hsame := arrive_exit_switch u s
    rw [holdGroove] at hsame
    exact hsame.symm
  have haBranch : a % 3 ≠ 0 := by
    have haEq : branchPort (s / 3) (u (s / 3)) = a := by
      unfold arrive at holdGroove
      rw [if_pos hsStem] at holdGroove
      exact congrArg Prod.fst holdGroove
    intro haStem
    cases hu : u (s / 3) <;>
      simp [branchPort, hu] at haEq <;> omega
  have hap : a ≠ p := by
    intro hEq
    subst p
    have holdForward := groove_forward holdGroove
    rw [harrive] at holdForward
    have huv : v = u := congrArg Prod.snd holdForward
    apply hchanged
    rw [huv]

  obtain ⟨oldPrefix, oldTail, hBrouteSplit⟩ :=
    List.append_of_mem holdOriented
  have hroute := B.orientedRoute_trace u hpaths
  have hrouteSimple := B.orientedRoute_simple u
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  have hOldPrefixData := simple_grooved_trace_prefix_to_occurrence
    hroute hBrouteSplit hrouteGrooved hrouteSimple
  have hOldPrefixGrooved : PassagesGrooved u oldPrefix := by
    intro passage hp
    exact hrouteGrooved passage (by
      rw [hBrouteSplit]
      exact List.mem_append_left _ hp)

  have hApproachSimple : SwitchSimple approach := by
    have hsimple := A.orientedRoute_simple B.activatedState
    unfold SwitchSimple at hsimple ⊢
    rw [hrouteSplit] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    exact (List.nodup_append.mp hsimple).1
  have hApproachGrooved : PassagesGrooved u approach :=
    happroach.grooved_of_switchSimple hApproachSimple
  have hApproachForeign : ∀ passage ∈ approach,
      passageSwitch passage ≠ p / 3 := by
    have hsimple := A.orientedRoute_simple B.activatedState
    unfold SwitchSimple at hsimple
    rw [hrouteSplit] at hsimple
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
  have hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ s / 3 := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    · have hmapped : passageSwitch passage ∈
          (reversePassages oldPrefix).map passageSwitch :=
        List.mem_map.mpr ⟨passage, hold, rfl⟩
      have hmap := map_passageSwitch_reversePassages hOldPrefixData.1
      rw [hmap] at hmapped
      have horiginal : passageSwitch passage ∈
          oldPrefix.map passageSwitch := List.mem_reverse.mp hmapped
      obtain ⟨prior, hprior, hpriorEq⟩ := List.mem_map.mp horiginal
      intro hmouth
      apply hOldPrefixData.2 prior hprior
      exact hpriorEq.trans (hmouth.trans hsa)
    · intro hmouth
      apply hApproachForeign passage hnew
      exact hmouth.trans hsp

  have hback := physicalTrace_contact_retraces_prefix
    hOldPrefixData.1 hOldPrefixGrooved B.entryEdge holdGroove
  have hforwardTrace := happroach.replay_grooved u hApproachGrooved
  have hsplice :
      PhysicalTrace w (s, u) ((s, a) :: candy) (p, u) := by
    simpa [candy, List.append_assoc] using hback.append hforwardTrace
  have hSpliceGrooved :
      PassagesGrooved u ((s, a) :: candy) := by
    intro passage hpassage
    rcases List.mem_cons.mp hpassage with hhead | htail
    · simpa [hhead] using groove_forward holdGroove
    · exact hCandyGrooved passage htail

  have hroute' := hroute
  rw [hBrouteSplit] at hroute'
  obtain ⟨middle, hOldBefore, hOldAfter⟩ := hroute'.split_append
  have hMiddle : middle = (a, u) := by
    have h₁ := hOldBefore.sound
    have h₂ := hOldPrefixData.1.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  cases hOldAfter with
  | @cons _ _ outside _ oldAfter _ _ hOldArrive hmouth hOldRest =>
      have hOldAfterState : oldAfter = u := by
        have hsame := groove_forward holdGroove
        rw [hOldArrive] at hsame
        exact congrArg Prod.snd hsame
      subst oldAfter
      have hcontactTrace : PhysicalTrace w (a, u) [(a, s)]
          (outside, u) :=
        PhysicalTrace.cons (groove_forward holdGroove) hmouth
          (PhysicalTrace.nil _)
      have hlead := hOldPrefixData.1.append hcontactTrace
      have hleadSplit : B.orientedRoute u =
          (oldPrefix ++ [(a, s)]) ++ oldTail := by
        rw [hBrouteSplit]
        simp [List.append_assoc]
      obtain ⟨tailSteps, hlen, hcomplete⟩ :=
        B.complete_after_oriented_prefix u hpaths hleadSplit hlead
      have hflip : v = flipAt u (s / 3) := by
        have hv := changed_arrival_eq_flipAt harrive hchanged
        simpa [hsp] using hv
      have hone : stepN w 1 (p, u) = some (outside, v) := by
        simp [stepN, step, harrive, hmouth]
      have hreach : stepN w (approach.length + 1)
          (g, B.activatedState) =
          some (outside, flipAt u (s / 3)) := by
        rw [stepN_add, happroach.sound]
        simp only [Option.bind_some]
        rw [hone, hflip]
      have hcrossed : arrive u p =
          (s, flipAt u (s / 3)) := by
        rw [harrive, hflip]
      have htailLen : B.toSupported.travel =
          oldPrefix.length + 1 + tailSteps := by
        rw [hlen]
        simp
      have happroachLe : approach.length + 1 ≤
          A.toSupported.travel := by
        have hrouteLen :
            (A.orientedRoute B.activatedState).length =
              approach.length + 1 + suffix.length := by
          rw [hrouteSplit]
          simp
          omega
        have hrouteLe :=
          A.orientedRoute_length_le_travel B.activatedState
        omega
      refine ⟨a, s, p, outside, oldPrefix, oldTail, candy, u,
        tailSteps, holdOriented, hBrouteSplit, hOldRest,
        hforwardTrace, hApproachGrooved, (by
          intro passage hpassage
          simpa [hsp] using hApproachForeign passage hpassage),
        rfl, haBranch, hsStem, hmouth, hap, hSpliceGrooved,
        hsplice, hcrossed, hpaths, hCandyGrooved, hCandyForeign,
        ?_, hreach, hcomplete, htailLen, happroachLe⟩
      exact stem_lobe_isReflector_foreign w candy
        hsStem haBranch hpBranch hsa hsp hap hCandyForeign
        hsplice.linked hsplice.last_link hmouth

/-- The historical-entry three-vector theorem with the exact concrete lead
retained.  This is the quantitative bridge needed by a serial certificate:
history is required only through the actual contact prefix. -/
theorem ManufacturedReflector.forward_contact_exact_three_novelty
    {w : Wiring} {g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (R : ManufacturedFlipReflector w e g)
    {approach suffix path : List Passage}
    {u v : Tongues} {old : Passage}
    (hrouteSplit : A.orientedRoute
        (ManufacturedReflector.flip R).activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w
      (g, (ManufacturedReflector.flip R).activatedState)
        approach (p, u))
    (hpaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ (ManufacturedReflector.flip R).toSupported.paths)
    (hold : old ∈ path)
    (holdOriented : old ∈
      (ManufacturedReflector.flip R).orientedRoute u)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3))
    (holdGroove : arrive u old.2 = (old.1, u))
    (hforward : x = old.2)
    (N : Nat) (history : List (List Bool))
    (hleadHistorical : ∀ j, j ≤ approach.length + 1 →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈ history)
    (times : List Nat) :
    NoveltyCoverOn w N
      (g, (ManufacturedReflector.flip R).activatedState)
      times history 3 := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, state, _tailSteps, horiented, hBrouteSplit, hOldTail,
      hApproach, hApproachGrooved, hApproachForeign, _hCandyEq,
      hentryBranch, _hmouthStem, hmouthLink, harms, hfullGrooved,
      hfullTrace, hcrossed, hRpaths, _hCandy, hCandyForeignNew,
      hLobe, hreach, _hcomplete, _htailLen, _happroachLe⟩ :=
    A.forward_contact_spliced_lobe_reflector
      (ManufacturedReflector.flip R)
      hrouteSplit happroach hpaths harrive hpath hold holdOriented
      hswitch hchanged holdGroove hforward
  have hentryHistorical : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history := by
    have hvector : restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState)
        (approach.length + 1) =
        VectorCount.restrict N (flipAt state (mouth / 3)) := by
      simp [restrictedTonguesAt, tonguesAt, hreach]
    rw [← hvector]
    exact hleadHistorical (approach.length + 1) (Nat.le_refl _)
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ :=
      List.append_of_mem hrunway
    obtain ⟨C, _hCAction, hEntryOldNe, hCpaths,
        hNewAvoidsCRaw, _htravel⟩ :=
      R.suffix_after_runway_passage_with_travel state hRpaths
        hrunwaySplit hmouthLink
    have hentrySwitch : entry / 3 = mouth / 3 := by
      have hheadGroove : arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hsame := arrive_exit_switch state entry
      rw [hheadGroove] at hsame
      exact hsame.symm
    have hActionsNe : mouth / 3 ≠ C.actionSwitch := by
      rw [← hentrySwitch]
      exact hEntryOldNe
    have hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
        C.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsCRaw
    by_cases hcontact : ∃ passage ∈ candy,
        passageSwitch passage = C.actionSwitch
    · apply manufactured_flip_arbitrary_lobe_absolute_three_novelty
        C state hCpaths hNewAvoidsC hentryBranch hentrySwitch
        hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
        hmouthLink hcontact hreach times history hentryHistorical
      intro j _hj hjLead
      exact hleadHistorical j (Nat.le_of_lt hjLead)
    · have hCandyForeignOld : ∀ passage ∈ candy,
          passageSwitch passage ≠ C.actionSwitch := by
        intro passage hp hEq
        exact hcontact ⟨passage, hp, hEq⟩
      apply manufactured_suffix_explicit_lobe_absolute_three_novelty
        C state hCpaths hNewAvoidsC hActionsNe hentryBranch
        hentrySwitch hfullGrooved hfullTrace hcrossed
        hCandyForeignNew hCandyForeignOld hLobe hmouthLink hreach
        times history hentryHistorical
      intro j _hj hjLead
      exact hleadHistorical j (Nat.le_of_lt hjLead)
  · obtain ⟨prior, hprior, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        horiented hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    have hone := manufactured_flip_candy_splice_absolute_one_novelty
      R state hRpaths hBrouteSplit hOldTail hrunway hentryBranch
      hprior horientation hentryGrooved hApproach hApproachGrooved
      hApproachForeign hcrossed hmouthLink harms hreach
      N history hentryHistorical times (by
        intro j _hj hjLead
        exact hleadHistorical j (Nat.le_of_lt hjLead))
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩

/-- An exact changed-forward contact reached by the first selected post-state
gives the literal four-vector cover.  The deadline is the concrete splice
lead, not the old reflector's complete travel. -/
theorem RawOverlappingFiveWindowReduction.early_forward_contact_exact_tail_four_cover
    {w : Wiring} {N g e shift p x : Nat}
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (A : ManufacturedReflector w g e)
    (R : ManufacturedFlipReflector w e g)
    {approach suffix path : List Passage}
    {u v : Tongues} {old : Passage}
    (hrouteSplit : A.orientedRoute
        (ManufacturedReflector.flip R).activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w
      (g, (ManufacturedReflector.flip R).activatedState)
        approach (p, u))
    (hpaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ (ManufacturedReflector.flip R).toSupported.paths)
    (hold : old ∈ path)
    (holdOriented : old ∈
      (ManufacturedReflector.flip R).orientedRoute u)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3))
    (holdGroove : arrive u old.2 = (old.1, u))
    (hforward : x = old.2)
    (hreach : stepN w shift start = some
      (g, (ManufacturedReflector.flip R).activatedState))
    (hdeadline : shift + (approach.length + 1) ≤ C.z1 + 1) :
    NoveltyCoverOn w N start
      [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1]
      (rawFirstWriterHistory w N start (C.z5 + 1) ++
        [restrictedTonguesAt w N start (C.z0 + 1)]) 4 := by
  classical
  let localStart : Nat × Tongues :=
    (g, (ManufacturedReflector.flip R).activatedState)
  let history0 := rawFirstWriterHistory w N start (C.z5 + 1) ++
    [restrictedTonguesAt w N start (C.z0 + 1)]
  let paid1 := restrictedTonguesAt w N start (C.z1 + 1)
  let history1 := history0 ++ [paid1]
  let localTimes :=
    [C.z1 + 1 - shift, C.z2 + 1 - shift,
      C.z3 + 1 - shift, C.z4 + 1 - shift,
      C.z5 + 1 - shift]
  change NoveltyCoverOn w N start
    [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1]
    history0 4
  have o12 : C.z1 < C.z2 := C.order12
  have o23 : C.z2 < C.z3 := C.order23
  have o34 : C.z3 < C.z4 := C.order34
  have o45 : C.z4 < C.z5 := C.order45
  have hshift : shift ≤ C.z1 + 1 :=
    Nat.le_trans (Nat.le_add_right shift (approach.length + 1))
      hdeadline
  have hperiodic : EventuallyPeriodic w localStart := by
    have hmerge : A.ChangedForwardMerge
        (ManufacturedReflector.flip R) :=
      A.changedForwardMerge_of_forward_contact
        (ManufacturedReflector.flip R)
        hrouteSplit happroach hpaths harrive hpath hold holdOriented
        hswitch hchanged holdGroove hforward
    simpa [localStart] using hmerge.eventuallyPeriodic
  have hlive : ∀ d, ∃ finish, stepN w d localStart = some finish :=
    hperiodic.stepN_some_all
  have hleadHistorical : ∀ j, j ≤ approach.length + 1 →
      restrictedTonguesAt w N localStart j ∈ history1 := by
    intro j hj
    obtain ⟨finish, hfinish⟩ := hlive j
    have hshiftVector := restrictedTonguesAt_add_of_reach
      (N := N) (d := j) hreach hfinish
    rw [← hshiftVector]
    apply C.prefix_through_z1_paid
    omega
  have hlocalCover :
      NoveltyCoverOn w N localStart localTimes history1 3 := by
    apply A.forward_contact_exact_three_novelty R
      hrouteSplit happroach hpaths harrive hpath hold holdOriented
      hswitch hchanged holdGroove hforward
    · simpa [localStart] using hleadHistorical
  have htransport : ∀ t, shift ≤ t →
      restrictedTonguesAt w N localStart (t - shift) =
        restrictedTonguesAt w N start t := by
    intro t ht
    obtain ⟨finish, hfinish⟩ := hlive (t - shift)
    have hshiftVector := restrictedTonguesAt_add_of_reach
      (N := N) (d := t - shift) hreach hfinish
    rw [← hshiftVector]
    congr 1
    omega
  obtain ⟨fresh, hfreshLength, hlocalMem⟩ := hlocalCover
  have hm1 : restrictedTonguesAt w N start (C.z1 + 1) ∈
      history1 ++ fresh := by
    have hm := hlocalMem (C.z1 + 1 - shift) (by simp [localTimes])
    rw [htransport (C.z1 + 1) hshift] at hm
    exact hm
  have hm2 : restrictedTonguesAt w N start (C.z2 + 1) ∈
      history1 ++ fresh := by
    have hm := hlocalMem (C.z2 + 1 - shift) (by simp [localTimes])
    rw [htransport (C.z2 + 1) (by omega)] at hm
    exact hm
  have hm3 : restrictedTonguesAt w N start (C.z3 + 1) ∈
      history1 ++ fresh := by
    have hm := hlocalMem (C.z3 + 1 - shift) (by simp [localTimes])
    rw [htransport (C.z3 + 1) (by omega)] at hm
    exact hm
  have hm4 : restrictedTonguesAt w N start (C.z4 + 1) ∈
      history1 ++ fresh := by
    have hm := hlocalMem (C.z4 + 1 - shift) (by simp [localTimes])
    rw [htransport (C.z4 + 1) (by omega)] at hm
    exact hm
  have hm5 : restrictedTonguesAt w N start (C.z5 + 1) ∈
      history1 ++ fresh := by
    have hm := hlocalMem (C.z5 + 1 - shift) (by simp [localTimes])
    rw [htransport (C.z5 + 1) (by omega)] at hm
    exact hm
  let fresh4 := paid1 :: fresh
  refine ⟨fresh4, ?_, ?_⟩
  · dsimp [fresh4]
    omega
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · simpa [history1, fresh4, List.append_assoc] using hm1
    · simpa [history1, fresh4, List.append_assoc] using hm2
    · simpa [history1, fresh4, List.append_assoc] using hm3
    · simpa [history1, fresh4, List.append_assoc] using hm4
    · simpa [history1, fresh4, List.append_assoc] using hm5

/-- Exact-lead form of the early changed-forward contradiction. -/
theorem RawOverlappingFiveWindowReduction.early_forward_contact_exact_false
    {w : Wiring} {N g e shift p x : Nat}
    (hN : ∀ a b, w.link a = some b → a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (A : ManufacturedReflector w g e)
    (R : ManufacturedFlipReflector w e g)
    {approach suffix path : List Passage}
    {u v : Tongues} {old : Passage}
    (hrouteSplit : A.orientedRoute
        (ManufacturedReflector.flip R).activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w
      (g, (ManufacturedReflector.flip R).activatedState)
        approach (p, u))
    (hpaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ (ManufacturedReflector.flip R).toSupported.paths)
    (hold : old ∈ path)
    (holdOriented : old ∈
      (ManufacturedReflector.flip R).orientedRoute u)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3))
    (holdGroove : arrive u old.2 = (old.1, u))
    (hforward : x = old.2)
    (hreach : stepN w shift start = some
      (g, (ManufacturedReflector.flip R).activatedState))
    (hdeadline : shift + (approach.length + 1) ≤ C.z1 + 1) : False := by
  exact C.toSixEventReduction.no_tail_four_cover hN
    (C.early_forward_contact_exact_tail_four_cover A R
      hrouteSplit happroach hpaths harrive hpath hold holdOriented
      hswitch hchanged holdGroove hforward hreach hdeadline)

end GeneralN
