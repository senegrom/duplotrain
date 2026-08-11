import TrackGlobalRepairSimple

/-!
# Activated-state lead certificate for changed-forward splices

The existing strengthened splice package retains switch-simplicity of the
fresh approach, but not the original trace from the protected reflector's
activated state.  The latter is exactly the certificate needed for phase
counting.  This variant exports both that trace and membership of the approach
in the current repair route.
-/

namespace GeneralN

/-- The changed-forward splice package with the original activated-state
approach retained. -/
theorem ManufacturedReflector.ChangedForwardMerge.spliced_lobe_reflector_active_lead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.ChangedForwardMerge B) :
    ∃ (entry mouth returnPort outside : Nat)
        (oldPrefix oldTail approach candy : List Passage)
        (state : Tongues) (leadSteps tailSteps : Nat),
      (entry, mouth) ∈ B.orientedRoute state ∧
      B.orientedRoute state =
        oldPrefix ++ (entry, mouth) :: oldTail ∧
      PhysicalTrace w (outside, state) oldTail
        (B.orientedFinish state, state) ∧
      PhysicalTrace w (g, state) approach (returnPort, state) ∧
      SwitchSimple approach ∧
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
       stepN w leadSteps (g, B.activatedState) =
         some (outside, flipAt state (mouth / 3)) ∧
       stepN w tailSteps (outside, state) =
         some (g, B.toSupported.action.apply state) ∧
       leadSteps = approach.length + 1 ∧
       B.toSupported.travel = oldPrefix.length + 1 + tailSteps ∧
       approach.length + 1 ≤ A.toSupported.travel ∧
       PhysicalTrace w (g, B.activatedState) approach
         (returnPort, state) ∧
       (∀ passage ∈ approach,
         passage ∈ A.orientedRoute B.activatedState) := by
  obtain ⟨approach, p, x, suffix, u, v, _path, _old,
      oriented, repaired, hsplit, happroach, hpaths, harrive,
      _hpath, _hold, _holdSwitch, hchanged, horiented,
      horientedGroove, _horientedSwitch, hforward,
      hrepair, hrestored⟩ := hmerge
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
  have hroute := B.orientedRoute_trace u hpaths
  have hrouteSimple := B.orientedRoute_simple u
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  have hOldPrefixData := simple_grooved_trace_prefix_to_occurrence
    hroute hrouteSplit hrouteGrooved hrouteSimple
  have hOldPrefixGrooved : PassagesGrooved u oldPrefix := by
    intro passage hp
    exact hrouteGrooved passage (by
      rw [hrouteSplit]
      exact List.mem_append_left _ hp)

  have hApproachSimple : SwitchSimple approach := by
    have hsimple :=
      A.orientedRoute_simple
        (ManufacturedReflector.activatedState B)
    unfold SwitchSimple at hsimple ⊢
    rw [hsplit] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    exact (List.nodup_append.mp hsimple).1
  have hApproachGrooved : PassagesGrooved u approach :=
    happroach.grooved_of_switchSimple hApproachSimple
  have hApproachForeign : ∀ passage ∈ approach,
      passageSwitch passage ≠ p / 3 := by
    have hsimple :=
      A.orientedRoute_simple
        (ManufacturedReflector.activatedState B)
    unfold SwitchSimple at hsimple
    rw [hsplit] at hsimple
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
      obtain ⟨old, holdMem, holdEq⟩ := List.mem_map.mp horiginal
      intro hmouth
      apply hOldPrefixData.2 old holdMem
      exact holdEq.trans (hmouth.trans hsa)
    · intro hmouth
      apply hApproachForeign passage hnew
      exact hmouth.trans hsp

  have hback := physicalTrace_contact_retraces_prefix
    hOldPrefixData.1 hOldPrefixGrooved B.entryEdge horientedGroove
  have hforwardTrace :=
    happroach.replay_grooved u hApproachGrooved
  have hsplice :
      PhysicalTrace w (s, u) ((s, a) :: candy) (p, u) := by
    simpa [candy, List.append_assoc] using hback.append hforwardTrace
  have hSpliceGrooved :
      PassagesGrooved u ((s, a) :: candy) := by
    intro passage hpassage
    rcases List.mem_cons.mp hpassage with hhead | htail
    · simpa [hhead] using groove_forward horientedGroove
    · exact hCandyGrooved passage htail

  have hroute' := hroute
  rw [hrouteSplit] at hroute'
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
        have hforward := groove_forward horientedGroove
        rw [hOldArrive] at hforward
        exact congrArg Prod.snd hforward
      subst oldAfter
      have hcontactTrace : PhysicalTrace w (a, u) [(a, s)]
          (outside, u) :=
        PhysicalTrace.cons (groove_forward horientedGroove) hmouth
          (PhysicalTrace.nil _)
      have hlead := hOldPrefixData.1.append hcontactTrace
      have hleadSplit : B.orientedRoute u =
          (oldPrefix ++ [(a, s)]) ++ oldTail := by
        rw [hrouteSplit]
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
          rw [hsplit]
          simp
          omega
        have hrouteLe :=
          A.orientedRoute_length_le_travel B.activatedState
        omega
      have hApproachRoute : ∀ passage ∈ approach,
          passage ∈ A.orientedRoute B.activatedState := by
        intro passage hp
        rw [hsplit]
        exact List.mem_append_left _ hp
      refine ⟨a, s, p, outside, oldPrefix, oldTail, approach,
        candy, u, approach.length + 1, tailSteps, horiented,
        hrouteSplit, hOldRest, hforwardTrace, hApproachSimple,
        hApproachGrooved,
        (by
          intro passage hpassage
          simpa [hsp] using hApproachForeign passage hpassage), rfl,
        haBranch, hsStem, hmouth,
        hap, hSpliceGrooved, hsplice, hcrossed, hpaths,
        hCandyGrooved, hCandyForeign, ?_, hreach, hcomplete,
        rfl, htailLen, happroachLe, happroach, hApproachRoute⟩
      exact stem_lobe_isReflector_foreign w candy
        hsStem haBranch hpBranch hsa hsp hap hCandyForeign
        hsplice.linked hsplice.last_link hmouth

end GeneralN
