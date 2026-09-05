import RunwaySpliceNovelty

/-!
# Pointwise phase tracking through theta contacts

The theta dichotomy (capture or repair) is here upgraded from an endpoint
statement to a pointwise one: at *every* step of a capture the tongue vector
is one of two phases (the disturbed vector and the restored vector), and at
every step of a repairing traversal it is one of three (the disturbed
vector, the restored vector, and the traversal's own outgoing vector).

No switch-count hypothesis appears anywhere: phase covers are blind to
lengths.  The proofs replay the exact endpoint constructions and track the
tongue vector through their three segments:

* the switch-simple prefix before the contact is grooved at the disturbed
  state (the contact switch does not occur on it), so the vector is
  constant there;
* a capture continues into the old mouth and restores the flip
  (`capture_from_mouth_two_phase`); a repair crosses the contacted passage
  trailing-first, restoring the flip in one step;
* after a repair the walk sits exactly on the grooved trajectory of the
  full traversal, so the remaining steps inherit its two-phase law.
-/

namespace GeneralN

/-- Two-phase law for a flip traversal, in liveness-carrying `stepN` form. -/
theorem ManufacturedFlipReflector.travel_two_phase_stepN
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    {d : Nat} (hd : d ≤ 2 * A.runway.length + A.candy.length + 2) :
    ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
      (phase = state ∨ phase = flipAt state A.actionSwitch) := by
  have hA' : PathGrooves
      (ManufacturedReflector.flip A).toSupported.paths state := hA
  have hd' : d ≤ (ManufacturedReflector.flip A).toSupported.travel := hd
  have hrun := ((ManufacturedReflector.flip A).toSupported.run state hA').1
  obtain ⟨mid, hmid⟩ := stepN_prefix_some hd' hrun
  rcases mid with ⟨port, phase⟩
  have hphase :=
    (ManufacturedReflector.flip A).travel_two_phase_tongues state hA' hd'
  have hph : tonguesAt w (g, state) d = phase := by
    simp [tonguesAt, hmid]
  rcases hphase with h | h
  · exact ⟨port, phase, hmid, Or.inl (hph.symm.trans h)⟩
  · have hout : phase =
        (ManufacturedReflector.flip A).toSupported.action.apply state :=
      hph.symm.trans h
    exact ⟨port, phase, hmid, Or.inr hout⟩

/-- The arms of a flip reflector select opposite tongue values. -/
private theorem theta_pointwise_arm_values_ne
    {w : Wiring} {g e : Nat}
    (B : ManufacturedFlipReflector w g e) :
    bval B.firstArm ≠ bval B.secondArm := by
  intro hval
  apply B.arms_ne
  calc
    B.firstArm = branchPort (B.firstArm / 3) (bval B.firstArm) :=
      (branchPort_bval B.firstArm_branch).symm
    _ = branchPort (B.secondArm / 3) (bval B.secondArm) := by
      rw [B.firstArm_switch, B.secondArm_switch, hval]
    _ = B.secondArm := branchPort_bval B.secondArm_branch

/-! ## Capture pointwise: the three contact geometries -/

section
variable {w : Wiring} {g e : Nat}
  (A : ManufacturedFlipReflector w g e)
  (B : ManufacturedFlipReflector w e g)
  (state : Tongues)
  (hA : PathGrooves [A.runway, A.candy] state)
  (hB : PathGrooves [B.runway, B.candy] state)
include w g e A B state hA hB

/-- Runway capture, pointwise: two phases throughout. -/
theorem manufactured_runway_theta_capture_pointwise
    {before after : List Passage} {x : Nat}
    (hoccurs : B.runway = before ++ (A.mouth, x) :: after) :
    ∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state) := by
  have hAcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  have hlinked : LinkedPassages w
      (before ++ (A.mouth, x) :: after) := by
    rw [← hoccurs]
    exact B.runwayTrace.linked
  have hgrooved : PassagesGrooved state
      (before ++ (A.mouth, x) :: after) := by
    rw [← hoccurs]
    exact (pathGrooves_pair.mp hB).1
  have hsimpleRunway : SwitchSimple B.runway := by
    have hs := B.simple
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hsimple : SwitchSimple
      (before ++ (A.mouth, x) :: after) := by
    rwa [← hoccurs]
  cases before with
  | nil =>
      have htrace := B.runwayTrace
      rw [hoccurs] at htrace
      have hstart : e = A.mouth := htrace.head_arrive.1
      refine ⟨A.candy.length + 2 + A.runway.length, ?_, ?_⟩
      · simpa [hstart] using hAcapture
      · intro d hd
        have hphase := A.capture_from_mouth_two_phase state
          (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2 hd
        simpa [hstart] using hphase
  | cons passage before =>
      rcases passage with ⟨r, y⟩
      have hconsLen : ((r, y) :: before).length = before.length + 1 := by
        simp
      have hprefixData := simple_grooved_prefix_to_occurrence
        hlinked hgrooved hsimple
      have htrace := B.runwayTrace
      rw [hoccurs] at htrace
      have hstart : e = r := htrace.head_arrive.1
      have hprefix :
          PhysicalTrace w (e, state) ((r, y) :: before)
            (A.mouth, state) := by
        simpa [hstart] using hprefixData.1
      have hforeign : ∀ passage ∈ (r, y) :: before,
          passageSwitch passage ≠ A.actionSwitch := by
        intro passage hp
        have hne := hprefixData.2 passage hp
        simpa [passageSwitch,
          ManufacturedFlipReflector.actionSwitch] using hne
      have hprefixSimple : SwitchSimple ((r, y) :: before) := by
        unfold SwitchSimple at hsimple ⊢
        simp only [List.map_append, List.map_cons] at hsimple
        exact (List.nodup_append.mp hsimple).1
      have hprefixGrooved : PassagesGrooved state ((r, y) :: before) :=
        hprefix.grooved_of_switchSimple hprefixSimple
      have hprefixGroovedFlip :
          PassagesGrooved (flipAt state A.actionSwitch)
            ((r, y) :: before) :=
        grooved_after_flip_other hprefixGrooved hforeign
      have hpreFlip := hprefix.flip_unvisited hforeign
      refine ⟨((r, y) :: before).length +
        (A.candy.length + 2 + A.runway.length), ?_, ?_⟩
      · exact theta_capture_after_unvisited_prefix
          hprefix hforeign hAcapture
      · intro d hd
        by_cases hdpre : d ≤ ((r, y) :: before).length
        · obtain ⟨port, hrun⟩ :=
            hprefix.grooved_prefix_tongues
              (flipAt state A.actionSwitch) hprefixGroovedFlip hdpre
          exact ⟨port, flipAt state A.actionSwitch, hrun, Or.inl rfl⟩
        · let rdepth := d - ((r, y) :: before).length
          have hrle : rdepth ≤ A.candy.length + 2 + A.runway.length := by
            dsimp [rdepth]
            omega
          have hdEq : d = ((r, y) :: before).length + rdepth := by
            dsimp [rdepth]
            omega
          obtain ⟨port, phase, hrunR, hphase⟩ :=
            A.capture_from_mouth_two_phase state
              (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2 hrle
          refine ⟨port, phase, ?_, hphase⟩
          rw [hdEq, stepN_add, hpreFlip.sound]
          simpa using hrunR

/-- Forward-candy capture, pointwise: two phases throughout. -/
theorem manufactured_candy_forward_theta_capture_pointwise
    (hselected : state B.actionSwitch = bval B.firstArm)
    {before after : List Passage} {x : Nat}
    (hoccurs : B.candy = before ++ (A.mouth, x) :: after) :
    ∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state) := by
  have hprefixData := B.forward_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hforeign : ∀ passage ∈
      B.runway ++ (B.mouth, B.firstArm) :: before,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hne
  have hcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  let pre := B.runway ++ (B.mouth, B.firstArm) :: before
  have hfullSimple : SwitchSimple
      (pre ++ (A.mouth, x) :: after) := by
    dsimp [pre]
    simpa [hoccurs, List.append_assoc] using B.simple
  have hpreSimple : SwitchSimple pre := by
    unfold SwitchSimple at hfullSimple ⊢
    simp only [List.map_append] at hfullSimple
    exact (List.nodup_append.mp hfullSimple).1
  have hpreGrooved : PassagesGrooved state pre :=
    hprefixData.1.grooved_of_switchSimple hpreSimple
  have hpreGroovedFlip :
      PassagesGrooved (flipAt state A.actionSwitch) pre :=
    grooved_after_flip_other hpreGrooved hforeign
  have hpreFlip := hprefixData.1.flip_unvisited hforeign
  refine ⟨pre.length + (A.candy.length + 2 + A.runway.length), ?_, ?_⟩
  · exact theta_capture_after_unvisited_prefix
      hprefixData.1 hforeign hcapture
  · intro d hd
    by_cases hdpre : d ≤ pre.length
    · obtain ⟨port, hrun⟩ :=
        hprefixData.1.grooved_prefix_tongues
          (flipAt state A.actionSwitch) hpreGroovedFlip hdpre
      exact ⟨port, flipAt state A.actionSwitch, hrun, Or.inl rfl⟩
    · let rdepth := d - pre.length
      have hrle : rdepth ≤ A.candy.length + 2 + A.runway.length := by
        dsimp [rdepth]
        omega
      have hdEq : d = pre.length + rdepth := by
        dsimp [rdepth]
        omega
      obtain ⟨port, phase, hrunR, hphase⟩ :=
        A.capture_from_mouth_two_phase state
          (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2 hrle
      refine ⟨port, phase, ?_, hphase⟩
      rw [hdEq, stepN_add, hpreFlip.sound]
      simpa using hrunR

/-- Reverse-candy capture, pointwise: two phases throughout. -/
theorem manufactured_candy_reverse_theta_capture_pointwise
    (hselected : state B.actionSwitch = bval B.secondArm)
    {before after : List Passage} {p : Nat}
    (hoccurs : B.candy = before ++ (p, A.mouth) :: after) :
    ∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state) := by
  have hprefixData := B.reverse_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hforeign : ∀ passage ∈
      B.runway ++
        (B.mouth, B.secondArm) :: reversePassages after,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hne
  have hcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  let pre := B.runway ++
    (B.mouth, B.secondArm) :: reversePassages after
  have hnotFirst : state B.actionSwitch ≠ bval B.firstArm := by
    intro hfirst
    exact theta_pointwise_arm_values_ne B
      (hfirst.symm.trans hselected)
  have hrouteSimple :=
    (ManufacturedReflector.flip B).orientedRoute_simple state
  have hdecomp :
      (ManufacturedReflector.flip B).orientedRoute state =
        pre ++ (A.mouth, p) :: reversePassages before := by
    simp only [ManufacturedReflector.orientedRoute, hnotFirst, if_false]
    dsimp [pre]
    rw [hoccurs, reversePassages_append]
    simp [reversePassages, List.append_assoc]
  rw [hdecomp] at hrouteSimple
  have hpreSimple : SwitchSimple pre := by
    unfold SwitchSimple at hrouteSimple ⊢
    simp only [List.map_append] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).1
  have hpreGrooved : PassagesGrooved state pre :=
    hprefixData.1.grooved_of_switchSimple hpreSimple
  have hpreGroovedFlip :
      PassagesGrooved (flipAt state A.actionSwitch) pre :=
    grooved_after_flip_other hpreGrooved hforeign
  have hpreFlip := hprefixData.1.flip_unvisited hforeign
  refine ⟨pre.length + (A.candy.length + 2 + A.runway.length), ?_, ?_⟩
  · exact theta_capture_after_unvisited_prefix
      hprefixData.1 hforeign hcapture
  · intro d hd
    by_cases hdpre : d ≤ pre.length
    · obtain ⟨port, hrun⟩ :=
        hprefixData.1.grooved_prefix_tongues
          (flipAt state A.actionSwitch) hpreGroovedFlip hdpre
      exact ⟨port, flipAt state A.actionSwitch, hrun, Or.inl rfl⟩
    · let rdepth := d - pre.length
      have hrle : rdepth ≤ A.candy.length + 2 + A.runway.length := by
        dsimp [rdepth]
        omega
      have hdEq : d = pre.length + rdepth := by
        dsimp [rdepth]
        omega
      obtain ⟨port, phase, hrunR, hphase⟩ :=
        A.capture_from_mouth_two_phase state
          (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2 hrle
      refine ⟨port, phase, ?_, hphase⟩
      rw [hdEq, stepN_add, hpreFlip.sound]
      simpa using hrunR

end

/-! ## Repair pointwise: the three contact geometries -/

/-- Shared tail argument: after the one-step repair the walk sits on the
grooved trajectory of the full traversal, inheriting its two-phase law. -/
private theorem theta_repair_tail_phase
    {w : Wiring} {e q : Nat} {u v : Tongues} {L total : Nat}
    (hmid : stepN w L (e, u) = some (q, u))
    (hphases : ∀ t, t ≤ total → ∃ port phase,
      stepN w t (e, u) = some (port, phase) ∧
        (phase = u ∨ phase = v))
    {r : Nat} (hr : L + r ≤ total) :
    ∃ port phase, stepN w r (q, u) = some (port, phase) ∧
      (phase = u ∨ phase = v) := by grind [stepN_add]

section
variable {w : Wiring} {g e : Nat}
  (A : ManufacturedFlipReflector w g e)
  (B : ManufacturedFlipReflector w e g)
  (state : Tongues)
include w g e A B state

/-- Runway repair, pointwise: three phases throughout. -/
theorem manufactured_runway_theta_repairs_pointwise
    (hB : PathGrooves [B.runway, B.candy] state)
    {before after : List Passage} {p : Nat}
    (hoccurs :
      B.runway = before ++ (p, A.mouth) :: after)
    {d : Nat}
    (hd : d ≤ 2 * B.runway.length + B.candy.length + 2) :
    ∃ port phase, stepN w d (e, flipAt state A.actionSwitch) =
      some (port, phase) ∧
      (phase = flipAt state A.actionSwitch ∨ phase = state ∨
        phase = flipAt state B.actionSwitch) := by
  have hsimpleRunway : SwitchSimple B.runway := by
    have hs := B.simple
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hrunwayGrooved : PassagesGrooved state B.runway :=
    (pathGrooves_pair.mp hB).1
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    B.runwayTrace hoccurs hrunwayGrooved hsimpleRunway
  have hmem : (p, A.mouth) ∈ B.runway := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hgrooveBack : arrive state A.mouth = (p, state) :=
    hrunwayGrooved (p, A.mouth) hmem
  have hforward : arrive state p = (A.mouth, state) :=
    groove_forward hgrooveBack
  have hpk : p / 3 = A.actionSwitch := by
    have hs := arrive_exit_switch state p
    rw [hforward] at hs
    simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm
  have hpbranch : p % 3 ≠ 0 := by
    intro hp
    have hne := arrive_exit_ne state p
    rw [hforward] at hne
    have hmouthStem := A.mouth_is_stem
    have hpk' : p / 3 = A.mouth / 3 := by
      simpa [ManufacturedFlipReflector.actionSwitch] using hpk
    apply hne
    omega
  have hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch, hpk] using hne
  have hlinked : LinkedPassages w
      (before ++ (p, A.mouth) :: after) := by
    rw [← hoccurs]
    exact B.runwayTrace.linked
  obtain ⟨q, hlink⟩ : ∃ q, w.link A.mouth = some q := by
    cases after with
    | nil =>
        have htrace := B.runwayTrace
        rw [hoccurs] at htrace
        obtain ⟨middle, hbeforeTrace, htargetTrace⟩ :=
          htrace.split_append
        have hlast := htargetTrace.last_link
        exact ⟨B.mouth, by simpa [lastPassageExit] using hlast⟩
    | cons passage rest =>
        rcases passage with ⟨q, y⟩
        exact ⟨q, linked_after_occurrence hlinked⟩
  have hbeforeSimple : SwitchSimple before := by
    have hs := hsimpleRunway
    rw [hoccurs] at hs
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hbeforeGrooved : PassagesGrooved state before :=
    hprefixData.1.grooved_of_switchSimple hbeforeSimple
  have hbeforeGroovedFlip :
      PassagesGrooved (flipAt state A.actionSwitch) before :=
    grooved_after_flip_other hbeforeGrooved hforeign
  by_cases hdpre : d ≤ before.length
  · obtain ⟨port, hrun⟩ :=
      hprefixData.1.grooved_prefix_tongues
        (flipAt state A.actionSwitch) hbeforeGroovedFlip hdpre
    exact ⟨port, flipAt state A.actionSwitch, hrun, Or.inl rfl⟩
  · have hone : stepN w 1 (p, state) = some (q, state) := by
      simp [stepN, step, hforward, hlink]
    have hmidGrooved :
        stepN w (before.length + 1) (e, state) = some (q, state) := by
      rw [stepN_add, hprefixData.1.sound]
      simpa using hone
    have hpreFlip := hprefixData.1.flip_unvisited hforeign
    have hrepairArrive :
        arrive (flipAt state A.actionSwitch) p = (A.mouth, state) := by
      rw [← hpk]
      exact flipped_passage_forward_trailing hforward hpbranch
    have honeFlip : stepN w 1 (p, flipAt state A.actionSwitch) =
        some (q, state) := by
      simp [stepN, step, hrepairArrive, hlink]
    have hmidFlip :
        stepN w (before.length + 1) (e, flipAt state A.actionSwitch) =
          some (q, state) := by
      rw [stepN_add, hpreFlip.sound]
      simpa using honeFlip
    have hRlen : B.runway.length =
        before.length + 1 + after.length := by
      rw [hoccurs]
      simp only [List.length_append, List.length_cons]
      omega
    let rdepth := d - (before.length + 1)
    have hdEq : d = (before.length + 1) + rdepth := by
      dsimp [rdepth]
      omega
    have habs : (before.length + 1) + rdepth ≤
        2 * B.runway.length + B.candy.length + 2 := by
      omega
    obtain ⟨port, phase, hrunR, hphase⟩ :=
      theta_repair_tail_phase hmidGrooved
        (fun t ht => B.travel_two_phase_stepN state hB ht) habs
    refine ⟨port, phase, ?_, ?_⟩
    · rw [hdEq, stepN_add, hmidFlip]
      simpa using hrunR
    · rcases hphase with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- Forward-candy repair, pointwise: three phases throughout. -/
theorem manufactured_candy_forward_theta_repairs_pointwise
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.firstArm)
    {before after : List Passage} {p : Nat}
    (hoccurs : B.candy = before ++ (p, A.mouth) :: after)
    {d : Nat}
    (hd : d ≤ 2 * B.runway.length + B.candy.length + 2) :
    ∃ port phase, stepN w d (e, flipAt state A.actionSwitch) =
      some (port, phase) ∧
      (phase = flipAt state A.actionSwitch ∨ phase = state ∨
        phase = flipAt state B.actionSwitch) := by
  let pre := B.runway ++ (B.mouth, B.firstArm) :: before
  have hprefixData := B.forward_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hmem : (p, A.mouth) ∈ B.candy := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hgrooveBack : arrive state A.mouth = (p, state) :=
    (pathGrooves_pair.mp hB).2 (p, A.mouth) hmem
  have hforward : arrive state p = (A.mouth, state) :=
    groove_forward hgrooveBack
  have hpk : p / 3 = A.actionSwitch := by
    have hs := arrive_exit_switch state p
    rw [hforward] at hs
    simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm
  have hpbranch : p % 3 ≠ 0 := by
    intro hp
    have hne := arrive_exit_ne state p
    rw [hforward] at hne
    have hm := A.mouth_is_stem
    have hpk' : p / 3 = A.mouth / 3 := by
      simpa [ManufacturedFlipReflector.actionSwitch] using hpk
    apply hne
    omega
  have hforeign : ∀ passage ∈ pre,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [pre, passageSwitch, hpk] using hne
  obtain ⟨q, hlink⟩ : ∃ q, w.link A.mouth = some q := by
    cases after with
    | nil =>
        have hlast := B.candyTrace.last_link
        rw [hoccurs, lastPassageExit_append_cons] at hlast
        exact ⟨B.secondArm, hlast⟩
    | cons passage rest =>
        rcases passage with ⟨q, y⟩
        have hcandyLinked : LinkedPassages w B.candy := by
          have htrace := B.candyTrace
          cases htrace with
          | cons harrive hheadLink candyTail =>
              exact candyTail.linked
        rw [hoccurs] at hcandyLinked
        exact ⟨q, linked_after_occurrence hcandyLinked⟩
  have hfullSimple : SwitchSimple
      (pre ++ (p, A.mouth) :: after) := by
    dsimp [pre]
    simpa [hoccurs, List.append_assoc] using B.simple
  have hpreSimple : SwitchSimple pre := by
    unfold SwitchSimple at hfullSimple ⊢
    simp only [List.map_append] at hfullSimple
    exact (List.nodup_append.mp hfullSimple).1
  have hpreGrooved : PassagesGrooved state pre :=
    hprefixData.1.grooved_of_switchSimple hpreSimple
  have hpreGroovedFlip :
      PassagesGrooved (flipAt state A.actionSwitch) pre :=
    grooved_after_flip_other hpreGrooved hforeign
  by_cases hdpre : d ≤ pre.length
  · obtain ⟨port, hrun⟩ :=
      hprefixData.1.grooved_prefix_tongues
        (flipAt state A.actionSwitch) hpreGroovedFlip hdpre
    exact ⟨port, flipAt state A.actionSwitch, hrun, Or.inl rfl⟩
  · have hone : stepN w 1 (p, state) = some (q, state) := by
      simp [stepN, step, hforward, hlink]
    have hmidGrooved :
        stepN w (pre.length + 1) (e, state) = some (q, state) := by
      rw [stepN_add, hprefixData.1.sound]
      simpa using hone
    have hpreFlip := hprefixData.1.flip_unvisited hforeign
    have hrepairArrive :
        arrive (flipAt state A.actionSwitch) p = (A.mouth, state) := by
      rw [← hpk]
      exact flipped_passage_forward_trailing hforward hpbranch
    have honeFlip : stepN w 1 (p, flipAt state A.actionSwitch) =
        some (q, state) := by
      simp [stepN, step, hrepairArrive, hlink]
    have hmidFlip :
        stepN w (pre.length + 1) (e, flipAt state A.actionSwitch) =
          some (q, state) := by
      rw [stepN_add, hpreFlip.sound]
      simpa using honeFlip
    have hClen : B.candy.length =
        before.length + 1 + after.length := by
      rw [hoccurs]
      simp only [List.length_append, List.length_cons]
      omega
    have hpreLen : pre.length =
        B.runway.length + 1 + before.length := by
      dsimp [pre]
      simp only [List.length_append, List.length_cons]
      omega
    let rdepth := d - (pre.length + 1)
    have hdEq : d = (pre.length + 1) + rdepth := by
      dsimp [rdepth]
      omega
    have habs : (pre.length + 1) + rdepth ≤
        2 * B.runway.length + B.candy.length + 2 := by
      omega
    obtain ⟨port, phase, hrunR, hphase⟩ :=
      theta_repair_tail_phase hmidGrooved
        (fun t ht => B.travel_two_phase_stepN state hB ht) habs
    refine ⟨port, phase, ?_, ?_⟩
    · rw [hdEq, stepN_add, hmidFlip]
      simpa using hrunR
    · rcases hphase with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- Reverse-candy repair, pointwise: three phases throughout. -/
theorem manufactured_candy_reverse_theta_repairs_pointwise
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.secondArm)
    {before after : List Passage} {x : Nat}
    (hoccurs : B.candy = before ++ (A.mouth, x) :: after)
    {d : Nat}
    (hd : d ≤ 2 * B.runway.length + B.candy.length + 2) :
    ∃ port phase, stepN w d (e, flipAt state A.actionSwitch) =
      some (port, phase) ∧
      (phase = flipAt state A.actionSwitch ∨ phase = state ∨
        phase = flipAt state B.actionSwitch) := by
  let pre := B.runway ++
    (B.mouth, B.secondArm) :: reversePassages after
  have hprefixData := B.reverse_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hmem : (A.mouth, x) ∈ B.candy := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hgroove : arrive state x = (A.mouth, state) :=
    (pathGrooves_pair.mp hB).2 (A.mouth, x) hmem
  have hxk : x / 3 = A.actionSwitch := by
    have hs := arrive_exit_switch state x
    rw [hgroove] at hs
    simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm
  have hxbranch : x % 3 ≠ 0 := by
    intro hx
    have hne := arrive_exit_ne state x
    rw [hgroove] at hne
    have hm := A.mouth_is_stem
    have hxk' : x / 3 = A.mouth / 3 := by
      simpa [ManufacturedFlipReflector.actionSwitch] using hxk
    apply hne
    omega
  have hforeign : ∀ passage ∈ pre,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [pre, passageSwitch, hxk] using hne
  have hcandyLinked : LinkedPassages w B.candy := by
    have htrace := B.candyTrace
    cases htrace with
    | cons harrive hheadLink candyTail => exact candyTail.linked
  obtain ⟨q, hlink⟩ : ∃ q, w.link A.mouth = some q := by
    cases before with
    | nil =>
        have htrace := B.candyTrace
        rw [hoccurs] at htrace
        cases htrace with
        | @cons p₀ x₀ q₀ u₀ v₀ passages finish
            harrive hheadLink candyTail =>
            have hstart : q₀ = A.mouth := candyTail.head_arrive.1
            rw [hstart] at hheadLink
            exact ⟨B.firstArm, w.symm _ _ hheadLink⟩
    | cons passage rest =>
        rcases passage with ⟨r, y⟩
        have hcandyLinked' := hcandyLinked
        rw [hoccurs] at hcandyLinked'
        have hboundary := linked_boundary_of_append hcandyLinked'
        exact ⟨lastPassageExit y rest, w.symm _ _ hboundary⟩
  have hnotFirst : state B.actionSwitch ≠ bval B.firstArm := by
    intro hfirst
    exact theta_pointwise_arm_values_ne B
      (hfirst.symm.trans hselected)
  have hrouteSimple :=
    (ManufacturedReflector.flip B).orientedRoute_simple state
  have hdecomp :
      (ManufacturedReflector.flip B).orientedRoute state =
        pre ++ (x, A.mouth) :: reversePassages before := by
    simp only [ManufacturedReflector.orientedRoute, hnotFirst, if_false]
    dsimp [pre]
    rw [hoccurs, reversePassages_append]
    simp [reversePassages, List.append_assoc]
  rw [hdecomp] at hrouteSimple
  have hpreSimple : SwitchSimple pre := by
    unfold SwitchSimple at hrouteSimple ⊢
    simp only [List.map_append] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).1
  have hpreGrooved : PassagesGrooved state pre :=
    hprefixData.1.grooved_of_switchSimple hpreSimple
  have hpreGroovedFlip :
      PassagesGrooved (flipAt state A.actionSwitch) pre :=
    grooved_after_flip_other hpreGrooved hforeign
  by_cases hdpre : d ≤ pre.length
  · obtain ⟨port, hrun⟩ :=
      hprefixData.1.grooved_prefix_tongues
        (flipAt state A.actionSwitch) hpreGroovedFlip hdpre
    exact ⟨port, flipAt state A.actionSwitch, hrun, Or.inl rfl⟩
  · have hone : stepN w 1 (x, state) = some (q, state) := by
      simp [stepN, step, hgroove, hlink]
    have hmidGrooved :
        stepN w (pre.length + 1) (e, state) = some (q, state) := by
      rw [stepN_add, hprefixData.1.sound]
      simpa using hone
    have hpreFlip := hprefixData.1.flip_unvisited hforeign
    have hrepairArrive :
        arrive (flipAt state A.actionSwitch) x = (A.mouth, state) := by
      rw [← hxk]
      exact flipped_passage_forward_trailing hgroove hxbranch
    have honeFlip : stepN w 1 (x, flipAt state A.actionSwitch) =
        some (q, state) := by
      simp [stepN, step, hrepairArrive, hlink]
    have hmidFlip :
        stepN w (pre.length + 1) (e, flipAt state A.actionSwitch) =
          some (q, state) := by
      rw [stepN_add, hpreFlip.sound]
      simpa using honeFlip
    have hClen : B.candy.length =
        before.length + 1 + after.length := by
      rw [hoccurs]
      simp only [List.length_append, List.length_cons]
      omega
    have hpreLen : pre.length =
        B.runway.length + 1 + after.length := by
      dsimp [pre]
      simp only [List.length_append, List.length_cons,
        reversePassages_length]
      omega
    let rdepth := d - (pre.length + 1)
    have hdEq : d = (pre.length + 1) + rdepth := by
      dsimp [rdepth]
      omega
    have habs : (pre.length + 1) + rdepth ≤
        2 * B.runway.length + B.candy.length + 2 := by
      omega
    obtain ⟨port, phase, hrunR, hphase⟩ :=
      theta_repair_tail_phase hmidGrooved
        (fun t ht => B.travel_two_phase_stepN state hB ht) habs
    refine ⟨port, phase, ?_, ?_⟩
    · rw [hdEq, stepN_add, hmidFlip]
      simpa using hrunR
    · rcases hphase with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-! ## The pointwise dichotomy -/

/-- **Pointwise support-fault dichotomy.**  When the disturbed walk enters
the supporting structure, it is either captured (two phases, returning with
the flip undone) or the traversal itself repairs the flip (three phases,
completing with the reflector's own action).  No switch-count hypothesis is
needed. -/
theorem manufactured_support_fault_dichotomy_pointwise
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state)) ∨
    (stepN w (2 * B.runway.length + B.candy.length + 2)
        (e, flipAt state A.actionSwitch) =
          some (g, flipAt state B.actionSwitch) ∧
      ∀ d, d ≤ 2 * B.runway.length + B.candy.length + 2 →
        ∃ port phase,
          stepN w d (e, flipAt state A.actionSwitch) =
            some (port, phase) ∧
          (phase = flipAt state A.actionSwitch ∨ phase = state ∨
            phase = flipAt state B.actionSwitch)) := by
  obtain ⟨path, hp, passage, hmem, hsw⟩ := hcontact
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · rcases passage with ⟨p, x⟩
    obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
    have hstem := B.runwayTrace.passage_stem_endpoint (p, x) hmem
    change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
    change p / 3 = A.actionSwitch at hsw
    have hmouth : A.mouth = 3 * A.actionSwitch := by
      have hs := A.mouth_is_stem
      unfold ManufacturedFlipReflector.actionSwitch
      omega
    rcases hstem with hpStem | hxStem
    · have hpMouth : p = A.mouth := by omega
      subst p
      left
      exact manufactured_runway_theta_capture_pointwise
        A B state hA hB hoccurs
    · have hxMouth : x = A.mouth := by omega
      right
      constructor
      · exact manufactured_runway_theta_repairs A B state hB
          (by simpa [hxMouth] using hoccurs)
      · intro d hd
        exact manufactured_runway_theta_repairs_pointwise
          A B state hB (by simpa [hxMouth] using hoccurs) hd
  · rcases passage with ⟨p, x⟩
    obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
    have hstem := B.candyTrace.passage_stem_endpoint (p, x)
      (List.mem_cons_of_mem _ hmem)
    change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
    change p / 3 = A.actionSwitch at hsw
    have hmouth : A.mouth = 3 * A.actionSwitch := by
      have hs := A.mouth_is_stem
      unfold ManufacturedFlipReflector.actionSwitch
      omega
    rcases B.selected_arm state with hforward | hreverse
    · rcases hstem with hpStem | hxStem
      · have hpMouth : p = A.mouth := by omega
        subst p
        left
        exact manufactured_candy_forward_theta_capture_pointwise
          A B state hA hB hforward hoccurs
      · have hxMouth : x = A.mouth := by omega
        right
        constructor
        · exact manufactured_candy_forward_theta_repairs A B state
            hB hforward (by simpa [hxMouth] using hoccurs)
        · intro d hd
          exact manufactured_candy_forward_theta_repairs_pointwise
            A B state hB hforward
            (by simpa [hxMouth] using hoccurs) hd
    · rcases hstem with hpStem | hxStem
      · have hpMouth : p = A.mouth := by omega
        right
        constructor
        · exact manufactured_candy_reverse_theta_repairs A B state
            hB hreverse (by simpa [hpMouth] using hoccurs)
        · intro d hd
          exact manufactured_candy_reverse_theta_repairs_pointwise
            A B state hB hreverse
            (by simpa [hpMouth] using hoccurs) hd
      · have hxMouth : x = A.mouth := by omega
        left
        exact manufactured_candy_reverse_theta_capture_pointwise
          A B state hA hB hreverse
            (by simpa [hxMouth] using hoccurs)

end

end GeneralN
