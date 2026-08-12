import TrackQuantitativeRouteSharp

/-!
# Theta captures cost at most `2*N+1`

The old-reflector return used by a theta capture is

    candy.length + 2 + runway.length.

The complete recorded route `runway ++ mouthPassage :: candy` is
switch-simple, hence has at most `N` passages.  The return above is exactly
one step longer, so it is at most `N+1`, not `2*N`.  Adding the foreign
switch-simple prefix (`<= N`) gives a capture bound `2*N+1`.
-/

namespace GeneralN

private theorem ManufacturedFlipReflector.capture_tail_le_succ
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e) :
    A.candy.length + 2 + A.runway.length ≤ N + 1 := by
  have htrace : PhysicalTrace w (g, A.base)
      (A.runway ++ (A.mouth, A.firstArm) :: A.candy)
      (A.secondArm, A.returnState) :=
    A.runwayTrace.append A.candyTrace
  have hlen := htrace.switchSimple_length_le_switches hN A.simple
  simp only [List.length_append, List.length_cons] at hlen
  omega

/-- Runway theta capture within `2*N+1`. -/
theorem manufactured_runway_theta_capture_within_two_succ
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    {before after : List Passage} {x : Nat}
    (hoccurs : B.runway = before ++ (A.mouth, x) :: after) :
    ∃ travel,
      travel ≤ 2 * N + 1 ∧
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
  have hAcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  have hcaptureLe := A.capture_tail_le_succ hN
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
      refine ⟨A.candy.length + 2 + A.runway.length, by omega, ?_⟩
      simpa [hstart] using hAcapture
  | cons passage before =>
      rcases passage with ⟨r, y⟩
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
        unfold SwitchSimple at hsimpleRunway ⊢
        rw [hoccurs] at hsimpleRunway
        simp only [List.map_append, List.map_cons] at hsimpleRunway
        exact (List.nodup_append.mp hsimpleRunway).1
      have hprefixLe : ((r, y) :: before).length ≤ N :=
        hprefix.switchSimple_length_le_switches hN hprefixSimple
      refine ⟨((r, y) :: before).length +
        (A.candy.length + 2 + A.runway.length), by omega, ?_⟩
      exact theta_capture_after_unvisited_prefix
        hprefix hforeign hAcapture

/-- Forward-candy theta capture within `2*N+1`. -/
theorem manufactured_candy_forward_theta_capture_within_two_succ
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.firstArm)
    {before after : List Passage} {x : Nat}
    (hoccurs : B.candy = before ++ (A.mouth, x) :: after) :
    ∃ travel,
      travel ≤ 2 * N + 1 ∧
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
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
  have hcaptureLe := A.capture_tail_le_succ hN
  let pre := B.runway ++ (B.mouth, B.firstArm) :: before
  have hfullSimple : SwitchSimple
      (pre ++ (A.mouth, x) :: after) := by
    dsimp [pre]
    simpa [hoccurs, List.append_assoc] using B.simple
  have hpreSimple : SwitchSimple pre := by
    unfold SwitchSimple at hfullSimple ⊢
    simp only [List.map_append] at hfullSimple
    exact (List.nodup_append.mp hfullSimple).1
  have hpreLe : pre.length ≤ N :=
    hprefixData.1.switchSimple_length_le_switches hN hpreSimple
  refine ⟨pre.length +
    (A.candy.length + 2 + A.runway.length), by omega, ?_⟩
  exact theta_capture_after_unvisited_prefix
    hprefixData.1 hforeign hcapture

private theorem ManufacturedFlipReflector.arm_values_ne_tighter
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

/-- Reverse-candy theta capture within `2*N+1`. -/
theorem manufactured_candy_reverse_theta_capture_within_two_succ
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.secondArm)
    {before after : List Passage} {p : Nat}
    (hoccurs : B.candy = before ++ (p, A.mouth) :: after) :
    ∃ travel,
      travel ≤ 2 * N + 1 ∧
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
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
  have hcaptureLe := A.capture_tail_le_succ hN
  let pre := B.runway ++
    (B.mouth, B.secondArm) :: reversePassages after
  have hnotFirst : state B.actionSwitch ≠ bval B.firstArm := by
    intro hfirst
    exact B.arm_values_ne_tighter (hfirst.symm.trans hselected)
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
  have hpreLe : pre.length ≤ N :=
    hprefixData.1.switchSimple_length_le_switches hN hpreSimple
  refine ⟨pre.length +
    (A.candy.length + 2 + A.runway.length), by omega, ?_⟩
  exact theta_capture_after_unvisited_prefix
    hprefixData.1 hforeign hcapture

/-- Orientation-free support fault with capture bounded by `2*N+1`. -/
theorem manufactured_support_fault_dichotomy_within_two_succ
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      travel ≤ 2 * N + 1 ∧
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w B.toSupported.travel
        (e, flipAt state A.actionSwitch) =
          some (g, flipAt state B.actionSwitch) := by
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
      exact manufactured_runway_theta_capture_within_two_succ
        hN A B state hA hB hoccurs
    · have hxMouth : x = A.mouth := by omega
      right
      simpa [ManufacturedFlipReflector.toSupported] using
        manufactured_runway_theta_repairs A B state hB
          (by simpa [hxMouth] using hoccurs)
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
        exact manufactured_candy_forward_theta_capture_within_two_succ
          hN A B state hA hB hforward hoccurs
      · have hxMouth : x = A.mouth := by omega
        right
        simpa [ManufacturedFlipReflector.toSupported] using
          manufactured_candy_forward_theta_repairs A B state
            hB hforward (by simpa [hxMouth] using hoccurs)
    · rcases hstem with hpStem | hxStem
      · have hpMouth : p = A.mouth := by omega
        right
        simpa [ManufacturedFlipReflector.toSupported] using
          manufactured_candy_reverse_theta_repairs A B state
            hB hreverse (by simpa [hpMouth] using hoccurs)
      · have hxMouth : x = A.mouth := by omega
        left
        exact manufactured_candy_reverse_theta_capture_within_two_succ
          hN A B state hA hB hreverse
            (by simpa [hxMouth] using hoccurs)

/-- One theta macro-step has length at most `6*N+1`. -/
theorem manufactured_theta_half_within_six_succ
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    ∃ travel, 0 < travel ∧ travel ≤ 6 * N + 1 ∧
      stepN w travel (g, state) =
        some (g, flipAt state B.actionSwitch) := by
  have hArun := (A.toSupported.run state hA).1
  have hBrun := (B.toSupported.run state hB).1
  change stepN w A.toSupported.travel (g, state) =
    some (e, flipAt state A.actionSwitch) at hArun
  change stepN w B.toSupported.travel (e, state) =
    some (g, flipAt state B.actionSwitch) at hBrun
  have hAt : A.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip A).travel_le_two_mul_switches hN
  have hBt : B.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip B).travel_le_two_mul_switches hN
  have hApos : 0 < A.toSupported.travel := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip A).travel_pos
  have hBpos : 0 < B.toSupported.travel := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip B).travel_pos
  rcases manufactured_support_fault_dichotomy_within_two_succ
      hN A B state hA hB hcontact with hcapture | hrepair
  · obtain ⟨captureTravel, hcaptureLe, hcapture⟩ := hcapture
    refine ⟨A.toSupported.travel + captureTravel + B.toSupported.travel,
      by omega, by omega, ?_⟩
    have hlen :
        A.toSupported.travel + captureTravel + B.toSupported.travel =
          A.toSupported.travel +
            (captureTravel + B.toSupported.travel) := by omega
    rw [hlen, stepN_add, hArun]
    simp only [Option.bind_some]
    rw [stepN_add, hcapture]
    exact hBrun
  · refine ⟨A.toSupported.travel + B.toSupported.travel,
      by omega, by omega, ?_⟩
    rw [stepN_add, hArun]
    exact hrepair

end GeneralN
