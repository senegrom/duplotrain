import ForeignSpliceNovelty

/-!
# Pointwise novelty of the runway splice

This file treats the runway case of the changed-forward splice (the candy
case is `ForeignSpliceNovelty.lean`): the selected old passage lies on the
runway of a manufactured flip reflector.
The untouched strict suffix is therefore itself a manufactured reflector,
while the changed-forward splice supplies an opposite explicit lobe.

All statements concern raw `Wiring`/`stepN` dynamics. Both the disjoint and
intersecting action cases use covered positive excursions, not periods. The
same two-phase lobe contract also covers splices into stay reflectors.
-/

namespace GeneralN

/-- Select the lobe's current orientation once. Every interior switch is
represented on this grooved route, in either direction. -/
theorem explicit_lobe_route_at
    {w : Wiring} {mouth entry returnPort : Nat}
    {state : Tongues} {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hforeign : ∀ passage ∈ candy, passageSwitch passage ≠ mouth / 3)
    (current : Tongues) (hcurrent : PassagesGrooved current candy)
    : ∃ route last, route.length = candy.length + 1 ∧
      PhysicalTrace w (mouth, current) route (last, current) ∧
      PassagesGrooved current route ∧
      arrive current last = (mouth, flipAt current (mouth / 3)) ∧
      ∀ old ∈ candy, ∃ passage ∈ route, passageSwitch passage = passageSwitch old := by
  have hreturnSwitch : returnPort / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state returnPort
    rw [hcrossed] at hs
    exact hs.symm
  obtain ⟨hbranch, hmouth, _⟩ := changed_arrival_is_trailing hcrossed
    (by simp [hreturnSwitch, flipAt])
  have hne : entry ≠ returnPort := by
    intro heq
    have hhead := hgrooved (mouth, entry) List.mem_cons_self
    rw [heq, hcrossed] at hhead
    have h := congrFun (Prod.mk.inj hhead).2 (mouth / 3)
    simp [flipAt] at h
  obtain ⟨route, last, hlen, hr, hg, hc, horient⟩ := stem_lobe_route w candy
    (by omega) hentryBranch hbranch hentrySwitch.symm hreturnSwitch.symm hne
    hforeign htrace.linked htrace.last_link current hcurrent
  refine ⟨route, last, hlen, hr, hg, hc, ?_⟩
  intro old hold
  rcases horient with rfl | rfl
  · exact ⟨old, List.mem_cons_of_mem _ hold, rfl⟩
  · exact ⟨(old.2, old.1), List.mem_cons_of_mem _ (reversePassage_mem hold),
      htrace.passage_exit_switch old (List.mem_cons_of_mem _ hold)⟩

/-- A lobe traversal exposes only its incoming and outgoing vectors. -/
theorem explicit_lobe_two_phase_at
    {w : Wiring} {mouth entry returnPort outside : Nat}
    {state : Tongues} {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hforeign : ∀ passage ∈ candy, passageSwitch passage ≠ mouth / 3)
    (hlink : w.link mouth = some outside)
    (current : Tongues) (hcurrent : PassagesGrooved current candy)
    {d : Nat} (hd : d ≤ candy.length + 2) :
    ∃ port phase, stepN w d (mouth, current) = some (port, phase) ∧
      (phase = current ∨ phase = flipAt current (mouth / 3)) := by
  obtain ⟨route, last, hlen, hr, hg, hc, _⟩ := explicit_lobe_route_at
    hentryBranch hentrySwitch hgrooved htrace hcrossed hforeign current hcurrent
  by_cases hroute : d ≤ route.length
  · obtain ⟨port, hp⟩ := hr.grooved_prefix_tongues current hg hroute
    exact ⟨port, current, hp, Or.inl rfl⟩
  · have hd' : d = route.length + 1 := by omega
    refine ⟨outside, flipAt current (mouth / 3), ?_, Or.inr rfl⟩
    simp [hd', stepN_add, hr.sound, stepN, step, hc, hlink]

/-- Prepending a constant-tongue trace preserves a two-phase cover. -/
theorem PhysicalTrace.prepend_two_phase
    {w : Wiring} {s p q L : Nat} {u v : Tongues} {lead : List Passage}
    (hprefix : PhysicalTrace w (s, u) lead (p, u))
    (hgrooved : PassagesGrooved u lead)
    (hend : stepN w L (p, u) = some (q, v))
    (hphases : ∀ d, d ≤ L → ∃ port phase,
      stepN w d (p, u) = some (port, phase) ∧
        (phase = u ∨ phase = v)) :
    stepN w (lead.length + L) (s, u) = some (q, v) ∧
      ∀ d, d ≤ lead.length + L → ∃ port phase,
        stepN w d (s, u) = some (port, phase) ∧
          (phase = u ∨ phase = v) := by
  constructor
  · rw [stepN_add, hprefix.sound]
    exact hend
  · apply stepN_cover_append hprefix.sound ?_ hphases
    intro d hd
    obtain ⟨port, hr⟩ := hprefix.grooved_prefix_tongues u hgrooved hd
    exact ⟨port, u, hr, Or.inl rfl⟩

/-- Only the first encounter with the disturbed switch matters. Before it a
fault follows the reference route unchanged. A stem entry invokes capture;
a branch entry restores the reference configuration and synchronizes every
later step. The reference route may repeat switches after this first contact. -/
theorem ManufacturedFlipReflector.grooved_route_fault
    {w : Wiring} {g e : Nat} (A : ManufacturedFlipReflector w g e)
    (state : Tongues) (hA : PathGrooves A.toSupported.paths state)
    {route : List Passage} {finish : Nat × Tongues}
    (htrace : PhysicalTrace w (e, state) route finish)
    (hgrooved : PassagesGrooved state route)
    (hcontact : ∃ passage ∈ route, passageSwitch passage = A.actionSwitch) :
    (∃ travel, stepN w travel (e, flipAt state A.actionSwitch) = some (e, state) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) = some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state)) ∨
    (∃ cutoff, cutoff ≤ route.length ∧
      (∀ d, d < cutoff → ∃ port,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, flipAt state A.actionSwitch)) ∧
      (∀ d, cutoff ≤ d → stepN w d (e, flipAt state A.actionSwitch) =
        stepN w d (e, state))) := by
  obtain ⟨before, ⟨p, x⟩, after, hsplit, hforeign, hswitch⟩ :=
    exists_first_satisfying_split
      (fun passage => passageSwitch passage = A.actionSwitch) route hcontact
  obtain ⟨_, _, hprefix, _⟩ :=
    (hsplit ▸ htrace).split_grooved_at (hsplit ▸ hgrooved)
  have hbefore : PassagesGrooved state before := by
    intro passage hp
    exact hgrooved passage (by rw [hsplit]; exact List.mem_append_left _ hp)
  have hprefixFlip := hprefix.flip_unvisited hforeign
  have hbeforeFlip := grooved_after_flip_other hbefore hforeign
  change p / 3 = A.actionSwitch at hswitch
  by_cases hstem : p % 3 = 0
  · have hmouth : p = A.mouth := by
      have hm := A.mouth_is_stem
      unfold ManufacturedFlipReflector.actionSwitch at hswitch
      omega
    rw [hmouth] at hprefixFlip
    have hcapture := A.capture_from_mouth state
      (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
    exact Or.inl ⟨before.length + (A.candy.length + 2 + A.runway.length),
      hprefixFlip.prepend_two_phase hbeforeFlip hcapture
        (fun _ hd => A.capture_from_mouth_two_phase state
          (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2 hd)⟩
  · have hforward : arrive state p = (x, state) :=
      groove_forward (hgrooved (p, x) (by rw [hsplit]; simp))
    have hrepair : arrive (flipAt state A.actionSwitch) p = (x, state) := by
      rw [← hswitch]
      exact flipped_passage_forward_trailing hforward hstem
    have hmerge : stepN w (before.length + 1) (e, flipAt state A.actionSwitch) =
        stepN w (before.length + 1) (e, state) := by
      rw [stepN_add w before.length 1, stepN_add w before.length 1,
        hprefixFlip.sound, hprefix.sound]
      simp [stepN, step, hrepair, hforward]
    refine Or.inr ⟨before.length + 1, ?_, ?_, ?_⟩
    · rw [hsplit, List.length_append, List.length_cons]; omega
    · intro d hd
      exact hprefixFlip.grooved_prefix_tongues _ hbeforeFlip (by omega)
    · intro d hd
      have heq : d = (before.length + 1) + (d - (before.length + 1)) := by omega
      rw [heq, stepN_add w (before.length + 1),
        stepN_add w (before.length + 1), hmerge]

section
variable {w : Wiring} {outside mouth entry returnPort : Nat}
  (C : ManufacturedFlipReflector w outside mouth)
  (state : Tongues)
  (hCpaths : PathGrooves C.toSupported.paths state)
include w outside mouth entry returnPort C state hCpaths


section
variable (hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
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
include hNewAvoidsC candy hentryBranch hentrySwitch hgrooved htrace hcrossed hCandyForeign hLobe
  hmouthLink

/-- Every suffix/lobe pair preserves one four-corner boundary invariant.
The selected route handles avoidance, capture, and repair in either orientation. -/
theorem manufactured_flip_arbitrary_lobe_all_time_four_phase (d : Nat) :
    ∃ port phase, stepN w d (outside, flipAt state (mouth / 3)) = some (port, phase) ∧
      phase ∈ [flipAt state (mouth / 3),
        flipAt (flipAt state (mouth / 3)) C.actionSwitch,
        state, flipAt state C.actionSwitch] := by
  let a := C.toSupported.action
  let b := LocalAction.flip (mouth / 3)
  let safe := fun u => u ∈ a.corners b state
  have hsafeA u hu := (a.corners_closed b state u hu).1
  have hsafeB u hu := (a.corners_closed b state u hu).2
  let boundary := fun c : Nat × Tongues => c.1 = outside ∧ safe c.2 ∧
    PathGrooves C.toSupported.paths c.2 ∧ PassagesGrooved c.2 candy
  have hLcover : ∀ u, PassagesGrooved u candy → safe u → ∀ d, d ≤ candy.length + 2 →
      ∃ port phase, stepN w d (mouth, u) = some (port, phase) ∧ safe phase := by
    intro u hLu hu d hd
    obtain ⟨port, phase, hr, hp⟩ := explicit_lobe_two_phase_at
      hentryBranch hentrySwitch hgrooved htrace hcrossed hCandyForeign hmouthLink u hLu hd
    exact ⟨port, phase, hr,
      hp.elim (fun h => h.symm ▸ hu) (fun h => h.symm ▸ hsafeB u hu)⟩
  have hprogress : ∀ start, boundary start → ∃ travel finish,
      0 < travel ∧ stepN w travel start = some finish ∧ boundary finish ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d start = some (port, phase) ∧ safe phase := by
    intro ⟨p, u⟩ ⟨hp, hu, hCu, hLu⟩
    dsimp only at hp hu hCu hLu
    subst p
    have hv := hsafeA u hu
    have hnew : boundary (outside, b.apply u) :=
      ⟨rfl, hsafeB u hu, hCu.after_avoiding_action hNewAvoidsC,
        grooved_after_flip_other hLu hCandyForeign⟩
    have hnormal := (hLobe u hLu).1
    have hafter : ∃ travel finish,
        stepN w travel (mouth, a.apply u) = some finish ∧ boundary finish ∧
        ∀ d, d ≤ travel → ∃ port phase,
          stepN w d (mouth, a.apply u) = some (port, phase) ∧ safe phase := by
      obtain ⟨route, last, hlen, hr, hg, _, hsupport⟩ := explicit_lobe_route_at
        hentryBranch hentrySwitch hgrooved htrace hcrossed hCandyForeign u hLu
      by_cases hcontact : ∃ passage ∈ route, passageSwitch passage = C.actionSwitch
      · rcases C.grooved_route_fault u hCu hr hg hcontact
            with ⟨travel, hreach, hcover⟩ | ⟨cutoff, hbound, hpre, hmerge⟩
        · change stepN w travel (mouth, a.apply u) = some (mouth, u) at hreach
          refine ⟨travel + (candy.length + 2), (outside, b.apply u), ?_, hnew, ?_⟩
          · rw [stepN_add, hreach]; exact hnormal
          · apply stepN_cover_append hreach ?_ (hLcover u hLu hu)
            intro d hd
            obtain ⟨port, phase, hr, hp⟩ := hcover d hd
            exact ⟨port, phase, hr,
              hp.elim (fun h => h.symm ▸ hv) (fun h => h.symm ▸ hu)⟩
        · refine ⟨candy.length + 2, (outside, b.apply u),
            (hmerge _ (by omega)).trans hnormal, hnew, ?_⟩
          intro d hd
          by_cases hearly : d < cutoff
          · obtain ⟨port, hr⟩ := hpre d hearly
            exact ⟨port, _, hr, hv⟩
          · obtain ⟨port, phase, hr, hp⟩ := hLcover u hLu hu d hd
            exact ⟨port, phase, (hmerge d (by omega)).trans hr, hp⟩
      · have hLv : PassagesGrooved (a.apply u) candy := by
          apply grooved_after_flip_other hLu
          intro old hold heq
          obtain ⟨passage, hp, hs⟩ := hsupport old hold
          exact hcontact ⟨passage, hp, hs.trans heq⟩
        have hrun := hLobe (a.apply u) hLv
        exact ⟨candy.length + 2, (outside, b.apply (a.apply u)), hrun.1,
          ⟨rfl, hsafeB _ hv, (C.toSupported.run u hCu).2.after_avoiding_action hNewAvoidsC,
            hrun.2⟩, hLcover _ hLv hv⟩
    obtain ⟨travel, finish, hr, hfinish, hcover⟩ := hafter
    have hCrun := (C.toSupported.run u hCu).1
    refine ⟨C.toSupported.travel + travel, finish,
      Nat.add_pos_left (ManufacturedReflector.flip C).travel_pos _, ?_, hfinish, ?_⟩
    · rw [stepN_add, hCrun]; exact hr
    · apply stepN_cover_append hCrun ?_ hcover
      intro d hd
      obtain ⟨port, phase, hr, hp⟩ :=
        (ManufacturedReflector.flip C).travel_two_phase_stepN u hCu hd
      exact ⟨port, phase, hr,
        hp.elim (fun h => h.symm ▸ hu) (fun h => h.symm ▸ hv)⟩
  have hCandy : PassagesGrooved state candy :=
    fun passage hp => hgrooved passage (List.mem_cons_of_mem _ hp)
  obtain ⟨port, phase, hr, hp⟩ := stepN_covered_of_progress boundary safe hprogress
    (start := (outside, b.apply state))
    ⟨rfl, by simp [safe, LocalAction.corners], hCpaths.after_avoiding_action hNewAvoidsC,
      grooved_after_flip_other hCandy hCandyForeign⟩ d
  exact ⟨port, phase, hr, by
    simpa [safe, LocalAction.corners, a, b, ManufacturedFlipReflector.toSupported, LocalAction.apply,
      or_comm, or_left_comm, or_assoc] using hp⟩

end

end

end GeneralN
