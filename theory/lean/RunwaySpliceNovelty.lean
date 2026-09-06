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

/-- A recorded lobe with a mouth-free interior is two-phase in every grooved
state, not only in the tongue assignment used to record it. Pin the mouth to
its recorded entry arm; the given state is that assignment or its one-bit flip.
The two orientations then supply the same abstract traversal contract. -/
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
  have hhead := hgrooved (mouth, entry) List.mem_cons_self
  have hselected : state (entry / 3) = bval entry := by
    have hpin : pin state entry = state := by
      simpa only [arrive, if_neg hentryBranch] using congrArg Prod.snd hhead
    have heq := congrFun hpin (entry / 3)
    simpa [pin] using heq.symm
  have hreturnSwitch : returnPort / 3 = mouth / 3 := by
    have h := arrive_exit_switch state returnPort
    rw [hcrossed] at h
    exact h.symm
  obtain ⟨hreturnBranch, hmouth, hpin⟩ := changed_arrival_is_trailing hcrossed
    (by simp [hreturnSwitch, flipAt])
  have hreturnValue : bval returnPort = !(state (mouth / 3)) := by
    have heq := congrFun hpin (mouth / 3)
    simpa [pin, flipAt, hreturnSwitch] using heq.symm
  let base := pin current entry
  have hbaseSelected : base (mouth / 3) = state (mouth / 3) := by
    rw [← hentrySwitch, hselected]
    simp [base, pin]
  have hbaseGrooved : PassagesGrooved base ((mouth, entry) :: candy) := by
    intro passage hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact groove_transfer hhead (by simpa [hentrySwitch] using hbaseSelected)
    · exact grooved_after_pin_other hcurrent
        (fun passage hp => by simpa [hentrySwitch] using hforeign passage hp) passage hp
  have hbaseTrace := htrace.replay_grooved base hbaseGrooved
  have hbaseCrossed : arrive base returnPort =
      (mouth, flipAt base (mouth / 3)) := by
    have hp := pin_eq_flipAt (u := base) hreturnSwitch
      (by rw [hbaseSelected]; exact hreturnValue)
    simpa [arrive, hreturnBranch, ← hmouth] using congrArg (Prod.mk mouth) hp
  by_cases haligned : current (entry / 3) = bval entry
  · have heq : base = current := pin_of_agrees haligned
    simpa only [heq] using explicit_lobe_travel_two_phase
      hbaseGrooved hbaseTrace hbaseCrossed hlink hd
  · have heq : base = flipAt current (mouth / 3) := by
      apply pin_eq_flipAt hentrySwitch
      have hne : current (mouth / 3) ≠ bval entry := by simpa [hentrySwitch] using haligned
      cases hc : current (mouth / 3) <;> cases he : bval entry <;> simp [hc, he] at hne ⊢
    simpa only [heq, flipAt_flipAt] using explicit_lobe_reverse_travel_two_phase
      hentryBranch hentrySwitch hbaseGrooved hbaseTrace hbaseCrossed hforeign hlink hd

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
  have hraw := htrace
  rw [hsplit] at hraw
  obtain ⟨middle, hleft, hright⟩ := hraw.split_append
  have hmiddle : middle.1 = p := hright.head_arrive.1
  have hbefore : PassagesGrooved state before := by
    intro passage hp
    exact hgrooved passage (by rw [hsplit]; exact List.mem_append_left _ hp)
  have hprefix : PhysicalTrace w (e, state) before (p, state) := by
    simpa only [hmiddle] using hleft.replay_grooved state hbefore
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

/-- Pointwise strengthening of the arbitrary-lobe theta half.  The old
manufactured reflector first exposes `state` and its own action state.  The
first old-action contact on the new lobe then either captures through the old
mouth or repairs trailing-first; in both cases every remaining intermediate
vector is `state` or the new lobe state.  Thus the complete half has exactly
the three advertised possible phases. -/
theorem manufactured_flip_arbitrary_lobe_theta_half_three_phase
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
      stepN w travel (outside, state) =
        some (outside, flipAt state (mouth / 3)) ∧
      ∀ d, d ≤ travel →
        ∃ port phase,
          stepN w d (outside, state) = some (port, phase) ∧
          phase ∈
            [state, flipAt state C.actionSwitch,
              flipAt state (mouth / 3)] := by
  let safe := fun phase => phase ∈
    [state, flipAt state C.actionSwitch, flipAt state (mouth / 3)]
  have hexplicit : ∀ d, d ≤ candy.length + 2 → ∃ port phase,
      stepN w d (mouth, state) = some (port, phase) ∧ safe phase := by
    intro d hd
    obtain ⟨port, phase, hr, hs⟩ := explicit_lobe_travel_two_phase
      hgrooved htrace hcrossed hmouthLink hd
    refine ⟨port, phase, hr, ?_⟩
    rcases hs with rfl | rfl <;> simp [safe]
  have hfault : ∃ travel, stepN w travel (mouth, flipAt state C.actionSwitch) =
      some (outside, flipAt state (mouth / 3)) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (mouth, flipAt state C.actionSwitch) = some (port, phase) ∧ safe phase := by
    have hrouteContact : ∃ passage ∈ (mouth, entry) :: candy,
        passageSwitch passage = C.actionSwitch := by
      obtain ⟨passage, hp, hs⟩ := hcontact
      exact ⟨passage, List.mem_cons_of_mem _ hp, hs⟩
    rcases C.grooved_route_fault state hCpaths htrace hgrooved hrouteContact with
      hcapture | hrepair
    · obtain ⟨travel, hr, hs⟩ := hcapture
      refine ⟨travel + (candy.length + 2), ?_, ?_⟩
      · rw [stepN_add, hr]; exact hnormal
      · apply stepN_cover_append hr ?_ hexplicit
        intro d hd
        obtain ⟨port, phase, hr, hp⟩ := hs d hd
        refine ⟨port, phase, hr, ?_⟩
        rcases hp with rfl | rfl <;> simp [safe]
    · obtain ⟨cutoff, hbound, hpre, hmerge⟩ := hrepair
      have hle : cutoff ≤ candy.length + 2 := by simpa using Nat.le_trans hbound (by simp)
      refine ⟨candy.length + 2, (hmerge _ hle).trans hnormal, ?_⟩
      intro d hd
      by_cases hearly : d < cutoff
      · obtain ⟨port, hr⟩ := hpre d hearly
        exact ⟨port, _, hr, by simp [safe]⟩
      · obtain ⟨port, phase, hr, hs⟩ := hexplicit d hd
        exact ⟨port, phase, (hmerge d (by omega)).trans hr, hs⟩
  obtain ⟨travel, hrun, hcover⟩ := hfault
  have hCrun := (C.toSupported.run state hCpaths).1
  refine ⟨C.toSupported.travel + travel,
    Nat.add_pos_left (ManufacturedReflector.flip C).travel_pos _, ?_, ?_⟩
  · rw [stepN_add, hCrun]; exact hrun
  · apply stepN_cover_append hCrun ?_ hcover
    intro d hd
    obtain ⟨port, phase, hr, hs⟩ := (ManufacturedReflector.flip C).travel_two_phase_stepN
      state hCpaths hd
    refine ⟨port, phase, hr, ?_⟩
    rcases hs with rfl | rfl <;> simp [safe, ManufacturedReflector.toSupported,
      ManufacturedFlipReflector.toSupported, LocalAction.apply]

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
  (hcontact : ∃ passage ∈ candy,
    passageSwitch passage = C.actionSwitch)
include hNewAvoidsC candy hentryBranch hentrySwitch hgrooved htrace hcrossed hCandyForeign hLobe
  hmouthLink hcontact

/-- Intersecting actions alternate covered positive excursions between the
base and lobe-flipped boundary states. First-contact capture or repair supplies
each excursion; no period or four-leg time window is needed. -/
theorem manufactured_flip_arbitrary_lobe_all_time_four_phase (d : Nat) :
    ∃ port phase, stepN w d (outside, flipAt state (mouth / 3)) = some (port, phase) ∧
      phase ∈ [flipAt state (mouth / 3),
        flipAt (flipAt state (mouth / 3)) C.actionSwitch,
        state, flipAt state C.actionSwitch] := by
  let newState := flipAt state (mouth / 3)
  let oldState := flipAt state C.actionSwitch
  let oldNewState := flipAt newState C.actionSwitch
  have hCandy : PassagesGrooved state candy := by
    intro passage hpassage
    exact hgrooved passage (List.mem_cons_of_mem _ hpassage)
  have hnormal := (hLobe state hCandy).1
  obtain ⟨forwardTravel, hforwardPositive,
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
  obtain ⟨reverseTravel, hreversePositive,
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
  let safe := fun phase => phase ∈ [newState, oldNewState, state, oldState]
  have hprogress : ∀ start,
      start = (outside, state) ∨ start = (outside, newState) →
      ∃ travel finish, 0 < travel ∧ stepN w travel start = some finish ∧
        (finish = (outside, state) ∨ finish = (outside, newState)) ∧
        ∀ t, t ≤ travel → ∃ port phase,
          stepN w t start = some (port, phase) ∧ safe phase := by
    intro start hs
    rcases hs with rfl | rfl
    · refine ⟨forwardTravel, (outside, newState), hforwardPositive,
        hforward, Or.inr rfl, ?_⟩
      intro t ht
      obtain ⟨port, phase, hr, hs⟩ := hforwardPointwise t ht
      refine ⟨port, phase, hr, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl <;> simp [safe, oldState, newState]
    · refine ⟨reverseTravel, (outside, state), hreversePositive,
        hreverse', Or.inl rfl, ?_⟩
      intro t ht
      obtain ⟨port, phase, hr, hs⟩ := hreversePointwise t ht
      refine ⟨port, phase, hr, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl <;> simp [safe, oldNewState, newState, flipAt_flipAt]
  exact stepN_covered_of_progress _ safe hprogress (Or.inr rfl) d

end

end

/-- The manufactured suffix and arbitrary lobe share one two-phase contract.
Their actions preserve the four-corner orbit and each other's grooves, so the
abstract pair invariant gives the all-time bound without a four-leg period. -/
theorem manufactured_suffix_explicit_lobe_all_time_four_phase
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
    ∃ port phase, stepN w d (outside, flipAt state (mouth / 3)) = some (port, phase) ∧
    phase ∈
      [flipAt state (mouth / 3),
       flipAt (flipAt state (mouth / 3)) C.actionSwitch,
       flipAt state C.actionSwitch,
       state] := by
  let L : SupportedReflector w mouth outside := {
    travel := candy.length + 2
    paths := [candy]
    action := .flip (mouth / 3)
    run := by simpa [IsReflector, PathGrooves, LocalAction.apply] using hLobe
  }
  have hOldAvoidsL : C.toSupported.action.Avoids L.paths := by
    intro path hp passage hm
    have heq : path = candy := by simpa [L] using hp
    subst path
    exact hCandyForeignOld passage hm
  have hCNew := hCpaths.after_avoiding_action hNewAvoidsC
  have hCandy : PassagesGrooved state candy :=
    fun passage hp => hgrooved passage (List.mem_cons_of_mem _ hp)
  have hLNew : PathGrooves L.paths (flipAt state (mouth / 3)) := by
    simpa [L, PathGrooves] using grooved_after_flip_other hCandy hCandyForeignNew
  have htwo : ∀ u, PathGrooves L.paths u → ∀ t, t ≤ L.travel →
      ∃ port phase, stepN w t (mouth, u) = some (port, phase) ∧
        (phase = u ∨ phase = L.action.apply u) := by
    intro u hu t ht
    exact explicit_lobe_two_phase_at hentryBranch hentrySwitch hgrooved htrace
      hcrossed hCandyForeignNew hmouthLink u (hu candy (by simp [L])) ht
  have hcover := C.toSupported.pair_all_time_four_phase L
    (ManufacturedReflector.flip C).travel_pos (by dsimp [L]; omega)
    (fun u hu _ ht => (ManufacturedReflector.flip C).travel_two_phase_stepN u hu ht)
    htwo (flipAt state (mouth / 3)) hCNew hLNew hOldAvoidsL hNewAvoidsC d
  simpa [L, ManufacturedFlipReflector.toSupported, LocalAction.apply,
    flipAt_comm hActionsNe, flipAt_flipAt] using hcover

end GeneralN
