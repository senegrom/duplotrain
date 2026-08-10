import TrackQuantitativeRouteSharp

/-!
# Sharp quantitative bounds for the early protected-repair exits

The old `12*N` estimates charged a grooved retrace/replay cycle by the
coarse `2*N` total-reflector travel on each side.  The actual prefixes are
switch-simple physical traces, hence each contains at most `N` passages.
This lowers backward contacts to `5*N+2` and the final-mouth alternating
capture to `6*N+3`.
-/

namespace GeneralN

/-- A backward protected contact with switch-simple old and new prefixes has
lead plus period at most `5*N+2`. -/
theorem backward_contact_within_five_succ_two
    {w : Wiring} {N g e p oldEntry : Nat}
    {oldBase oldEnd base u v : Tongues}
    {recorded approach : List Passage}
    (hrecordedLe : recorded.length ≤ N)
    (happroachLe : approach.length ≤ N)
    (hrecorded :
      PhysicalTrace w (g, oldBase) recorded (oldEntry, oldEnd))
    (hrecordedGrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (happroach : PhysicalTrace w (e, base) approach (p, u))
    (happroachGrooved : PassagesGrooved v approach) :
    EventuallyPeriodicWithin w (e, base) (5 * N + 2) := by
  have hback := physicalTrace_contact_retraces_prefix
    hrecorded hrecordedGrooved hentry hcontact
  have hforward := happroach.replay_grooved v happroachGrooved
  let cycle := (p, oldEntry) ::
    reversePassages recorded ++ approach
  have hcycle : PhysicalTrace w (p, u) cycle (p, v) := by
    dsimp [cycle]
    simpa [List.append_assoc] using hback.append hforward
  have hheadGrooved : arrive v oldEntry = (p, v) := by
    have hbackLocal := arrive_back u p
    rwa [hcontact] at hbackLocal
  have hallGrooved : PassagesGrooved v cycle := by
    intro passage hp
    dsimp [cycle] at hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadGrooved
    · rcases List.mem_append.mp htail with hold | hnew
      · exact reversePassages_grooved hrecordedGrooved passage hold
      · exact happroachGrooved passage hnew
  have hperiod : stepN w cycle.length (p, v) = some (p, v) := by
    dsimp [cycle]
    exact run_grooved_passages w v p oldEntry p
      (reversePassages recorded ++ approach)
      hcycle.linked hallGrooved hcycle.last_link
  have hlead : stepN w (approach.length + cycle.length)
      (e, base) = some (p, v) := by
    rw [stepN_add, happroach.sound]
    exact hcycle.sound
  have hcycleLen : cycle.length =
      1 + recorded.length + approach.length := by
    dsimp [cycle]
    simp [reversePassages_length]
    omega
  have hpositive : 0 < cycle.length := by
    rw [hcycleLen]
    omega
  exact ⟨approach.length + cycle.length, cycle.length, (p, v),
    hpositive, by rw [hcycleLen]; omega, hlead, hperiod⟩

/-- Sharp state-changing protected-support classification.  The backward
orientation has a `5*N+2` lasso; the forward orientation is retained for the
splice analysis. -/
theorem ManufacturedReflector.protected_changed_contact_within_five_succ_two_or_forward
    {w : Wiring} {N g e p x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedReflector w e g)
    {startState u v : Tongues}
    {route approach suffix : List Passage}
    {path : List Passage} {old : Passage}
    (hrouteSplit : route = approach ++ (p, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, u))
    (hpaths : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    EventuallyPeriodicWithin w (g, startState) (5 * N + 2) ∨
      ∃ oriented repaired,
        oriented ∈ B.orientedRoute u ∧
        arrive u oriented.2 = (oriented.1, u) ∧
        passageSwitch oriented = p / 3 ∧
        x = oriented.2 ∧
        arrive v oriented.1 = (oriented.2, repaired) ∧
        arrive repaired oriented.2 = (oriented.1, repaired) := by
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hdirection⟩ :=
    B.changed_contact_on_orientedRoute u v hpaths
      hpath hold hswitch harrive hchanged
  rcases hdirection with hbackward | hforward
  · obtain ⟨recorded, tail, hBsplit⟩ :=
      List.append_of_mem horiented
    have hBroute := B.orientedRoute_trace u hpaths
    have hBsimple := B.orientedRoute_simple u
    have hBgrooved := hBroute.grooved_of_switchSimple hBsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hBroute hBsplit hBgrooved hBsimple
    have hrecorded := hprefixData.1
    have hrecordedForeign : ∀ passage ∈ recorded,
        passageSwitch passage ≠ p / 3 := by
      intro passage hp hEq
      apply hprefixData.2 passage hp
      exact hEq.trans horientedSwitch.symm
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hBsimple ⊢
      rw [hBsplit] at hBsimple
      simp only [List.map_append, List.map_cons] at hBsimple
      exact (List.nodup_append.mp hBsimple).1
    have hflip : v = flipAt u (p / 3) :=
      changed_arrival_eq_flipAt harrive hchanged
    have hrecordedV : PhysicalTrace w
        (e, v) recorded (oriented.1, v) := by
      rw [hflip]
      exact hrecorded.flip_unvisited hrecordedForeign
    have hrecordedGroovedV : PassagesGrooved v recorded :=
      hrecordedV.grooved_of_switchSimple hrecordedSimple
    have hrouteSimple' := hrouteSimple
    rw [hrouteSplit] at hrouteSimple'
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple' ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      exact (List.nodup_append.mp hrouteSimple').1
    have happroachForeign : ∀ passage ∈ approach,
        passageSwitch passage ≠ p / 3 := by
      unfold SwitchSimple at hrouteSimple'
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      have hparts := List.nodup_append.mp hrouteSimple'
      intro passage hp hEq
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (p / 3) (by simp [passageSwitch])
      exact hne hEq
    have happroachV : PhysicalTrace w
        (g, flipAt startState (p / 3)) approach (p, v) := by
      rw [hflip]
      exact happroach.flip_unvisited happroachForeign
    have happroachGroovedV : PassagesGrooved v approach :=
      happroachV.grooved_of_switchSimple happroachSimple
    have hrecordedLe : recorded.length ≤ N :=
      hrecorded.switchSimple_length_le_switches hN hrecordedSimple
    have happroachLe : approach.length ≤ N :=
      happroach.switchSimple_length_le_switches hN happroachSimple
    exact Or.inl (backward_contact_within_five_succ_two
      hrecordedLe happroachLe hrecorded hrecordedGroovedV
      B.entryEdge (by simpa [hbackward] using harrive)
      happroach happroachGroovedV)
  · obtain ⟨hforwardExit, repaired, hrepair, hgroove⟩ := hforward
    exact Or.inr ⟨oriented, repaired, horiented,
      horientedGroove, horientedSwitch,
      hforwardExit, hrepair, hgroove⟩

/-- Sharp no-change protected-support classification. -/
theorem ManufacturedReflector.protected_facing_contact_within_five_succ_two_or_forward
    {w : Wiring} {N g e p marker fresh : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedReflector w e g)
    {startState contact : Tongues}
    {route approach suffix path : List Passage}
    (hrouteSplit : route = approach ++ (p, marker) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hpath : path ∈ B.toSupported.paths)
    (hold : (fresh, p) ∈ path)
    (harrive : arrive contact p = (fresh, contact)) :
    EventuallyPeriodicWithin w (g, startState) (5 * N + 2) ∨
      (p, fresh) ∈ B.orientedRoute contact := by
  obtain ⟨oriented, horiented, horientation⟩ :=
    B.support_passage_on_orientedRoute contact hpath hold
  rcases horientation with hsame | hreverse
  · have horientedEq : oriented = (fresh, p) := hsame
    subst oriented
    obtain ⟨recorded, tail, hBsplit⟩ :=
      List.append_of_mem horiented
    have hBroute := B.orientedRoute_trace contact hpaths
    have hBsimple := B.orientedRoute_simple contact
    have hBgrooved := hBroute.grooved_of_switchSimple hBsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hBroute hBsplit hBgrooved hBsimple
    have hrecorded := hprefixData.1
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hBsimple ⊢
      rw [hBsplit] at hBsimple
      simp only [List.map_append, List.map_cons] at hBsimple
      exact (List.nodup_append.mp hBsimple).1
    have hrecordedGrooved : PassagesGrooved contact recorded :=
      hrecorded.grooved_of_switchSimple hrecordedSimple
    have hrouteSimple' := hrouteSimple
    rw [hrouteSplit] at hrouteSimple'
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple' ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      exact (List.nodup_append.mp hrouteSimple').1
    have happroachGrooved : PassagesGrooved contact approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have hrecordedLe : recorded.length ≤ N :=
      hrecorded.switchSimple_length_le_switches hN hrecordedSimple
    have happroachLe : approach.length ≤ N :=
      happroach.switchSimple_length_le_switches hN happroachSimple
    exact Or.inl (backward_contact_within_five_succ_two
      hrecordedLe happroachLe hrecorded hrecordedGrooved
      B.entryEdge harrive happroach happroachGrooved)
  · right
    simpa [hreverse] using horiented

private theorem ManufacturedFlipReflector.capture_tail_le_succ_early
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (B : ManufacturedFlipReflector w e g) :
    B.candy.length + 2 + B.runway.length ≤ N + 1 := by
  have htrace : PhysicalTrace w (e, B.base)
      (B.runway ++ (B.mouth, B.firstArm) :: B.candy)
      (B.secondArm, B.returnState) :=
    B.runwayTrace.append B.candyTrace
  have hlen := htrace.switchSimple_length_le_switches hN B.simple
  simp only [List.length_append, List.length_cons] at hlen
  omega

/-- Sharp final-mouth capture: the switch-simple approach costs at most `N`
and one old-reflector capture at most `N+1`; the alternating lasso therefore
has total cap `6*N+3`. -/
theorem ManufacturedFlipReflector.facing_mouth_contact_within_six_succ_three
    {w : Wiring} {N g e x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedFlipReflector w e g)
    {startState contact : Tongues}
    {route approach suffix : List Passage}
    (hrouteSplit : route = approach ++ (B.mouth, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach
      (B.mouth, contact))
    (hpaths : PathGrooves [B.runway, B.candy] contact) :
    EventuallyPeriodicWithin w (g, startState) (6 * N + 3) := by
  have hrouteSimple' := hrouteSimple
  rw [hrouteSplit] at hrouteSimple'
  have happroachSimple : SwitchSimple approach := by
    unfold SwitchSimple at hrouteSimple' ⊢
    simp only [List.map_append, List.map_cons] at hrouteSimple'
    exact (List.nodup_append.mp hrouteSimple').1
  have hforeign : ∀ passage ∈ approach,
      passageSwitch passage ≠ B.actionSwitch := by
    unfold SwitchSimple at hrouteSimple'
    simp only [List.map_append, List.map_cons] at hrouteSimple'
    have hparts := List.nodup_append.mp hrouteSimple'
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (B.mouth, x)) (by simp)
    apply hne
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hEq
  have happroachGrooved : PassagesGrooved contact approach :=
    happroach.grooved_of_switchSimple happroachSimple
  have happroachContact : PhysicalTrace w
      (g, contact) approach (B.mouth, contact) :=
    happroach.replay_grooved contact happroachGrooved
  let alternate := flipAt contact B.actionSwitch
  have happroachAlternate : PhysicalTrace w
      (g, alternate) approach (B.mouth, alternate) := by
    dsimp [alternate]
    exact happroachContact.flip_unvisited hforeign
  have hpathsAlternate :
      PathGrooves [B.runway, B.candy] alternate := by
    dsimp [alternate]
    change PathGrooves [B.runway, B.candy]
      ((LocalAction.flip B.actionSwitch).apply contact)
    exact hpaths.after_avoiding_action B.support_foreign
  let cap := B.candy.length + 2 + B.runway.length
  have hcaptureFromAlternate :
      stepN w cap (B.mouth, alternate) = some (g, contact) := by
    dsimp [cap, alternate]
    exact B.capture_from_mouth contact
      (pathGrooves_pair.mp hpaths).1
      (pathGrooves_pair.mp hpaths).2
  have hcaptureFromContact :
      stepN w cap (B.mouth, contact) = some (g, alternate) := by
    have hcapture := B.capture_from_mouth alternate
      (pathGrooves_pair.mp hpathsAlternate).1
      (pathGrooves_pair.mp hpathsAlternate).2
    simpa [cap, alternate, flipAt_flipAt] using hcapture
  let half := approach.length + cap
  have hhalfAlternate :
      stepN w half (g, alternate) = some (g, contact) := by
    dsimp [half]
    rw [stepN_add, happroachAlternate.sound]
    exact hcaptureFromAlternate
  have hhalfContact :
      stepN w half (g, contact) = some (g, alternate) := by
    dsimp [half]
    rw [stepN_add, happroachContact.sound]
    exact hcaptureFromContact
  have hperiod :
      stepN w (half + half) (g, alternate) =
        some (g, alternate) := by
    rw [stepN_add, hhalfAlternate]
    exact hhalfContact
  have hlead : stepN w half (g, startState) =
      some (g, alternate) := by
    dsimp [half]
    rw [stepN_add, happroach.sound]
    exact hcaptureFromContact
  have happroachLe : approach.length ≤ N :=
    happroach.switchSimple_length_le_switches hN happroachSimple
  have hcapLe : cap ≤ N + 1 := by
    dsimp [cap]
    exact B.capture_tail_le_succ_early hN
  have hpositive : 0 < half + half := by
    dsimp [half, cap]
    omega
  exact ⟨half, half + half, (g, alternate), hpositive,
    by dsimp [half]; omega, hlead, hperiod⟩

/-- Orientation-free sharp final-return exception. -/
theorem ManufacturedReflector.return_change_facing_within_six_succ_three
    {w : Wiring} {N g e p x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedReflector w e g)
    {startState contact : Tongues}
    {route approach suffix : List Passage}
    (hrouteSplit : route = approach ++ (p, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hp : p % 3 = 0)
    (hswitch : p / 3 = B.preReturn.1 / 3)
    (hreturnChange : B.activatedState (p / 3) ≠
      B.preReturn.2 (p / 3)) :
    EventuallyPeriodicWithin w (g, startState) (6 * N + 3) := by
  cases B with
  | stay R => exact (hreturnChange rfl).elim
  | flip R =>
      have hsecondSwitch : R.secondArm / 3 = R.mouth / 3 := by
        have hs := arrive_exit_switch R.returnState R.secondArm
        rw [R.crossed] at hs
        exact hs.symm
      have hmouthStem := R.mouth_is_stem
      have hpmouth : p = R.mouth := by
        change p / 3 = R.secondArm / 3 at hswitch
        omega
      subst p
      exact R.facing_mouth_contact_within_six_succ_three hN
        hrouteSplit hrouteSimple happroach hpaths

/-- Protected-repair classification with every early lasso bounded by
`6*N+3`; the two forward merges and complete-repair residual are unchanged.
-/
theorem manufactured_pair_protected_repair_quantitative_outcomes_six_succ_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    EventuallyPeriodicWithin w (g, B.activatedState) (6 * N + 3) ∨
      A.FacingForwardMerge B ∨
      A.ChangedForwardMerge B ∨
      ∃ finalState,
        PhysicalTrace w (g, B.activatedState)
          (A.orientedRoute B.activatedState)
          (A.orientedFinish B.activatedState, finalState) ∧
        PathGrooves A.toSupported.paths finalState ∧
        PathGrooves B.toSupported.paths finalState := by
  rcases A.repair_current_route_preserving_until_conflict
      B.baseState B.activatedState hA hB with hfacing | hrest
  · obtain ⟨before, p, x, after, contact, other,
        hsplit, hprefix, hBcontact, hp, hchange,
        hcontact, harrive, hother⟩ := hfacing
    rcases B.facing_exit_matches_activation_passage
        hchange hcontact hp harrive with hreturn | hexploration
    · left
      exact B.return_change_facing_within_six_succ_three hN
        hsplit (A.orientedRoute_simple B.activatedState)
        hprefix hBcontact hp hreturn.1 hreturn.2
    · obtain ⟨oldApproach, fresh, oldSuffix, oldU, oldV, path,
          _holdSplit, _holdSwitch, _holdTrace, _holdArrive,
          hpath, hold, hotherFresh⟩ := hexploration
      have harriveFresh : arrive contact p = (fresh, contact) := by
        simpa [hotherFresh] using harrive
      rcases B.protected_facing_contact_within_five_succ_two_or_forward
          hN hsplit (A.orientedRoute_simple B.activatedState)
          hprefix hBcontact hpath hold harriveFresh with
        hperiodic | hforward
      · exact Or.inl (hperiodic.weaken (by omega))
      · exact Or.inr (Or.inl ⟨before, p, x, after,
          contact, fresh, path, hsplit, hprefix, hBcontact, hp,
          hchange, by simpa [passageSwitch] using hcontact,
          hpath, hold, harriveFresh,
          by simpa [hotherFresh] using hother,
          hforward⟩)
  · rcases hrest with hchanged | hcomplete
    · obtain ⟨approach, p, x, suffix, u, v, path, old,
          hsplit, hprefix, hBu, harrive,
          hpath, hold, hswitch, hchange⟩ := hchanged
      rcases B.protected_changed_contact_within_five_succ_two_or_forward
          hN hsplit (A.orientedRoute_simple B.activatedState)
          hprefix hBu harrive hpath hold hswitch hchange with
        hperiodic | hforward
      · exact Or.inl (hperiodic.weaken (by omega))
      · obtain ⟨oriented, repaired, horiented, horientedGroove,
            horientedSwitch, hforwardExit, hrepair,
            hgroove⟩ := hforward
        exact Or.inr (Or.inr (Or.inl
          ⟨approach, p, x, suffix, u, v, path, old,
            oriented, repaired, hsplit, hprefix, hBu, harrive,
            hpath, hold, hswitch, hchange, horiented,
            horientedGroove, horientedSwitch, hforwardExit,
            hrepair, hgroove⟩))
    · exact Or.inr (Or.inr (Or.inr hcomplete))

end GeneralN
