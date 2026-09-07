import PreReturnProtectedRoute
import ReservedHistoryCharge
import KnownEdgeNAddFourChangedClosed

/-!
# The protected-pair `N+4` bound

The two manufacturing journeys share one coordinate budget and one canonical
history. A stay reflector costs at most `N+2` historical vectors. For a flip
reflector, either its action coordinate is reserved, again giving `N+2`, or
its occurrence in the second construction recovers a historical Gray corner.
The repair tail therefore costs at most two new vectors in the first case
and one in the second: `(N+2)+2 = (N+3)+1 = N+4`.

There is no split on whether the action writer is the first productive event,
no doubly-erased history, and no unresolved writer-order residual.
-/

namespace GeneralN

/-- Every support-preserving protected repair prefix ends in either the
protected reflector's activated state or its pre-return state.  For a flip
reflector these are the two values of its action tongue; for a stay
reflector the core groove rules out even that one-coordinate difference. -/
theorem ManufacturedReflector.repair_prefix_contact_eq_activated_or_preReturn
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {approach : List Passage} {finishPort : Nat} {contact : Tongues}
    (hprefix : PhysicalTrace w (g, B.activatedState) approach
      (finishPort, contact))
    (hsimple : SwitchSimple approach)
    (hroute : ∀ passage ∈ approach,
      passage ∈ A.orientedRoute B.activatedState)
    (hBcontact : PathGrooves B.toSupported.paths contact) :
    contact = B.activatedState ∨ contact = B.preReturn.2 := by
  have hchanges := A.repair_prefix_changes_only_protected_return
    B hA hBstart hprefix hsimple hroute hBcontact
  cases B with
  | stay R =>
      left
      have hkey := grooved_states_agree_on_passage
        (passagesGrooved_singleton.mp (pathGrooves_pair.mp hBstart).2)
        (passagesGrooved_singleton.mp (pathGrooves_pair.mp hBcontact).2)
      funext j
      by_cases hj : contact j = R.returnState j
      · exact hj
      · have hs := hchanges j hj
        change j = R.arm / 3 at hs
        exact hs ▸ hkey.symm
  | flip R =>
      change contact = R.afterReturn ∨ contact = R.returnState
      have hrelation := tongues_eq_or_eq_flipAt_of_changes_only
        (u := R.afterReturn) (v := contact) (k := R.actionSwitch)
        (fun j hj => (hchanges j hj).trans R.secondArm_switch)
      have hpre := (ManufacturedReflector.flip R).preReturn_eq_action_activated
      change R.returnState = flipAt R.afterReturn R.actionSwitch at hpre
      rcases hrelation with heq | heq
      · exact Or.inl heq.symm
      · right; rw [hpre, heq, flipAt_flipAt]

/-- A historical two-phase prefix followed by an all-time two-phase tail
has at most one fresh vector.  The shared boundary phase is charged only once. -/
theorem two_phase_prefix_then_two_phase_tail_one_novelty
    {w : Wiring} {N lead : Nat}
    {start endpoint : Nat × Tongues} {u v z : Tongues}
    (hreach : stepN w lead start = some endpoint)
    (hphase : ∀ d, d ≤ lead → ∃ port phase,
      stepN w d start = some (port, phase) ∧ (phase = u ∨ phase = v))
    (hendpoint : endpoint.2 = v)
    (history : List (List Bool))
    (hu : VectorCount.restrict N u ∈ history)
    (hv : VectorCount.restrict N v ∈ history)
    (htail : ∀ d, ∃ port phase,
      stepN w d endpoint = some (port, phase) ∧ (phase = v ∨ phase = z))
    (times : List Nat) :
    NoveltyCoverOn w N start times history 1 := by
  refine ⟨[VectorCount.restrict N z], by simp, ?_⟩
  apply cover_of_live_phase_orbit hreach (phases := [v, z])
  · intro d
    obtain ⟨port, phase, hr, hp⟩ := htail d
    exact ⟨port, phase, hr, by simpa using hp⟩
  · intro phase hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact List.mem_append_left _ hv
    · exact List.mem_append_right _ (by simp)
  · intro j _ hj
    obtain ⟨port, phase, hr, hp⟩ := hphase j (by omega)
    rw [show restrictedTonguesAt w N start j = VectorCount.restrict N phase by
      simp [restrictedTonguesAt, tonguesAt, hr]]
    rcases hp with rfl | rfl
    · exact hu
    · exact hv
/-- A direct three-state tail with two distinct historical states actually
costs at most one new vector.  The witnesses need not occur in the sampled
list: if two different nonhistorical samples existed, adjoining the two
historical witness times would contradict the three-state cap. -/
private theorem direct_three_tail_one_novelty_of_two_historical_witnesses
    {w : Wiring} {N d₁ d₂ p₁ p₂ : Nat}
    {start : Nat × Tongues} {u₁ u₂ : Tongues}
    (history : List (List Bool))
    (hrun₁ : stepN w d₁ start = some (p₁, u₁))
    (hrun₂ : stepN w d₂ start = some (p₂, u₂))
    (hhist₁ : VectorCount.restrict N u₁ ∈ history)
    (hhist₂ : VectorCount.restrict N u₂ ∈ history)
    (hne : VectorCount.restrict N u₁ ≠
      VectorCount.restrict N u₂)
    (hthree : ∀ samples : List Nat,
      (∀ k ∈ samples, (stepN w k start).isSome) →
      (samples.map (restrictedTonguesAt w N start)).Nodup →
      samples.length ≤ 3)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome) :
    NoveltyCoverOn w N start times history 1 := by
  let f := restrictedTonguesAt w N start
  have hf₁ : f d₁ = VectorCount.restrict N u₁ := by
    simp [f, restrictedTonguesAt, tonguesAt, hrun₁]
  have hf₂ : f d₂ = VectorCount.restrict N u₂ := by
    simp [f, restrictedTonguesAt, tonguesAt, hrun₂]
  by_cases hnew : ∃ k ∈ times, f k ∉ history
  · obtain ⟨k₀, hk₀, hnew₀⟩ := hnew
    refine ⟨[f k₀], by simp, ?_⟩
    intro k hk
    by_cases hh : f k ∈ history
    · exact List.mem_append_left _ hh
    · have heq : f k = f k₀ := by
        apply Classical.byContradiction
        intro hne₀
        have hnd : ([d₁, d₂, k₀, k].map f).Nodup := by
          simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
            List.not_mem_nil, List.nodup_nil]
          grind
        have hbound := hthree [d₁, d₂, k₀, k] (by
          intro j hj
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl | rfl
          · simp [hrun₁]
          · simp [hrun₂]
          · exact hlive _ hk₀
          · exact hlive _ hk) hnd
        simp at hbound
      exact List.mem_append_right _ (by simpa only [List.mem_singleton] using heq)
  · exact ⟨[], by simp, by simpa [f] using hnew⟩

/-- Flipping a represented switch changes the restricted tongue vector. -/
private theorem restrict_flipAt_ne_of_lt
    {N C : Nat} {u : Tongues} (hC : C < N) :
    VectorCount.restrict N (flipAt u C) ≠
      VectorCount.restrict N u := by
  intro heq
  have hbit := restrict_eq_apply heq hC
  simp [flipAt] at hbit

private theorem ManufacturedReflector.return_change_facing_one_novelty
    {w : Wiring} {N g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {contact : Tongues} {approach suffix : List Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState) approach
      (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hp : p % 3 = 0)
    (hswitch : p / 3 = B.preReturn.1 / 3)
    (hreturnChange : B.activatedState (p / 3) ≠
      B.preReturn.2 (p / 3))
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history)
    (times : List Nat)
    (hlive : ∀ d ∈ times,
      (stepN w d (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
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
      have hrouteSimple :=
        A.orientedRoute_simple (ManufacturedReflector.flip R).activatedState
      have happroachSimple : SwitchSimple approach := by
        unfold SwitchSimple at hrouteSimple ⊢
        rw [hrouteSplit] at hrouteSimple
        simp only [List.map_append, List.map_cons] at hrouteSimple
        exact (List.nodup_append.mp hrouteSimple).1
      have hrouteMembership : ∀ passage ∈ approach,
          passage ∈ A.orientedRoute
            (ManufacturedReflector.flip R).activatedState := by
        intro passage hpassage
        rw [hrouteSplit]
        exact List.mem_append_left _ hpassage
      have hphase := A.repair_prefix_two_phase (.flip R) hA hBstart
        happroach happroachSimple hrouteMembership hpaths
      have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
        (.flip R) hA hBstart happroach happroachSimple
          hrouteMembership hpaths
      have hcontactHistorical : VectorCount.restrict N contact ∈ history := by
        rcases hrelation with rfl | rfl
        · exact hinitialHistorical
        · exact hpreHistorical
      have happroachGrooved : PassagesGrooved contact approach :=
        happroach.grooved_of_switchSimple happroachSimple
      have happroachContact : PhysicalTrace w
          (g, contact) approach (R.mouth, contact) :=
        happroach.replay_grooved contact happroachGrooved
      have hall := R.facing_mouth_tail_two_phase
        happroachContact happroachGrooved hpaths
      exact two_phase_prefix_then_two_phase_tail_one_novelty
        happroach.sound hphase rfl history hinitialHistorical hcontactHistorical
        hall times


/-- A backward state-changing protected contact costs one fresh vector over
the activated/pre-return history; otherwise the exact forward merge is
retained. -/
private theorem ManufacturedReflector.protected_changed_contact_one_or_forward
    {w : Wiring} {N g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {u v : Tongues} {approach suffix : List Passage}
    {path : List Passage} {old : Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState) approach (p, u))
    (hpaths : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3))
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      NoveltyCoverOn w N (g, B.activatedState) times history 1) ∨
      ∃ oriented, oriented ∈ B.orientedRoute u ∧
        arrive u oriented.2 = (oriented.1, u) ∧
        passageSwitch oriented = p / 3 ∧ x = oriented.2 := by
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hdirection⟩ :=
    B.changed_contact_on_orientedRoute u v hpaths
      hpath hold hswitch harrive
  rcases hdirection with hbackward | hforward
  · obtain ⟨recorded, tail, hBsplit⟩ := List.append_of_mem horiented
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
    have hrouteSimple := A.orientedRoute_simple B.activatedState
    rw [hrouteSplit] at hrouteSimple
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple
      exact (List.nodup_append.mp hrouteSimple).1
    have happroachForeign : ∀ passage ∈ approach,
        passageSwitch passage ≠ p / 3 := by
      unfold SwitchSimple at hrouteSimple
      simp only [List.map_append, List.map_cons] at hrouteSimple
      have hparts := List.nodup_append.mp hrouteSimple
      intro passage hp hEq
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (p / 3) (by simp [passageSwitch])
      exact hne hEq
    have happroachV : PhysicalTrace w
        (g, flipAt B.activatedState (p / 3)) approach (p, v) := by
      rw [hflip]
      exact happroach.flip_unvisited happroachForeign
    have happroachGroovedV : PassagesGrooved v approach :=
      happroachV.grooved_of_switchSimple happroachSimple
    have happroachGroovedU : PassagesGrooved u approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachReplayU : PhysicalTrace w (g, u) approach (p, u) :=
      happroach.replay_grooved u happroachGroovedU
    have happroachRoute : ∀ passage ∈ approach,
        passage ∈ A.orientedRoute B.activatedState := by
      intro passage hp
      rw [hrouteSplit]
      exact List.mem_append_left _ hp
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
      B hA hBstart happroach happroachSimple happroachRoute hpaths
    have huHistorical : VectorCount.restrict N u ∈ history := by
      rcases hrelation with rfl | rfl
      · exact hinitialHistorical
      · exact hpreHistorical
    have hall := backward_contact_all_time_two_phase
      hrecorded hrecordedGroovedV B.entryEdge
      (by simpa [hbackward] using harrive) happroachReplayU happroachGroovedV
    left
    intro times _ _
    exact two_phase_prefix_then_two_phase_tail_one_novelty
      happroach.sound hphase rfl history hinitialHistorical huHistorical hall times
  · exact Or.inr ⟨oriented, horiented, horientedGroove, horientedSwitch, hforward⟩

/-- A backward no-change protected contact costs one fresh vector over the
activated/pre-return history; otherwise the exact facing-forward merge is
retained. -/
private theorem ManufacturedReflector.protected_facing_contact_one_or_forward
    {w : Wiring} {N g e p marker fresh : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {contact : Tongues} {approach suffix path : List Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, marker) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState) approach
      (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hpath : path ∈ B.toSupported.paths)
    (hold : (fresh, p) ∈ path)
    (harrive : arrive contact p = (fresh, contact))
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      NoveltyCoverOn w N (g, B.activatedState) times history 1) ∨
      (p, fresh) ∈ B.orientedRoute contact := by
  obtain ⟨oriented, horiented, horientation⟩ :=
    B.support_passage_on_orientedRoute contact hpath hold
  rcases horientation with hsame | hreverse
  · have horientedEq : oriented = (fresh, p) := hsame
    subst oriented
    obtain ⟨recorded, tail, hBsplit⟩ := List.append_of_mem horiented
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
    have hrouteSimple := A.orientedRoute_simple B.activatedState
    rw [hrouteSplit] at hrouteSimple
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple
      exact (List.nodup_append.mp hrouteSimple).1
    have happroachGrooved : PassagesGrooved contact approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachReplay :
        PhysicalTrace w (g, contact) approach (p, contact) :=
      happroach.replay_grooved contact happroachGrooved
    have happroachRoute : ∀ passage ∈ approach,
        passage ∈ A.orientedRoute B.activatedState := by
      intro passage hp
      rw [hrouteSplit]
      exact List.mem_append_left _ hp
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
      B hA hBstart happroach happroachSimple happroachRoute hpaths
    have hcontactHistorical : VectorCount.restrict N contact ∈ history := by
      rcases hrelation with rfl | rfl
      · exact hinitialHistorical
      · exact hpreHistorical
    have hall := backward_contact_all_time_two_phase
      hrecorded hrecordedGrooved B.entryEdge harrive
      happroachReplay happroachGrooved
    left
    intro times _ _
    exact two_phase_prefix_then_two_phase_tail_one_novelty
      happroach.sound hphase rfl history hinitialHistorical hcontactHistorical hall times
  · right
    simpa [hreverse] using horiented

/-- Protected-repair classification with every early exit already charged
by one vector over a history containing the activated and pre-return states.
Public: the productive-boundary closure consumes it from a separate file. -/
theorem manufactured_pair_protected_repair_novelty_outcomes
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      NoveltyCoverOn w N (g, B.activatedState) times history 1) ∨
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
      intro times hlive hnd
      exact A.return_change_facing_one_novelty B hA hB
        hsplit hprefix hBcontact hp hreturn.1 hreturn.2
        history hinitialHistorical hpreHistorical times hlive hnd
    · obtain ⟨fresh, path,
          hpath, hold, hotherFresh⟩ := hexploration
      have harriveFresh : arrive contact p = (fresh, contact) := by
        simpa [hotherFresh] using harrive
      rcases A.protected_facing_contact_one_or_forward B hA hB
          hsplit hprefix hBcontact hpath hold harriveFresh history
          hinitialHistorical hpreHistorical with hcount | hforward
      · exact Or.inl hcount
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
      rcases A.protected_changed_contact_one_or_forward B hA hB
          hsplit hprefix hBu harrive hpath hold hswitch hchange
          history hinitialHistorical hpreHistorical with hcount | hforward
      · exact Or.inl hcount
      · obtain ⟨oriented, horiented, horientedGroove, horientedSwitch, hforwardExit⟩ := hforward
        exact Or.inr (Or.inr (Or.inl
          ⟨approach, p, x, suffix, u, v, path, old,
            oriented, hsplit, hprefix, hBu, harrive,
            hpath, hold, hswitch, hchange, horiented,
            horientedGroove, horientedSwitch, hforwardExit⟩))
    · exact Or.inr (Or.inr (Or.inr hcomplete))

/-- A facing-forward merge has at most one fresh vector over the activated
and pre-return history.  Its eventual two-phase tail consists exactly of
those two protected states; the direct three-state theorem supplies the
finite-sample formulation. -/
theorem ManufacturedReflector.FacingForwardMerge.one_novelty_of_preReturn
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    (hmerge : A.FacingForwardMerge B)
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome) :
    NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
  obtain ⟨R, before, p, x, after, contact, fresh,
      hBeq, hrouteSplit, hprefix, hpaths,
      hcandyMem, hsecond⟩ := hmerge.flip_candy
  subst B
  obtain ⟨candyBefore, candyAfter, hcandySplit⟩ :=
    List.append_of_mem hcandyMem
  obtain ⟨hbeforeSimple, hbeforeRoute⟩ := A.orientedRoute_prefix_simple_and_mem
    (ManufacturedReflector.flip R).activatedState hrouteSplit
  have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
    (.flip R) hA hBstart hprefix hbeforeSimple hbeforeRoute hpaths
  have hpreAction :
      (ManufacturedReflector.flip R).preReturn.2 =
        flipAt (ManufacturedReflector.flip R).activatedState
          R.actionSwitch := by
    simpa [ManufacturedReflector.toSupported,
      ManufacturedFlipReflector.toSupported, LocalAction.apply] using
        (ManufacturedReflector.flip R).preReturn_eq_action_activated
  have hpreInitNe :
      VectorCount.restrict N (ManufacturedReflector.flip R).preReturn.2 ≠
        VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState := by
    rw [hpreAction]
    exact restrict_flipAt_ne_of_lt (R.action_lt hN)
  have hinitPreNe :
      VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState ≠
        VectorCount.restrict N (ManufacturedReflector.flip R).preReturn.2 :=
    Ne.symm hpreInitNe
  have hrunZero : stepN w 0
      (g, (ManufacturedReflector.flip R).activatedState) =
        some (g, (ManufacturedReflector.flip R).activatedState) := by
    rfl
  have hthree : ∀ samples : List Nat,
      (∀ k ∈ samples,
        (stepN w k
          (g, (ManufacturedReflector.flip R).activatedState)).isSome) →
      (samples.map (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState))).Nodup →
      samples.length ≤ 3 := by
    intro samples hsLive hsNodup
    exact hmerge.distinct_le_three hA hBstart samples hsLive hsNodup
  rcases hrelation with hcontactInitial | hcontactPre
  · obtain ⟨tailTravel, _htailPositive, _htailLe, htailContact,
        _htailAlternate, _htailContactPhase, _htailAlternatePhase⟩ :=
      R.reverse_candy_suffix_absorbs_twoPhases contact hpaths hsecond
        hcandySplit
    let loopSteps := before.length + tailTravel
    have hrunAlternate : stepN w loopSteps
        (g, (ManufacturedReflector.flip R).activatedState) =
          some (g, flipAt contact R.actionSwitch) := by
      dsimp [loopSteps]
      rw [stepN_add, hprefix.sound]
      exact htailContact
    have hAlternatePre : flipAt contact R.actionSwitch =
        (ManufacturedReflector.flip R).preReturn.2 := by
      rw [hcontactInitial]
      exact hpreAction.symm
    apply direct_three_tail_one_novelty_of_two_historical_witnesses
      history hrunZero hrunAlternate hinitialHistorical
        (by simpa [hAlternatePre] using hpreHistorical)
        (by simpa [hAlternatePre] using hinitPreNe)
        hthree times hlive
  · apply direct_three_tail_one_novelty_of_two_historical_witnesses
      history hrunZero hprefix.sound hinitialHistorical
        (by simpa [hcontactPre] using hpreHistorical)
        (by simpa [hcontactPre] using hinitPreNe)
        hthree times hlive

private theorem ManufacturedReflector.trailing_orientedRoute_grooved
    {w : Wiring} {g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (selector state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state)
    (hmem : (p, x) ∈ A.orientedRoute selector)
    (hpBranch : p % 3 ≠ 0) :
    arrive state p = (x, state) := by
  cases A with
  | stay R =>
      change PathGrooves [R.runway, [(R.mouth, R.arm)]] state at hpaths
      change (p, x) ∈ R.runway ++ [(R.mouth, R.arm)] at hmem
      rcases List.mem_append.mp hmem with hrunway | hcore
      · exact groove_forward
          (hpaths R.runway (by simp) (p, x) hrunway)
      · simp only [List.mem_singleton] at hcore
        rcases Prod.mk.inj hcore with ⟨rfl, rfl⟩
        exact groove_forward
          (hpaths [(R.mouth, R.arm)] (by simp)
            (R.mouth, R.arm) (by simp))
  | flip R =>
      change PathGrooves [R.runway, R.candy] state at hpaths
      by_cases hselected : selector R.actionSwitch = bval R.firstArm
      · simp only [ManufacturedReflector.orientedRoute, hselected,
          if_pos] at hmem
        rcases List.mem_append.mp hmem with hrunway | hrest
        · exact groove_forward
            (hpaths R.runway (by simp) (p, x) hrunway)
        · rcases List.mem_cons.mp hrest with hmouth | hcandy
          · have hpMouth : p = R.mouth := congrArg Prod.fst hmouth
            exact (hpBranch (by rw [hpMouth]; exact R.mouth_is_stem)).elim
          · exact groove_forward
              (hpaths R.candy (by simp) (p, x) hcandy)
      · simp only [ManufacturedReflector.orientedRoute, hselected,
          if_false] at hmem
        rcases List.mem_append.mp hmem with hrunway | hrest
        · exact groove_forward
            (hpaths R.runway (by simp) (p, x) hrunway)
        · rcases List.mem_cons.mp hrest with hmouth | hcandy
          · have hpMouth : p = R.mouth := congrArg Prod.fst hmouth
            exact (hpBranch (by rw [hpMouth]; exact R.mouth_is_stem)).elim
          · have hreverse : PassagesGrooved state
                (reversePassages R.candy) :=
              reversePassages_grooved (hpaths R.candy (by simp))
            exact groove_forward (hreverse (p, x) hcandy)

/-- Under the fully protected pre-return hypothesis a changed forward merge
is impossible.  The changed route passage is a reusable passage of `A`, so
`hpre` grooves it in `B.preReturn`.  The same switch is also represented in
`B`'s support.  That support is grooved both at the contact state and at
`B.preReturn`, forcing the two tongue values to agree, while the changed
trailing arrival forces them to be opposite. -/
theorem ManufacturedReflector.ChangedForwardMerge.impossible_of_preReturn_grooved
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (hmerge : A.ChangedForwardMerge B) : False := by
  obtain ⟨approach, p, x, suffix, u, v, path, old,
      oriented, hsplit, _hprefix, hBu, harrive, hpath, hold, hswitch, hchanged,
      _horiented, _horientedGroove, _horientedSwitch, _hforward⟩ := hmerge
  have hmem : (p, x) ∈ A.orientedRoute B.activatedState := by
    rw [hsplit]
    exact List.mem_append_right approach List.mem_cons_self
  obtain ⟨hpBranch, _hxStem, hvPin⟩ :=
    changed_arrival_is_trailing harrive hchanged
  have hprePassage : arrive B.preReturn.2 p =
      (x, B.preReturn.2) :=
    A.trailing_orientedRoute_grooved B.activatedState
      B.preReturn.2 hpre hmem hpBranch
  have hBpre : PathGrooves B.toSupported.paths B.preReturn.2 := by
    rw [B.preReturn_eq_action_activated]
    exact hBstart.after_avoiding_action B.action_avoids_own_support
  have hupre := pathGrooves_agree_at_support_passage
    hBu hBpre hpath hold
  have hupre' : u (p / 3) = B.preReturn.2 (p / 3) := by
    rw [hswitch] at hupre
    exact hupre
  have hprePin : pin B.preReturn.2 p = B.preReturn.2 := by
    unfold arrive at hprePassage
    rw [if_neg hpBranch] at hprePassage
    exact (Prod.mk.inj hprePassage).2
  have hvValue : v (p / 3) = bval p := by
    rw [hvPin]
    simp [pin]
  have hpreValue : B.preReturn.2 (p / 3) = bval p := by
    have h := congrFun hprePin (p / 3)
    simp only [pin, if_pos] at h
    exact h.symm
  apply hchanged
  calc
    v (p / 3) = bval p := hvValue
    _ = B.preReturn.2 (p / 3) := hpreValue.symm
    _ = u (p / 3) := hupre'.symm

section
variable {w : Wiring} {N g e : Nat}
include w N g e

/-- The historical corner recovered from the last action writer belongs
already to the second reflector's uncompressed construction history.  This
form lets boundary arguments use their own smaller two-journey history
instead of the canonical `preservedTwoHistoryCore`. -/
theorem ManufacturedFlipReflector.flipped_preReturn_mem_second_sharp_of_last
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch)
    (hlast : forall j, t < j -> j < B.exploration.length ->
      Not (RawProductiveAt w N (e, B.baseState) j)) :
    VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch) ∈
      B.sharpConstructionHistory N := by
  have htData := mem_rawFirstWriterTimes_iff.mp ht
  have hprod : RawProductiveAt w N (e, B.baseState) t := htData.2.1
  let span := B.exploration.length - (t + 1)
  have hsum : t + 1 + span = B.exploration.length := by
    dsimp [span]
    omega
  have hendQuiet :
      restrictedTonguesAt w N (e, B.baseState) B.exploration.length =
        restrictedTonguesAt w N (e, B.baseState) (t + 1) := by
    have h := restrictedTonguesAt_eq_of_quiet_interval
      (first := t + 1) (span := span)
      (by simpa [hsum] using B.exploration_trace.sound)
      (fun j hj hbound => hlast j (by omega) (by
        rw [hsum] at hbound
        exact hbound))
    simpa [hsum] using h
  have hend :
      restrictedTonguesAt w N (e, B.baseState) B.exploration.length =
        VectorCount.restrict N B.preReturn.2 := by
    simp [restrictedTonguesAt, tonguesAt, B.exploration_trace.sound]
  have hpost := rawProductiveAt_restricted_flip hprod
  rw [hwriter] at hpost
  have hflipEnd := restrict_flipAt_congr (C := R.actionSwitch)
    (hend.symm.trans hendQuiet)
  have hflipPost := restrict_flipAt_congr (C := R.actionSwitch) hpost
  have hrecover :
      VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch) =
        restrictedTonguesAt w N (e, B.baseState) t := by
    calc
      VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch) =
          VectorCount.restrict N
            (flipAt (tonguesAt w (e, B.baseState) (t + 1))
              R.actionSwitch) := hflipEnd
      _ = VectorCount.restrict N
          (flipAt
            (flipAt (tonguesAt w (e, B.baseState) t)
              R.actionSwitch)
            R.actionSwitch) := hflipPost
      _ = restrictedTonguesAt w N (e, B.baseState) t := by
        simp [restrictedTonguesAt, flipAt_flipAt]
  rw [hrecover]
  unfold ManufacturedReflector.sharpConstructionHistory
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨t, List.mem_range.mpr (by omega), rfl⟩

/-- A completed protected repair needs only one fresh vector whenever the
`A`-action applied to `B`'s pre-return vector is historical.  Depending on
which of the two repair phases is final, this historical vector is one of
the two nominally fresh Gray-square corners. -/
theorem ManufacturedReflector.completed_protected_route_one_novelty_of_action_preReturn
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    {finalState : Tongues}
    (hrepair : PhysicalTrace w (g, B.activatedState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState))
    (hAfinal : PathGrooves A.toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState)
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history)
    (haPreHistorical : VectorCount.restrict N
      (A.toSupported.action.apply B.preReturn.2) ∈ history)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome) :
    NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
  have hrelation := A.completed_repair_initial_action_relation
    B hA hB hrepair hBfinal
  have hpreAction :
      B.preReturn.2 = B.toSupported.action.apply B.activatedState :=
    B.preReturn_eq_action_activated
  have hAorBAHistorical :
      VectorCount.restrict N
          (A.toSupported.action.apply finalState) ∈ history ∨
        VectorCount.restrict N
          (B.toSupported.action.apply
            (A.toSupported.action.apply finalState)) ∈ history := by
    rcases hrelation with heq | haction
    · right
      have hpreB : B.preReturn.2 =
          B.toSupported.action.apply finalState := by
        rw [hpreAction, heq]
      have hcorner :
          B.toSupported.action.apply
              (A.toSupported.action.apply finalState) =
            A.toSupported.action.apply B.preReturn.2 := by
        calc
          B.toSupported.action.apply
              (A.toSupported.action.apply finalState) =
              A.toSupported.action.apply
                (B.toSupported.action.apply finalState) :=
            (A.toSupported.action.commute B.toSupported.action
              finalState).symm
          _ = A.toSupported.action.apply B.preReturn.2 := by rw [hpreB]
      simpa [hcorner] using haPreHistorical
    · left
      have hpreFinal : B.preReturn.2 = finalState := by
        calc
          B.preReturn.2 =
              B.toSupported.action.apply B.activatedState := hpreAction
          _ = finalState := by
            rw [haction, B.toSupported.action.involutive]
      simpa [hpreFinal] using haPreHistorical
  rcases hAorBAHistorical with hAHistorical | hBAHistorical
  · exact ⟨[VectorCount.restrict N (B.toSupported.action.apply
      (A.toSupported.action.apply finalState))], by simp,
      A.completed_protected_route_cover B hA hB hrepair hAfinal hBfinal history _
        hinitialHistorical hpreHistorical (List.mem_append_left _ hAHistorical)
        (by simp) times hlive⟩
  · exact ⟨[VectorCount.restrict N (A.toSupported.action.apply finalState)],
      by simp,
      A.completed_protected_route_cover B hA hB hrepair hAfinal hBfinal history _
        hinitialHistorical hpreHistorical (by simp)
        (List.mem_append_left _ hBAHistorical) times hlive⟩

section
variable (A : ManufacturedReflector w g e)
  (B : ManufacturedReflector w e g)
  (hbase : B.baseState = A.activatedState)
  (hApaths : PathGrooves A.toSupported.paths A.activatedState)
  (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
  (history : List (List Bool))
  (hhistory : ∀ x,
    x ∈ A.sharpConstructionHistory N ∨
      x ∈ B.sharpConstructionHistory N → x ∈ history)
  (budget : Nat)
  (htail : ∀ tailTimes : List Nat,
    (∀ k ∈ tailTimes,
      (stepN w k (g, B.activatedState)).isSome) →
    (tailTimes.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
    NoveltyCoverOn w N (g, B.activatedState) tailTimes
      history budget)
  (times : List Nat)
  (hlive : ∀ k ∈ times,
    (stepN w k (g, A.baseState)).isSome)
  (hnd : (times.map
    (restrictedTonguesAt w N (g, A.baseState))).Nodup)
include A B hbase hApaths hBpaths history hhistory budget htail times hlive hnd

/-- Lift a novelty cover for the protected repair tail across the two
manufacturing journeys.  Every prefix vector is supplied by the shared
history; only the shifted tail spends the given novelty budget. -/
theorem ManufacturedReflector.two_journeys_then_shared_history_novelty_cover :
    NoveltyCoverOn w N (g, A.baseState) times history budget := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let secondTravel := B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let localTimes :=
    (times.filter (fun k => decide (totalTravel < k))).map
      (fun k => k - totalTravel)
  have hreachA : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hApaths
  have hreachB : stepN w secondTravel (e, A.activatedState) =
      some (g, B.activatedState) := by
    have h := B.manufacturing_journey_reaches_activated hBpaths
    simpa [secondTravel, hbase] using h
  have hreachTotal : stepN w totalTravel (g, A.baseState) =
      some (g, B.activatedState) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachB
  have hprefixCover : ∀ d, d ≤ totalTravel →
      restrictedTonguesAt w N (g, A.baseState) d ∈ history := by
    intro d hd
    by_cases hfirst : d ≤ firstTravel
    · apply hhistory
      left
      exact A.manufacturing_journey_mem_sharpHistory
        hApaths (by simpa [firstTravel] using hfirst)
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLe : q ≤ secondTravel := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hm := B.manufacturing_journey_mem_sharpHistory
        (N := N) hBpaths (j := q)
          (by simpa [secondTravel] using hqLe)
      rw [hdEq, restrictedTonguesAt_add_of_reaches hreachA
        (stepN_prefix_some hqLe hreachB)]
      exact hhistory _ (Or.inr (by simpa [hbase] using hm))
  have hlocalLive : ∀ d ∈ localTimes,
      (stepN w d (g, B.activatedState)).isSome := by
    intro d hd
    obtain ⟨k, hkFiltered, rfl⟩ := List.mem_map.mp hd
    have hk := (List.mem_filter.mp hkFiltered).1
    have hkGt : totalTravel < k := by
      simpa using (List.mem_filter.mp hkFiltered).2
    have hkEq : k = totalTravel + (k - totalTravel) := by omega
    have hkLive := hlive k hk
    rw [hkEq, stepN_add, hreachTotal] at hkLive
    exact hkLive
  have hlocalVector : localTimes.map
      (restrictedTonguesAt w N (g, B.activatedState)) =
      (times.filter (fun k => decide (totalTravel < k))).map
        (restrictedTonguesAt w N (g, A.baseState)) := by
    dsimp [localTimes]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkGt : totalTravel < k := by
      simpa using (List.mem_filter.mp hk).2
    have hkEq : k = totalTravel + (k - totalTravel) := by omega
    have hkLive :
        (stepN w (totalTravel + (k - totalTravel)) (g, A.baseState)).isSome := by
      rw [← hkEq]
      exact hlive k hkTimes
    have heq := restrictedTonguesAt_add_of_reaches (N := N) hreachTotal
      (stepN_suffix_some_of_reaches hreachTotal hkLive)
    rw [← hkEq] at heq
    exact heq.symm
  have hfilteredNodup :
      ((times.filter (fun k => decide (totalTravel < k))).map
        (restrictedTonguesAt w N (g, A.baseState))).Nodup :=
    tailsharp_nodup_map_filter _ hnd
  have hlocalNodup :
      (localTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup := by
    rw [hlocalVector]
    exact hfilteredNodup
  obtain ⟨fresh, hfresh, hlocalMem⟩ :=
    htail localTimes hlocalLive hlocalNodup
  refine ⟨fresh, hfresh, ?_⟩
  intro k hk
  by_cases hprefix : k ≤ totalTravel
  · exact List.mem_append_left _ (hprefixCover k hprefix)
  · have hkGt : totalTravel < k := by omega
    let d := k - totalTravel
    have hkEq : k = totalTravel + d := by
      dsimp [d]
      omega
    have hkFiltered : k ∈
        times.filter (fun t => decide (totalTravel < t)) := by
      apply List.mem_filter.mpr
      exact ⟨hk, by simp [hkGt]⟩
    have hdMem : d ∈ localTimes := by
      dsimp [localTimes]
      exact List.mem_map.mpr ⟨k, hkFiltered, rfl⟩
    rw [hkEq, restrictedTonguesAt_add_of_reaches hreachTotal
      (Option.isSome_iff_exists.mp (hlocalLive d hdMem))]
    exact hlocalMem d hdMem

/-- Generic two-journey bookkeeping over an arbitrary shared history: the
counting form of the novelty cover above. -/
theorem ManufacturedReflector.two_journeys_then_shared_history_novelty_count :
    times.length ≤ history.length + budget :=
  noveltyCoverOn_distinct_count
    (A.two_journeys_then_shared_history_novelty_cover B hbase hApaths
      hBpaths history hhistory budget htail times hlive hnd) hnd

end

theorem ManufacturedStayReflector.protectedHistory_length_le_N_add_two
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedStayReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = (ManufacturedReflector.stay R).activatedState)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.preReturn.2) :
    ((ManufacturedReflector.stay R).preservedTwoHistoryCore B N).length ≤
      N + 2 := by
  let A : ManufacturedReflector w g e := .stay R
  have hboundary : VectorCount.restrict N A.activatedState ∈
      B.writerConstructionHistory N := by
    dsimp [A]
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge := A.reusable_add_second_first_writers_le
    hN B hbaseGrooves hpreGrooves
  have heq : A.exploration.length = A.reusableSwitches.length := by
    simp [A, ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches]
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length, B.writerConstructionHistory_length]
  omega

/-- Every continuation of a fully protected opposite-reflector pair has at
most two fresh vectors over any history which represents both construction
journeys.  Unlike the top-level counting theorem, this statement keeps the
history abstract so a productive-boundary proof can substitute a smaller
history containing its pre-passage vector. -/
theorem ManufacturedReflector.protected_repair_two_novelty_over_history
    (hN : forall p q, w.link p = some q -> p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (history : List (List Bool))
    (hhistory : forall x,
      x ∈ A.sharpConstructionHistory N \/
        x ∈ B.sharpConstructionHistory N -> x ∈ history)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    NoveltyCoverOn w N (g, B.activatedState) times history 2 := by
  have hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history :=
    hhistory _ (Or.inr B.activated_mem_sharpHistory)
  have hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history :=
    hhistory _ (Or.inr B.preReturn_mem_sharpHistory)
  rcases manufactured_pair_protected_repair_novelty_outcomes
      A B hA hB history hinitialHistorical hpreHistorical with
    hone | hfacing | hchanged | hcomplete
  · obtain ⟨fresh, hfresh, hmem⟩ := hone times hlive hnd
    exact ⟨fresh, by omega, hmem⟩
  · obtain ⟨fresh, hfresh, hmem⟩ :=
      hfacing.one_novelty_of_preReturn hN hA hB history
        hinitialHistorical hpreHistorical times hlive
    exact ⟨fresh, by omega, hmem⟩
  · exact (hchanged.impossible_of_preReturn_grooved hB hpre).elim
  · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
    exact ⟨[VectorCount.restrict N (A.toSupported.action.apply finalState),
      VectorCount.restrict N (B.toSupported.action.apply
        (A.toSupported.action.apply finalState))], by simp,
      A.completed_protected_route_cover B hA hB hrepair hAfinal hBfinal history _
        hinitialHistorical hpreHistorical (by simp) (by simp) times hlive⟩

/-- If the first flip reflector's action switch is a productive first writer
of the second construction, every protected repair continuation has only one
fresh vector over any history representing both construction journeys. -/
theorem ManufacturedFlipReflector.protected_repair_one_novelty_over_history_of_action_writer
    (hN : forall p q, w.link p = some q -> p < 3 * N /\ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (history : List (List Bool))
    (hhistory : forall x,
      x ∈ (ManufacturedReflector.flip R).sharpConstructionHistory N \/
        x ∈ B.sharpConstructionHistory N -> x ∈ history)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
  have hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history :=
    hhistory _ (Or.inr B.activated_mem_sharpHistory)
  have hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history :=
    hhistory _ (Or.inr B.preReturn_mem_sharpHistory)
  rcases manufactured_pair_protected_repair_novelty_outcomes
      (ManufacturedReflector.flip R) B hA hB history
        hinitialHistorical hpreHistorical with
    hone | hfacing | hchanged | hcomplete
  · exact hone times hlive hnd
  · exact hfacing.one_novelty_of_preReturn
      hN hA hB history hinitialHistorical hpreHistorical times hlive
  · exact (hchanged.impossible_of_preReturn_grooved hB hpre).elim
  · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
    have hlast := R.no_productive_after_action_writer
      B.exploration_trace B.exploration_simple hA hpre ht hwriter
    have haPreSharp := R.flipped_preReturn_mem_second_sharp_of_last B ht hwriter hlast
    have haPreHistorical : VectorCount.restrict N
        ((ManufacturedReflector.flip R).toSupported.action.apply
          B.preReturn.2) ∈ history := by
      apply hhistory
      right
      simpa [ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported, LocalAction.apply] using
          haPreSharp
    exact (ManufacturedReflector.flip R).completed_protected_route_one_novelty_of_action_preReturn
      B hA hB hrepair hAfinal hBfinal history
        hinitialHistorical hpreHistorical haPreHistorical times hlive


/-- The protected pair needs only a coordinate-usage split, not a writer-order
split. If the old flip action is absent from the second writer list, reserve
that coordinate and pay `(N+2)+2`. If present, its last-write history recovers
one tail corner and we pay `(N+3)+1`. A stay reflector always uses `(N+2)+2`.
The same canonical history is used in every case; no second erasure is needed. -/
theorem ManufacturedReflector.preReturn_grooved_protected_pair_all_run_distinct_le_N_add_four
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 4 := by
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  let history := A.preservedTwoHistoryCore B N
  have hhistory : ∀ x, x ∈ A.sharpConstructionHistory N ∨
      x ∈ B.sharpConstructionHistory N → x ∈ history := by
    intro x hx
    show x ∈ A.preservedTwoHistoryCore B N
    grind [ManufacturedReflector.mem_sharpHistoryCore_of_mem,
      ManufacturedReflector.mem_writerConstructionHistory_of_mem_sharp,
      ManufacturedReflector.preservedTwoHistoryCore,
      ManufacturedReflector.sharpConstructionHistory]
  have htwo : history.length ≤ N + 2 → times.length ≤ N + 4 := by
    intro hlen
    have hcount := A.two_journeys_then_shared_history_novelty_count
      B hbase hApaths hBpaths history hhistory 2
      (A.protected_repair_two_novelty_over_history hN B hAatBase
        hBpaths hpre history hhistory) times hlive hnd
    omega
  cases A with
  | stay R =>
      exact htwo (R.protectedHistory_length_le_N_add_two
        hN B hbase hAatBase hpre)
  | flip R =>
      by_cases haction : R.actionSwitch ∈ B.constructionFirstWriterSwitches N
      · have hlen := (ManufacturedReflector.flip R).preservedTwoHistoryCore_length_le_N_add_three
          hN B hbase hAatBase hpre
        obtain ⟨t, ht, hwriter⟩ := List.mem_map.mp haction
        have hcount := (ManufacturedReflector.flip R).two_journeys_then_shared_history_novelty_count
          B hbase hApaths hBpaths history hhistory 1
          (R.protected_repair_one_novelty_over_history_of_action_writer
            hN B hAatBase hBpaths hpre history hhistory ht hwriter)
          times hlive hnd
        change history.length ≤ N + 3 at hlen
        omega
      · exact htwo ((ManufacturedReflector.flip R).preservedTwoHistoryCore_length_le_N_add_two_of_reserved
          hN B hbase hAatBase hpre (R.action_lt hN)
          R.action_not_mem_reusable haction)

end

/-- **Unconditional known-edge protected-pair law, exact raw `N+4`.**
Broken pre-return support is the already-closed changed-contact branch;
fully protected support is the theorem above. -/
theorem knownEdgeProtectedPairNAddFourLaw :
    KnownEdgeProtectedPairNAddFourLaw := by
  intro w N e hN start D times hlive hnd
  by_cases hpre : PathGrooves D.A.toSupported.paths D.B.preReturn.2
  · have hliveA : ∀ k ∈ times,
        (stepN w k (start.1, D.A.baseState)).isSome := by
      simpa [D.A_base] using hlive
    have hndA : (times.map
        (restrictedTonguesAt w N (start.1, D.A.baseState))).Nodup := by
      simpa [D.A_base] using hnd
    exact D.A.preReturn_grooved_protected_pair_all_run_distinct_le_N_add_four
      hN D.B D.B_base D.A_grooves D.B_grooves hpre times hliveA hndA
  · have htrace : PhysicalTrace w (e, D.A.activatedState)
        D.B.exploration D.B.preReturn := by
      simpa [D.B_base] using D.B.exploration_trace
    obtain ⟨S⟩ :=
      PartialSecondRunSharp.ManufacturedReflector.changedContact_of_broken_simple
        D.A
      D.A_grooves htrace D.B.exploration_simple hpre
    have hliveA : ∀ k ∈ times,
        (stepN w k (start.1, D.A.baseState)).isSome := by
      simpa [D.A_base] using hlive
    have hndA : (times.map
        (restrictedTonguesAt w N
          (start.1, D.A.baseState))).Nodup := by
      simpa [D.A_base] using hnd
    exact S.all_run_distinct_le_N_add_four
      hN D.A_grooves times hliveA hndA

end GeneralN
