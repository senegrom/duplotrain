import FacingForwardNovelty
import PreReturnProtectedRoute
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
      obtain ⟨happroachSimple, hrouteMembership⟩ :=
        A.orientedRoute_prefix_simple_and_mem _ hrouteSplit
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
    have hrouteSimple := A.orientedRoute_simple B.activatedState
    rw [hrouteSplit] at hrouteSimple
    obtain ⟨happroachSimple, happroachRoute⟩ :=
      A.orientedRoute_prefix_simple_and_mem _ hrouteSplit
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
      B hA hBstart happroach happroachSimple happroachRoute hpaths
    have hcontactHistorical : VectorCount.restrict N contact ∈ history := by
      rcases hrelation with rfl | rfl
      · exact hinitialHistorical
      · exact hpreHistorical
    have hall := B.backward_contact_two_phase hpaths horiented happroach
      (by grind [SwitchSimple, passageSwitch]) harrive
    left
    intro times _ _
    exact two_phase_prefix_then_two_phase_tail_one_novelty
      happroach.sound hphase rfl history hinitialHistorical hcontactHistorical hall times
  · right
    simpa [hreverse] using horiented

/-- Trailing passages of any selected route are reusable grooves; the
private mouth passage is facing and therefore cannot occur here. -/
private theorem ManufacturedReflector.trailing_orientedRoute_grooved
    {w : Wiring} {g e p x : Nat}
    (A : ManufacturedReflector w g e) (selector state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state)
    (hmem : (p, x) ∈ A.orientedRoute selector) (hpBranch : p % 3 ≠ 0) :
    arrive state p = (x, state) := by
  cases A with
  | stay R =>
      apply groove_forward
      change PathGrooves [R.runway, [(R.mouth, R.arm)]] state at hpaths
      change (p, x) ∈ R.runway ++ [(R.mouth, R.arm)] at hmem
      rcases List.mem_append.mp hmem with hm | hm
      · exact hpaths R.runway (by simp) (p, x) hm
      · exact hpaths [(R.mouth, R.arm)] (by simp) (p, x) hm
  | flip R =>
      by_cases hr : (p, x) ∈ R.runway
      · exact groove_forward (hpaths R.runway (by simp [ManufacturedReflector.toSupported,
          ManufacturedFlipReflector.toSupported]) (p, x) hr)
      · obtain ⟨old, ho, heq⟩ :=
          R.nonrunway_oriented_branch_entry_is_candy selector hmem hr hpBranch
        have hg := hpaths R.candy (by simp [ManufacturedReflector.toSupported,
          ManufacturedFlipReflector.toSupported]) old ho
        rcases heq with heq | heq <;> cases heq
        · exact groove_forward hg
        · exact hg

/-- A repair cannot change guarded support when both reflector supports are
still grooved at the protected pre-return state. -/
theorem ManufacturedReflector.changed_protected_contact_impossible
    {w : Wiring} {g e p x : Nat} {u v : Tongues} {path : List Passage} {old : Passage}
    (A : ManufacturedReflector w g e) (B : ManufacturedReflector w e g)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (hmem : (p, x) ∈ A.orientedRoute B.activatedState)
    (hBu : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ B.toSupported.paths) (hold : old ∈ path)
    (hswitch : passageSwitch old = p / 3) (hchanged : v (p / 3) ≠ u (p / 3)) : False := by
  have hprePassage := A.trailing_orientedRoute_grooved B.activatedState B.preReturn.2
    hpre hmem (changed_arrival_is_trailing harrive hchanged).1
  have hBpre : PathGrooves B.toSupported.paths B.preReturn.2 := by
    rw [B.preReturn_eq_action_activated]
    exact hBstart.after_avoiding_action B.action_avoids_own_support
  have hupre := pathGrooves_agree_at_support_passage hBu hBpre hpath hold
  rw [hswitch] at hupre
  have hback := arrive_back u p
  rw [harrive] at hback
  exact hchanged ((grooved_states_agree_on_passage
    (groove_forward hback) hprePassage).trans hupre.symm)

/-- Protected-repair classification with every early exit already charged
by one vector over a history containing the activated and pre-return states.
The pre-return grooves exclude state-changing support contacts outright. -/
theorem manufactured_pair_protected_repair_novelty_outcomes
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
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
          contact, fresh, path, hsplit, hprefix, hBcontact,
          hpath, hold, harriveFresh, hforward⟩)
  · rcases hrest with hchanged | hcomplete
    · obtain ⟨approach, p, x, suffix, u, v, path, old,
          hsplit, hprefix, hBu, harrive,
          hpath, hold, hswitch, hchange⟩ := hchanged
      exact (A.changed_protected_contact_impossible B hB hpre
        (by rw [hsplit]; simp) hBu harrive hpath hold hswitch hchange).elim
    · exact Or.inr (Or.inr hcomplete)

/-- Both phases of a facing-forward repair are already historical: the
contact is activated or pre-return, and the alternate is the other state. -/
theorem ManufacturedReflector.FacingForwardMerge.zero_novelty_of_preReturn
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e} {B : ManufacturedReflector w e g}
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    (hmerge : A.FacingForwardMerge B)
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history)
    (times : List Nat) :
    NoveltyCoverOn w N (g, B.activatedState) times history 0 := by
  obtain ⟨R, before, p, x, after, contact, fresh, hB, hsplit, hprefix,
      hpaths, hcandy, hsecond⟩ := hmerge.flip_candy
  subst B
  obtain ⟨candyBefore, candyAfter, hcandySplit⟩ := List.append_of_mem hcandy
  obtain ⟨hsimple, hroute⟩ := A.orientedRoute_prefix_simple_and_mem _ hsplit
  have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
    (.flip R) hA hBstart hprefix hsimple hroute hpaths
  have hphase := A.repair_prefix_two_phase (.flip R) hA hBstart
    hprefix hsimple hroute hpaths
  have hgrooved := hprefix.grooved_of_switchSimple hsimple
  let alternate := flipAt contact R.actionSwitch
  obtain ⟨travel, hpositive, hjourney⟩ :=
    R.reverse_candy_suffix_absorbs_twoPhases contact hpaths hsecond hcandySplit
  have htail : ∀ d, ∃ port phase, stepN w d (p, contact) = some (port, phase) ∧
      (phase = contact ∨ phase = alternate) := by
    apply R.grooved_return_two_phase contact hpaths
      (hprefix.replay_grooved contact hgrooved) hgrooved ?_ (Or.inr rfl) (Or.inl rfl)
    intro current hc
    exact ⟨travel, alternate, hpositive, (hjourney current hc).1,
      Or.inr rfl, (hjourney current hc).2⟩
  have hpreAction := (ManufacturedReflector.flip R).preReturn_eq_action_activated
  change (ManufacturedReflector.flip R).preReturn.2 =
    flipAt (ManufacturedReflector.flip R).activatedState R.actionSwitch at hpreAction
  have hcontact : VectorCount.restrict N contact ∈ history := by
    rcases hrelation with heq | heq
    · simpa only [heq] using hinitialHistorical
    · simpa only [heq] using hpreHistorical
  have halternate : VectorCount.restrict N alternate ∈ history := by
    rcases hrelation with heq | heq
    · simpa only [alternate, heq, ← hpreAction] using hpreHistorical
    · simpa only [alternate, heq, hpreAction, flipAt_flipAt] using hinitialHistorical
  refine ⟨[], by simp, ?_⟩
  apply cover_of_live_phase_orbit hprefix.sound (phases := [contact, alternate])
  · intro d
    obtain ⟨port, phase, hr, hp⟩ := htail d
    exact ⟨port, phase, hr, by simpa using hp⟩
  · intro phase hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simpa using hcontact
    · simpa using halternate
  · intro d _ hd
    obtain ⟨port, phase, hr, hp⟩ := hphase d (by omega)
    rcases hp with heq | heq
    · simpa [restrictedTonguesAt, tonguesAt, hr, heq] using hinitialHistorical
    · simpa [restrictedTonguesAt, tonguesAt, hr, heq] using hcontact


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
  have hrecover := last_productive_recovers B.exploration_trace.sound
    htData.1 htData.2.1 hlast
  rw [hwriter] at hrecover
  rw [hrecover]
  exact List.mem_append_left _ (List.mem_map.mpr
    ⟨t, List.mem_range.mpr (by omega), rfl⟩)

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
  have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn B hA hB
    hrepair (A.orientedRoute_simple B.activatedState) (fun _ hp => hp) hBfinal
  have hAorBAHistorical :
      VectorCount.restrict N (A.toSupported.action.apply finalState) ∈ history ∨
      VectorCount.restrict N
        (B.toSupported.action.apply (A.toSupported.action.apply finalState)) ∈ history := by
    rcases hrelation with rfl | rfl
    · right
      simpa [B.preReturn_eq_action_activated,
        A.toSupported.action.commute B.toSupported.action] using haPreHistorical
    · exact Or.inl haPreHistorical
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
  have hinfo : ∀ k ∈ times.filter (fun k => decide (totalTravel < k)),
      (stepN w (k - totalTravel) (g, B.activatedState)).isSome ∧
      restrictedTonguesAt w N (g, B.activatedState) (k - totalTravel) =
        restrictedTonguesAt w N (g, A.baseState) k := by
    intro k hk
    obtain ⟨hk, hlate⟩ := List.mem_filter.mp hk
    have hle : totalTravel ≤ k := by simp only [decide_eq_true_eq] at hlate; omega
    refine ⟨?_, (restrictedTonguesAt_sub_of_reach hreachTotal hle (hlive k hk)).symm⟩
    have hrun := hlive k hk
    rw [show k = totalTravel + (k - totalTravel) by omega, stepN_add, hreachTotal] at hrun
    exact hrun
  have hmap : localTimes.map (restrictedTonguesAt w N (g, B.activatedState)) =
      (times.filter (fun k => decide (totalTravel < k))).map
        (restrictedTonguesAt w N (g, A.baseState)) := by
    rw [List.map_map]
    exact List.map_congr_left fun k hk => (hinfo k hk).2
  apply (htail localTimes (by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    exact (hinfo j hj).1) (by rw [hmap]; grind)).prepend
      hreachTotal hprefixCover hlive
  intro k hk hlate
  exact List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, by simp [hlate]⟩, rfl⟩

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
  have hcharge := A.reusable_add_continuation_first_writers_le
    hN B.exploration_trace B.exploration_simple hbaseGrooves hpreGrooves
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
      A B hA hB hpre history hinitialHistorical hpreHistorical with
    hone | hfacing | hcomplete
  · obtain ⟨fresh, hfresh, hmem⟩ := hone times hlive hnd
    exact ⟨fresh, by omega, hmem⟩
  · obtain ⟨fresh, hfresh, hmem⟩ :=
      hfacing.zero_novelty_of_preReturn hA hB history
        hinitialHistorical hpreHistorical times
    exact ⟨fresh, by omega, hmem⟩
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
      (ManufacturedReflector.flip R) B hA hB hpre history
        hinitialHistorical hpreHistorical with
    hone | hfacing | hcomplete
  · exact hone times hlive hnd
  · obtain ⟨fresh, hfresh, hmem⟩ := hfacing.zero_novelty_of_preReturn
      hA hB history hinitialHistorical hpreHistorical times
    exact ⟨fresh, by omega, hmem⟩
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
      (A.protected_repair_two_novelty_over_history B hAatBase
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
            B hAatBase hBpaths hpre history hhistory ht hwriter)
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
