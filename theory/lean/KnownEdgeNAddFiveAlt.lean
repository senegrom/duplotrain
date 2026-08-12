import StateLawCoefficientOneTop
import PartialSecondRunSharp
import ChangedFlipCountFour
import CompleteRepairFour
import MellitFiveNoveltyAssembly

/-!
# Known-edge `N+5`: the second historical overlap

This file audits the only branch still using the sixth additive constant in
the known-edge coefficient-one argument.  It is intentionally separate from
the existing proof files.
-/

namespace GeneralN

/-- The state immediately before a manufactured reflector's final return is
the reflector action applied to its activated state.  For a stay reflector
this is definitional.  For a flip reflector, the recorded candy traversal
leaves the first arm selected, so entering the opposite second arm performs
exactly the advertised flip. -/
theorem ManufacturedReflector.preReturn_eq_action_activated
    {w : Wiring} {g e : Nat}
    (B : ManufacturedReflector w g e) :
    B.preReturn.2 = B.toSupported.action.apply B.activatedState := by
  cases B with
  | stay R => rfl
  | flip R =>
      change R.returnState = flipAt R.afterReturn R.actionSwitch
      have hsimpleCandy :
          SwitchSimple ((R.mouth, R.firstArm) :: R.candy) := by
        have hs := R.simple
        unfold SwitchSimple at hs ⊢
        simp only [List.map_append] at hs
        exact (List.nodup_append.mp hs).2.1
      have hgrooved := R.candyTrace.grooved_of_switchSimple hsimpleCandy
      have hfirst : arrive R.returnState R.firstArm =
          (R.mouth, R.returnState) :=
        hgrooved (R.mouth, R.firstArm) List.mem_cons_self
      have hpinFirst : pin R.returnState R.firstArm = R.returnState := by
        have hsnd := congrArg Prod.snd hfirst
        simpa [arrive, R.firstArm_branch] using hsnd
      have hselected :
          R.returnState R.actionSwitch = bval R.firstArm := by
        have hbit := congrFun hpinFirst R.actionSwitch
        simpa [pin, R.firstArm_switch] using hbit.symm
      have hopposite :
          bval R.secondArm = !(R.returnState R.actionSwitch) := by
        rw [hselected]
        exact branch_values_opposite R.firstArm_branch
          R.secondArm_branch
          (R.firstArm_switch.trans R.secondArm_switch.symm)
          R.arms_ne
      have hpin : pin R.returnState R.secondArm =
          flipAt R.returnState R.actionSwitch :=
        pin_eq_flipAt R.secondArm_switch hopposite
      have hcross : R.afterReturn =
          flipAt R.returnState R.actionSwitch := by
        have hsnd := congrArg Prod.snd R.crossed
        have hpinAfter : pin R.returnState R.secondArm = R.afterReturn := by
          simpa [arrive, R.secondArm_branch] using hsnd
        exact hpinAfter.symm.trans hpin
      rw [hcross, flipAt_flipAt]

/-- The pre-return vector of the second construction is retained by the
coefficient-one two-history core. -/
theorem ManufacturedReflector.preReturn_mem_preservedTwoHistoryCore
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g) :
    VectorCount.restrict N B.preReturn.2 ∈
      A.preservedTwoHistoryCore B N := by
  apply A.mem_preservedTwoHistoryCore B
  right
  unfold ManufacturedReflector.sharpConstructionHistory
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨B.exploration.length, List.mem_range.mpr (by omega), ?_⟩
  have hreach := B.exploration_trace.sound
  simp [restrictedTonguesAt, tonguesAt, hreach]

/-- Moving one explicitly appended historical vector into the fresh list
costs exactly one unit of novelty budget. -/
theorem noveltyCoverOn_append_singleton_to_succ
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times : List Nat} {history : List (List Bool)}
    {x : List Bool} {budget : Nat}
    (hcover : NoveltyCoverOn w N start times (history ++ [x]) budget) :
    NoveltyCoverOn w N start times history (budget + 1) := by
  obtain ⟨fresh, hfresh, hmem⟩ := hcover
  refine ⟨x :: fresh, ?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · intro k hk
    have hm := hmem k hk
    simpa [List.append_assoc] using hm

/-- In the changed-forward flip branch, the construction's pre-return vector
is the missing old-action corner.  Once both the activated and pre-return
vectors are historical, the entire protected tail has at most two fresh
vectors, not three. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_two_novelty_of_preReturn
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hA : PathGrooves A.toSupported.paths
      (ManufacturedReflector.flip R).baseState)
    (hBstart : PathGrooves (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hmerge : A.ChangedForwardMerge (.flip R))
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N
      (ManufacturedReflector.flip R).activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N
      (ManufacturedReflector.flip R).preReturn.2 ∈ history)
    (times : List Nat) :
    NoveltyCoverOn w N
      (g, (ManufacturedReflector.flip R).activatedState)
      times history 2 := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, hOldTail, hApproachReplay, hApproachSimple,
      hApproachGrooved, hApproachForeign, _hCandyEq,
      hentryBranch, _hmouthStem, hmouthLink, harms,
      hfullGrooved, hfullTrace, hcrossed, hRpaths, _hCandy,
      hCandyForeignNew, hLobe, hreach, _hcomplete,
      hleadLen, _htailLen, _happroachLe,
      hActiveApproach, hApproachRoute⟩ :=
    hmerge.spliced_lobe_reflector_active_lead
  let initial := (ManufacturedReflector.flip R).activatedState
  let alternate := flipAt state (mouth / 3)
  let augmented := history ++ [VectorCount.restrict N alternate]
  have hpreAction :
      (ManufacturedReflector.flip R).preReturn.2 =
        flipAt initial R.actionSwitch := by
    simpa [initial, ManufacturedReflector.toSupported,
      ManufacturedFlipReflector.toSupported, LocalAction.apply] using
      (ManufacturedReflector.flip R).preReturn_eq_action_activated
  have hphase := A.repair_prefix_two_phase (.flip R) hA hBstart
    hActiveApproach hApproachSimple hApproachRoute hRpaths
  have hchangesRaw :=
    A.repair_prefix_changes_only_protected_return (.flip R)
      hA hBstart hActiveApproach hApproachSimple
      hApproachRoute hRpaths
  have hchanges : ∀ j, state j ≠ initial j → j = R.actionSwitch := by
    intro j hj
    have h := hchangesRaw j (by simpa [initial] using hj)
    change j = R.secondArm / 3 at h
    exact h.trans R.secondArm_switch
  have hrelation :
      initial = state ∨ initial = flipAt state R.actionSwitch :=
    tongues_eq_or_eq_flipAt_of_changes_only
      (u := initial) (v := state) (k := R.actionSwitch) hchanges
  have hstateHistoricalBase :
      VectorCount.restrict N state ∈ history := by
    rcases hrelation with hsame | hold
    · simpa [initial, hsame] using hinitialHistorical
    · have hpreState :
          (ManufacturedReflector.flip R).preReturn.2 = state := by
        calc
          (ManufacturedReflector.flip R).preReturn.2 =
              flipAt initial R.actionSwitch := hpreAction
          _ = state := by rw [hold, flipAt_flipAt]
      simpa [hpreState] using hpreHistorical
  have hinitialAug : VectorCount.restrict N initial ∈ augmented := by
    apply List.mem_append_left
    simpa [initial] using hinitialHistorical
  have hstateAug : VectorCount.restrict N state ∈ augmented :=
    List.mem_append_left _ hstateHistoricalBase
  have hentryAug : VectorCount.restrict N alternate ∈ augmented := by
    simp [augmented]
  have hleadHistorical : ∀ j, j < leadSteps →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈ augmented := by
    intro j hj
    have hjApproach : j ≤ approach.length := by
      rw [hleadLen] at hj
      omega
    obtain ⟨port, phase, hrun, hphaseEq⟩ := hphase j hjApproach
    have hvec : restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j =
        VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hrun]
    rw [hvec]
    rcases hphaseEq with hinit | hstate
    · have hinit' : phase = initial := by simpa [initial] using hinit
      simpa [hinit'] using hinitialAug
    · simpa [hstate] using hstateAug
  have hcoverAug : NoveltyCoverOn w N
      (g, (ManufacturedReflector.flip R).activatedState)
      times augmented 1 := by
    by_cases hrunway : (entry, mouth) ∈ R.runway
    · obtain ⟨before, after, hrunwaySplit⟩ := List.append_of_mem hrunway
      obtain ⟨C, hCAction, hEntryOldNe, hCpaths,
          hNewAvoidsCRaw, _htravel⟩ :=
        R.suffix_after_runway_passage_with_travel state hRpaths
          hrunwaySplit hmouthLink
      have hentrySwitch : entry / 3 = mouth / 3 := by
        have hheadGroove : arrive state entry = (mouth, state) :=
          hfullGrooved (mouth, entry) List.mem_cons_self
        have hswitch := arrive_exit_switch state entry
        rw [hheadGroove] at hswitch
        exact hswitch.symm
      have hActionsNe : mouth / 3 ≠ C.actionSwitch := by
        rw [← hentrySwitch]
        exact hEntryOldNe
      have hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
          C.toSupported.paths := by
        simpa [hentrySwitch] using hNewAvoidsCRaw
      have holdHistoricalBase : VectorCount.restrict N
          (flipAt state C.actionSwitch) ∈ history := by
        rcases hrelation with hsame | hold
        · have heq : flipAt state C.actionSwitch =
              (ManufacturedReflector.flip R).preReturn.2 := by
            rw [hCAction, ← hsame]
            exact hpreAction.symm
          simpa [heq] using hpreHistorical
        · have heq : flipAt state C.actionSwitch = initial := by
            rw [hCAction, ← hold]
          simpa [initial, heq] using hinitialHistorical
      have holdHistorical : VectorCount.restrict N
          (flipAt state C.actionSwitch) ∈ augmented :=
        List.mem_append_left _ holdHistoricalBase
      by_cases hcontact : ∃ passage ∈ candy,
          passageSwitch passage = C.actionSwitch
      · exact manufactured_flip_arbitrary_lobe_absolute_one_novelty
          C state hCpaths hNewAvoidsC hentryBranch hentrySwitch
          hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
          hmouthLink hcontact hreach times augmented hentryAug
          hstateAug holdHistorical (by
            intro j _hj hjLead
            exact hleadHistorical j hjLead)
      · have hCandyForeignOld : ∀ passage ∈ candy,
            passageSwitch passage ≠ C.actionSwitch := by
          intro passage hp hEq
          exact hcontact ⟨passage, hp, hEq⟩
        exact manufactured_suffix_explicit_lobe_absolute_one_novelty
          C state hCpaths hNewAvoidsC hActionsNe hentryBranch
          hentrySwitch hfullGrooved hfullTrace hcrossed
          hCandyForeignNew hCandyForeignOld hLobe hmouthLink hreach
          times augmented hentryAug hstateAug holdHistorical (by
            intro j _hj hjLead
            exact hleadHistorical j hjLead)
    · obtain ⟨old, hOldMem, horientation⟩ :=
        R.nonrunway_oriented_branch_entry_is_candy state
          horiented hrunway hentryBranch
      have hentryGrooved : arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hone := manufactured_flip_candy_splice_absolute_one_novelty
        R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
        hOldMem horientation hentryGrooved hApproachReplay hApproachGrooved
        hApproachForeign hcrossed hmouthLink harms hreach
        N augmented hentryAug times (by
          intro j _hj hjLead
          exact hleadHistorical j hjLead)
      obtain ⟨fresh, hfresh, hmem⟩ := hone
      exact ⟨fresh, hfresh, hmem⟩
  exact noveltyCoverOn_append_singleton_to_succ hcoverAug

/-- In the completed-repair branch, the activated and pre-return vectors are
two opposite corners of the restored pair's Gray square.  The other two
corners therefore form a two-vector novelty cover over the construction
history. -/
theorem ManufacturedReflector.completed_protected_route_two_novelty_of_preReturn
    {w : Wiring} {N g e : Nat}
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
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome) :
    NoveltyCoverOn w N (g, B.activatedState) times history 2 := by
  obtain ⟨reference, _hreferencePaths, hrouteEq, hfinishEq,
      hreferenceGrooved, _hguard⟩ :=
    A.current_route_reference B.baseState B.activatedState hA
  have hfinalGrooved :
      PassagesGrooved finalState (A.orientedRoute B.activatedState) :=
    hrepair.grooved_of_switchSimple
      (A.orientedRoute_simple B.activatedState)
  have hfinalReferenceGrooved :
      PassagesGrooved finalState (A.orientedRoute reference) := by
    rw [hrouteEq]
    exact hfinalGrooved
  have hreferenceGrooved' :
      PassagesGrooved reference (A.orientedRoute reference) := by
    rw [hrouteEq]
    exact hreferenceGrooved
  have horiented := A.oriented_data_eq_of_route_grooved
    reference finalState hreferenceGrooved' hfinalReferenceGrooved
  have hrouteFinal := A.orientedRoute_trace finalState hAfinal
  have hrouteFinal' : PhysicalTrace w (g, finalState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState) := by
    rw [horiented.1, horiented.2, hrouteEq, hfinishEq] at hrouteFinal
    exact hrouteFinal
  let L := (A.orientedRoute B.activatedState).length
  let endpoint : Nat × Tongues :=
    (A.orientedFinish B.activatedState, finalState)
  have hrepairReach : stepN w L (g, B.activatedState) =
      some endpoint := by
    simpa [L, endpoint] using hrepair.sound
  have hpairReach : stepN w L (g, finalState) = some endpoint := by
    simpa [L, endpoint] using hrouteFinal'.sound
  have hprefixPhase := A.repair_prefix_two_phase B hA hB
    hrepair (A.orientedRoute_simple B.activatedState)
    (by intro passage hp; exact hp) hBfinal
  have hrelation := A.completed_repair_initial_action_relation
    B hA hB hrepair hBfinal
  have hpreAction :
      B.preReturn.2 = B.toSupported.action.apply B.activatedState :=
    B.preReturn_eq_action_activated
  have hfinalHistorical :
      VectorCount.restrict N finalState ∈ history := by
    rcases hrelation with heq | haction
    · simpa [heq] using hinitialHistorical
    · have hpreFinal : B.preReturn.2 = finalState := by
        calc
          B.preReturn.2 =
              B.toSupported.action.apply B.activatedState := hpreAction
          _ = finalState := by
            rw [haction, B.toSupported.action.involutive]
      simpa [hpreFinal] using hpreHistorical
  have hBfinalHistorical : VectorCount.restrict N
      (B.toSupported.action.apply finalState) ∈ history := by
    rcases hrelation with heq | haction
    · have hpreB : B.preReturn.2 =
          B.toSupported.action.apply finalState := by
        rw [hpreAction, heq]
      simpa [hpreB] using hpreHistorical
    · simpa [haction] using hinitialHistorical
  let freshStates : List Tongues :=
    [A.toSupported.action.apply finalState,
      B.toSupported.action.apply
        (A.toSupported.action.apply finalState)]
  let fresh := freshStates.map (VectorCount.restrict N)
  have hfreshLength : fresh.length ≤ 2 := by
    simp [fresh, freshStates]
  have hcornerCover : ∀ phase ∈ manufacturedPairActionCorners A B finalState,
      VectorCount.restrict N phase ∈ history ++ fresh := by
    intro phase hp
    simp only [manufacturedPairActionCorners, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact List.mem_append_left _ hfinalHistorical
    · apply List.mem_append_right
      simp [fresh, freshStates]
    · exact List.mem_append_left _ hBfinalHistorical
    · apply List.mem_append_right
      simp [fresh, freshStates]
  refine ⟨fresh, hfreshLength, ?_⟩
  intro k hk
  by_cases hkpre : k ≤ L
  · obtain ⟨port, phase, hrun, hphase⟩ := hprefixPhase k hkpre
    have hvec : restrictedTonguesAt w N (g, B.activatedState) k =
        VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hrun]
    rw [hvec]
    rcases hphase with h | h
    · apply List.mem_append_left
      simpa [h] using hinitialHistorical
    · apply List.mem_append_left
      simpa [h] using hfinalHistorical
  · let d := k - L
    have hkEq : k = L + d := by
      dsimp [d]
      omega
    have hkLive := hlive k hk
    have htailLive : ∃ finish, stepN w d endpoint = some finish := by
      rw [hkEq, stepN_add, hrepairReach] at hkLive
      simp only [Option.bind_some] at hkLive
      cases htail : stepN w d endpoint with
      | none => simp [htail] at hkLive
      | some finish => exact ⟨finish, rfl⟩
    have hmem := manufactured_pair_reached_action_corners_tongues
      A B finalState hAfinal hBfinal hpairReach htailLive
    have hshift := tonguesAt_add_of_reaches hrepairReach htailLive
    have hcovered := hcornerCover (tonguesAt w endpoint d) hmem
    have hvector : restrictedTonguesAt w N
        (g, B.activatedState) k =
          VectorCount.restrict N (tonguesAt w endpoint d) := by
      unfold restrictedTonguesAt
      rw [hkEq]
      exact congrArg (VectorCount.restrict N) hshift
    simpa [hvector] using hcovered

/-- Global bookkeeping for the improved tail: the two completed construction
histories cost at most `N+3`, and a tail with two-vector novelty over that
same history gives `N+5`. -/
theorem ManufacturedReflector.two_journeys_then_two_novelty_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes,
        (stepN w k (g, B.activatedState)).isSome) →
      NoveltyCoverOn w N (g, B.activatedState) tailTimes
        (A.preservedTwoHistoryCore B N) 2)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let secondTravel := B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let history := A.preservedTwoHistoryCore B N
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
    · dsimp [history]
      apply A.mem_preservedTwoHistoryCore B
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
      have hliveQ := stepN_prefix_some hqLe hreachB
      have hshift := tonguesAt_add_of_reaches hreachA hliveQ
      have hm := B.manufacturing_journey_mem_sharpHistory
        (N := N) hBpaths (j := q)
          (by simpa [secondTravel] using hqLe)
      have hm' : restrictedTonguesAt w N (e, A.activatedState) q ∈
          B.sharpConstructionHistory N := by
        simpa [hbase] using hm
      have heq : restrictedTonguesAt w N (g, A.baseState) d =
          restrictedTonguesAt w N (e, A.activatedState) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      dsimp [history]
      exact A.mem_preservedTwoHistoryCore B (Or.inr hm')
  have hlocalLive : ∀ d ∈ localTimes,
      (stepN w d (g, B.activatedState)).isSome := by
    intro d hd
    obtain ⟨k, hkFiltered, rfl⟩ := List.mem_map.mp hd
    have hk := (List.mem_filter.mp hkFiltered).1
    have hkGt : totalTravel < k := by
      have := (List.mem_filter.mp hkFiltered).2
      simpa using this
    have hkEq : k = totalTravel + (k - totalTravel) := by omega
    have hkLive := hlive k hk
    rw [hkEq, stepN_add, hreachTotal] at hkLive
    exact hkLive
  have hlocalCover : NoveltyCoverOn w N
      (g, B.activatedState) localTimes history 2 := by
    dsimp [history]
    exact htail localTimes hlocalLive
  obtain ⟨fresh, hfresh, hlocalMem⟩ := hlocalCover
  have hglobalCover : NoveltyCoverOn w N (g, A.baseState)
      times history 2 := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hprefix : k ≤ totalTravel
    · apply List.mem_append_left
      exact hprefixCover k hprefix
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
      have hlocalReach : ∃ finish,
          stepN w d (g, B.activatedState) = some finish :=
        Option.isSome_iff_exists.mp (hlocalLive d hdMem)
      have hshift := tonguesAt_add_of_reaches hreachTotal hlocalReach
      have hvector : restrictedTonguesAt w N (g, A.baseState) k =
          restrictedTonguesAt w N (g, B.activatedState) d := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [hvector]
      exact hlocalMem d hdMem
  have hcount := noveltyCoverOn_distinct_count hglobalCover hnd
  have hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have hhistory : history.length ≤ N + 3 := by
    dsimp [history]
    exact A.preservedTwoHistoryCore_length_le_N_add_three
      hN B hbase hbaseGrooves hpre
  omega

/-- The support-preserving two-reflector branch needs only `N+5`: all
three-state outcomes use the ordinary boundary overlap, while the two
four-state outcomes use the activated/pre-return double overlap above. -/
theorem ManufacturedReflector.preReturn_grooved_all_run_distinct_le_N_add_five_alt
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  have hreachA := A.manufacturing_journey_reaches_activated hApaths
  have hreachB := B.manufacturing_journey_reaches_activated hBpaths
  have hreachB' :
      stepN w (B.exploration.length + B.runway.length + 1)
        (e, A.activatedState) = some (g, B.activatedState) := by
    rw [← hbase]
    exact hreachB
  have hAatBase :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have closeThree (htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes,
        (stepN w k (g, B.activatedState)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
      tailTimes.length ≤ 3) : times.length ≤ N + 5 := by
    have hc :=
      two_manufacturing_journeys_preserved_support_then_tail_distinct_le
        hN A B A.activatedState B.activatedState
        rfl rfl hreachA hApaths hbase rfl hreachB' hBpaths
        hpre htail (by omega) times hlive hnd
    omega
  have hinitialHistorical : VectorCount.restrict N B.activatedState ∈
      A.preservedTwoHistoryCore B N := by
    apply A.mem_preservedTwoHistoryCore B
    right
    simp [ManufacturedReflector.sharpConstructionHistory]
  have hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈
      A.preservedTwoHistoryCore B N :=
    A.preReturn_mem_preservedTwoHistoryCore B
  rcases manufactured_pair_protected_repair_constant_outcomes
      A B hAatBase hBpaths with hcount | hrest
  · exact closeThree hcount
  · rcases hrest with hfacing | hrest
    · exact closeThree (fun tailTimes tailLive tailNodup =>
        hfacing.distinct_le_three hAatBase hBpaths
          tailTimes tailLive tailNodup)
    · rcases hrest with hchanged | hcomplete
      · cases B with
        | stay R =>
            exact closeThree (fun tailTimes tailLive tailNodup =>
              hchanged.stay_distinct_le_three hAatBase hBpaths
                tailTimes tailLive tailNodup)
        | flip R =>
            apply A.two_journeys_then_two_novelty_le_N_add_five
              hN (.flip R) hbase hApaths hBpaths hpre
            · intro tailTimes _tailLive
              exact hchanged.flip_two_novelty_of_preReturn
                hAatBase hBpaths
                (A.preservedTwoHistoryCore (.flip R) N)
                hinitialHistorical hpreHistorical tailTimes
            · exact hlive
            · exact hnd
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        apply A.two_journeys_then_two_novelty_le_N_add_five
          hN B hbase hApaths hBpaths hpre
        · intro tailTimes tailLive
          exact A.completed_protected_route_two_novelty_of_preReturn
            B hAatBase hBpaths hrepair hAfinal hBfinal
            (A.preservedTwoHistoryCore B N)
            hinitialHistorical hpreHistorical tailTimes tailLive
        · exact hlive
        · exact hnd

/-- **Unconditional two-reflector `N+5` theorem.**  Damage was already
`N+5`; preservation is sharpened by the second historical overlap. -/
theorem ManufacturedReflector.two_journeys_all_run_distinct_le_N_add_five_alt
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  by_cases hpre : PathGrooves A.toSupported.paths B.preReturn.2
  · exact A.preReturn_grooved_all_run_distinct_le_N_add_five_alt
      hN B hbase hApaths hBpaths hpre times hlive hnd
  · exact A.preReturn_broken_all_run_distinct_le_N_add_five
      hN B hbase hApaths hpre times hlive hnd

/-- The original known-edge decomposition with its sole `N+6` call replaced
by the sharpened two-reflector `N+5` theorem. -/
theorem known_edge_N_add_five_or_one_reflector_early_outcome_alt
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k, k ∈ times → (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 5 ∨
      Nonempty (OneReflectorSecondDead w N e start) ∨
      Nonempty (OneReflectorDamagedCycle w N e start) := by
  cases hfirst : stepN w (N + 1) start with
  | none =>
      left
      have hc := dead_horizon_live_distinct_le
        hfirst times hlive hnd
      omega
  | some firstFinish =>
      rcases first_activated_count_outcome_sharp
          hN hfirst hentry with hcycleA | hreflectorA
      · left
        have hc := hcycleA times hnd
        omega
      · obtain ⟨A, stateA, _hfirstLe, hgroovesA,
          hbaseA, hactivatedA, hreachA, _hpreservesA⟩ := hreflectorA
        subst stateA
        have hentryB : w.link start.1 = some e :=
          w.symm _ _ hentry
        have hliveA : ∀ k, k ∈ times →
            (stepN w k (start.1, A.baseState)).isSome := by
          simpa [hbaseA] using hlive
        have hndA : (times.map
            (restrictedTonguesAt w N
              (start.1, A.baseState))).Nodup := by
          simpa [hbaseA] using hnd
        have closePair : ∀
            (B : ManufacturedReflector w e start.1),
            B.baseState = A.activatedState →
            PathGrooves B.toSupported.paths B.activatedState →
            times.length ≤ N + 5 := by
          intro B hbaseB hgroovesB
          exact A.two_journeys_all_run_distinct_le_N_add_five_alt
            hN B hbaseB hgroovesA hgroovesB
            times hliveA hndA
        cases hsecond : stepN w (N + 1)
            (e, A.activatedState) with
        | none =>
            right
            left
            exact ⟨{
              A := A
              grooves := hgroovesA
              base := hbaseA
              reached := hreachA
              dead := hsecond
            }⟩
        | some secondFinish =>
            rcases first_activated_count_outcome_sharp
                (w := w) (N := N) (e := start.1)
                hN hsecond hentryB with
              _hcycleB | hreflectorB
            · rcases first_activated_trace_outcome_sharp
                  (w := w) (N := N) (e := start.1)
                  hN hsecond hentryB with htraceCycle | hreflectorB'
              · obtain ⟨C⟩ := htraceCycle
                by_cases hrepeat :
                    PathGrooves A.toSupported.paths C.atRepeat.2
                · left
                  have hc := C.preserved_all_run_distinct_le_N_add_three
                    hN A hgroovesA hrepeat times hliveA hndA
                  omega
                · right
                  right
                  exact ⟨{
                    A := A
                    grooves := hgroovesA
                    base := hbaseA
                    reached := hreachA
                    cycle := C
                    damaged := hrepeat
                  }⟩
              · obtain ⟨B, stateB, _hsecondLe, hgroovesB,
                    hbaseB, hactivatedB, _hreachB,
                    _hpreservesB⟩ := hreflectorB'
                subst stateB
                left
                exact closePair B hbaseB hgroovesB
            · obtain ⟨B, stateB, _hsecondLe, hgroovesB,
                  hbaseB, hactivatedB, _hreachB,
                  _hpreservesB⟩ := hreflectorB
              subst stateB
              left
              exact closePair B hbaseB hgroovesB

/-- The early damaged-cycle classifier preserves the sharpened constant. -/
theorem known_edge_N_add_five_or_exact_one_reflector_outcome_alt
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 5 ∨
      Nonempty (OneReflectorSecondDead w N e start) ∨
      Nonempty (OneReflectorForwardDamagedCycle w N e start) := by
  rcases known_edge_N_add_five_or_one_reflector_early_outcome_alt
      hN hentry times hlive hnd with hclosed | hdead | hdamaged
  · exact Or.inl hclosed
  · exact Or.inr (Or.inl hdead)
  · obtain ⟨D⟩ := hdamaged
    rcases D.N_add_three_or_forward hN times hlive hnd with
      hbackward | hforward
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr hforward)

theorem ManufacturedReflector.partial_second_run_distinct_le_N_add_five_alt
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  cases hprobe : stepN w (N + 1) (e, A.activatedState) with
  | none =>
      exact
        PartialSecondRunSharp.ManufacturedReflector.dead_second_run_distinct_le_N_add_five
          hN A hA hprobe times hlive hnd
  | some finish =>
      have hentry : w.link g = some e := w.symm _ _ A.entryEdge
      rcases first_activated_trace_outcome_sharp_partial
          hN hprobe hentry with hcycle | hreflector
      · obtain ⟨C⟩ := hcycle
        exact
          PartialSecondRunSharp.PartialSecondCycleOutcome.all_run_distinct_le_N_add_five
            hN A hA C times hlive hnd
      · obtain ⟨B, state, _hlength, hB, hbase,
            _hactivated, _hreach, _hpreserves⟩ := hreflector
        subst state
        exact A.two_journeys_all_run_distinct_le_N_add_five_alt
          hN B hbase hA hB times hlive hnd

/-- **Known-edge coefficient-one `N+5` theorem.**  The first probe either
dies, settles on its retained cycle, or manufactures a reflector; the
partial second run closes all three continuations at the same constant. -/
theorem known_edge_all_run_distinct_le_N_add_five_alt
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 5 := by
  cases hfirst : stepN w (N + 1) start with
  | none =>
      have hshort := dead_horizon_live_distinct_le
        hfirst times hlive hnd
      omega
  | some finish =>
      rcases first_activated_count_outcome_sharp
          hN hfirst hentry with hcycle | hreflector
      · have hshort := hcycle times hnd
        omega
      · obtain ⟨A, state, _hlength, hA, hbase,
            _hactivated, _hreach, _hpreserves⟩ := hreflector
        subst state
        have hliveA : ∀ k ∈ times,
            (stepN w k (start.1, A.baseState)).isSome := by
          simpa [hbase] using hlive
        have hndA : (times.map
            (restrictedTonguesAt w N
              (start.1, A.baseState))).Nodup := by
          simpa [hbase] using hnd
        exact A.partial_second_run_distinct_le_N_add_five_alt
          hN hA times hliveA hndA

/-- **Unconditional raw `N+6` theorem.**  The generic arbitrary-start lift
costs exactly its one possible time-zero vector. -/
theorem state_law_linear_N_add_six_alt
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  have hbound := arbitrary_start_distinct_le_succ_of_all_known_edge
    (w := w) (N := N) (cap := N + 5)
    (fun hentry localTimes hlocalLive hlocalNodup =>
      known_edge_all_run_distinct_le_N_add_five_alt
        hN hentry localTimes hlocalLive hlocalNodup)
    start times hlive hnd
  omega

/-- The exact raw state-law declaration: an arbitrary run on `N` switches
contains at most `N+6` pairwise-distinct restricted tongue vectors. -/
theorem stateLaw_N_add_six_alt : StateLaw := by
  intro w N hN start times hlive hnd
  exact state_law_linear_N_add_six_alt
    w N hN start times hlive hnd

theorem stateLaw : StateLaw := stateLaw_N_add_six_alt

end GeneralN
