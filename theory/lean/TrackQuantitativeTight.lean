import TrackQuantitative

/-!
# Tight quantitative extraction

This file sharpens the direct physical-track lasso accounting without
changing the qualitative repair argument.  The key point is that a runway
contact discards an exact prefix of the old reflector: the prefix appearing
in the selected route has the same length as the prefix appearing in the
runway, and the suffix reflector saves exactly twice that prefix length plus
the contacted passage.
-/

namespace GeneralN

private theorem nodup_map_fibre_tight
    {α β γ : Type} (xs : List α) (f : α → β) (g : α → γ)
    (hfibre : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → g x = g y)
    (hnd : (xs.map g).Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      constructor
      · intro hmem
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
        have hgy := hfibre x List.mem_cons_self y
          (List.mem_cons_of_mem _ hy) hfy.symm
        exact hnd.1 (List.mem_map.mpr ⟨y, hy, hgy.symm⟩)
      · exact ih
          (fun a ha b hb => hfibre a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb)) hnd.2

/-- If a passage lies on the runway of a selected flip-reflector route, the
prefix selected by splitting the full route has exactly the runway-prefix
length.  Switch simplicity makes the split at the passage's switch unique. -/
theorem ManufacturedFlipReflector.runway_split_prefix_length
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    {entry mouth : Nat}
    {oldPrefix oldTail before after : List Passage}
    (hrouteSplit :
      (ManufacturedReflector.flip R).orientedRoute state =
        oldPrefix ++ (entry, mouth) :: oldTail)
    (hrunwaySplit :
      R.runway = before ++ (entry, mouth) :: after) :
    oldPrefix.length = before.length := by
  obtain ⟨canonicalTail, hcanonical⟩ :
      ∃ canonicalTail,
        (ManufacturedReflector.flip R).orientedRoute state =
          before ++ (entry, mouth) :: canonicalTail := by
    by_cases hselected :
        state R.actionSwitch = bval R.firstArm
    · refine
        ⟨after ++ (R.mouth, R.firstArm) :: R.candy, ?_⟩
      simp only [ManufacturedReflector.orientedRoute, hselected, if_pos]
      rw [hrunwaySplit]
      simp [List.append_assoc]
    · refine
        ⟨after ++
          (R.mouth, R.secondArm) :: reversePassages R.candy, ?_⟩
      simp only [ManufacturedReflector.orientedRoute, hselected, if_false]
      rw [hrunwaySplit]
      simp [List.append_assoc]
  have hsimple :
      (((ManufacturedReflector.flip R).orientedRoute state).map
        passageSwitch).Nodup := by
    exact (ManufacturedReflector.flip R).orientedRoute_simple state
  have hmapSplit :
      ((ManufacturedReflector.flip R).orientedRoute state).map
          passageSwitch =
        oldPrefix.map passageSwitch ++
          passageSwitch (entry, mouth) ::
            oldTail.map passageSwitch := by
    rw [hrouteSplit]
    simp
  have hmapCanonical :
      ((ManufacturedReflector.flip R).orientedRoute state).map
          passageSwitch =
        before.map passageSwitch ++
          passageSwitch (entry, mouth) ::
            canonicalTail.map passageSwitch := by
    rw [hcanonical]
    simp
  have hpref :=
    (nodup_nat_split_unique hsimple hmapSplit hmapCanonical).1
  have hlen := congrArg List.length hpref
  simpa using hlen

/-- Exact runway accounting, including the lead into the newly spliced lobe.
The shortened old reflector and the new lobe share the discarded runway
prefix in opposite directions, so the coarse independent bounds collapse to
an 18*N lasso. -/
private theorem manufactured_flip_runway_splice_with_lead_within_eighteen
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hRpaths : PathGrooves R.toSupported.paths state)
    {entry mouth returnPort outside : Nat}
    {before after approach candy : List Passage}
    {start : Nat × Tongues} {leadSteps : Nat}
    (hrunwaySplit : R.runway = before ++ (entry, mouth) :: after)
    (hmouthLink : w.link mouth = some outside)
    (hentryBranch : entry % 3 ≠ 0)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandy : PassagesGrooved state candy)
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hcandyLen : candy.length = before.length + approach.length)
    (hreach : stepN w leadSteps start =
      some (outside, flipAt state (mouth / 3)))
    (hleadLen : leadSteps = approach.length + 1)
    (happroachLe : approach.length + 1 ≤ 2 * N) :
    EventuallyPeriodicWithin w start (18 * N) := by
  obtain ⟨C, _hCAction, _hActionsNe, hCpaths, hNewAvoidsC,
      htravelExact⟩ :=
    R.suffix_after_runway_passage_with_travel state hRpaths
      hrunwaySplit hmouthLink
  have hentrySwitch : entry / 3 = mouth / 3 := by
    have hheadGroove : arrive state entry = (mouth, state) :=
      hgrooved (mouth, entry) List.mem_cons_self
    have hswitch := arrive_exit_switch state entry
    rw [hheadGroove] at hswitch
    exact hswitch.symm
  have hNewAvoidsC' :
      (LocalAction.flip (mouth / 3)).Avoids
        C.toSupported.paths := by
    simpa [hentrySwitch] using hNewAvoidsC
  have hlocal : EventuallyPeriodicWithin w
      (outside, flipAt state (mouth / 3))
      (4 * (C.toSupported.travel + (candy.length + 2))) := by
    by_cases hcontact : ∃ passage ∈ candy,
        passageSwitch passage = C.actionSwitch
    · exact manufactured_flip_arbitrary_lobe_within C state hCpaths
        hNewAvoidsC' hentryBranch hentrySwitch hgrooved htrace
        hcrossed hCandyForeign hLobe hcontact
    · let L : SupportedReflector w mouth outside := {
        travel := candy.length + 2
        paths := [candy]
        action := .flip (mouth / 3)
        run := by
          intro current hpaths
          have hCandyCurrent : PassagesGrooved current candy :=
            hpaths candy (by simp)
          obtain ⟨hstep, hnext⟩ := hLobe current hCandyCurrent
          constructor
          · exact hstep
          · intro path hpath
            simp only [List.mem_singleton] at hpath
            subst path
            exact hnext
      }
      have hOldAvoidsL : C.toSupported.action.Avoids L.paths := by
        change (LocalAction.flip C.actionSwitch).Avoids [candy]
        intro path hpath passage hpassage
        simp only [List.mem_singleton] at hpath
        subst path
        intro hEq
        exact hcontact ⟨passage, hpassage, hEq⟩
      have hCflip : PathGrooves C.toSupported.paths
          (flipAt state (mouth / 3)) :=
        hCpaths.after_avoiding_action hNewAvoidsC'
      have hCandyFlip :
          PassagesGrooved (flipAt state (mouth / 3)) candy :=
        grooved_after_flip_other hCandy hCandyForeign
      have hLflip : PathGrooves L.paths
          (flipAt state (mouth / 3)) := by
        intro path hpath
        simp only [L, List.mem_singleton] at hpath
        subst path
        exact hCandyFlip
      have hperiod := C.toSupported.paired_period L
        hOldAvoidsL hNewAvoidsC'
        (flipAt state (mouth / 3)) hCflip hLflip
      have hpositive :
          0 < 2 * (C.toSupported.travel + L.travel) := by
        dsimp [L]
        omega
      exact eventuallyPeriodicWithin_of_period hpositive (by
        dsimp [L]
        omega) hperiod
  have hRtravel : R.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip R).travel_le_two_mul_switches hN
  have hNpos : 0 < N := by
    have hports := hN mouth outside hmouthLink
    omega
  have hbudget :
      leadSteps +
          4 * (C.toSupported.travel + (candy.length + 2)) ≤
        18 * N := by
    rw [hleadLen, hcandyLen]
    omega
  exact (hlocal.prepend hreach).weaken hbudget

/-- A state-changing forward merge into a manufactured flip reflector closes
within 18*N. Runway contacts use exact suffix accounting; candy contacts
retain the previous 8*N/16*N cycles. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_within_eighteen
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R)) :
    EventuallyPeriodicWithin w
      (g, (ManufacturedReflector.flip R).activatedState) (18 * N) := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, hOldTail, hApproach, hApproachGrooved,
      hApproachForeign, hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete, hleadLen, _htailLen, happroachLe⟩ :=
    hmerge.spliced_lobe_reflector
  have hAtravel : A.toSupported.travel ≤ 2 * N :=
    A.travel_le_two_mul_switches hN
  have hRtravel :
      (ManufacturedReflector.flip R).toSupported.travel ≤ 2 * N :=
    (ManufacturedReflector.flip R).travel_le_two_mul_switches hN
  have hleadLe : leadSteps ≤ 2 * N := by
    rw [hleadLen]
    omega
  have hcandyLen : candy.length =
      oldPrefix.length + approach.length := by
    rw [hCandyEq]
    simp [reversePassages_length]
  have hNpos : 0 < N := by
    have hports := hN mouth outside hmouthLink
    omega
  have holdTailLeRoute : oldTail.length ≤
      ((ManufacturedReflector.flip R).orientedRoute state).length := by
    rw [hrouteSplit]
    simp
    omega
  have holdTailLe : oldTail.length ≤ 2 * N :=
    Nat.le_trans holdTailLeRoute
      (Nat.le_trans
        ((ManufacturedReflector.flip R).orientedRoute_length_le_travel state)
        hRtravel)
  have hrunwayLe : R.runway.length ≤ 2 * N := by
    have hle : R.runway.length ≤
        (ManufacturedReflector.flip R).toSupported.travel := by
      simp [ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported]
      omega
    exact Nat.le_trans hle hRtravel
  have happLe : approach.length ≤ 2 * N := by
    omega
  let cycleSteps :=
    oldTail.length + R.runway.length + approach.length + 2
  have hcycleLe : cycleSteps ≤ 8 * N := by
    dsimp [cycleSteps]
    omega
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ :=
      List.append_of_mem hrunway
    have hprefixLen :=
      R.runway_split_prefix_length state hrouteSplit hrunwaySplit
    have hcandyTight :
        candy.length = before.length + approach.length := by
      omega
    have happOneLe : approach.length + 1 ≤ 2 * N :=
      Nat.le_trans happroachLe hAtravel
    exact manufactured_flip_runway_splice_with_lead_within_eighteen
      hN R state hRpaths hrunwaySplit hmouthLink hentryBranch
      hfullGrooved hfullTrace hcrossed hCandy hCandyForeign hLobe
      hcandyTight hreach hleadLen happOneLe
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        horiented hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    by_cases hcontact : ∃ passage ∈ approach,
        passageSwitch passage = R.actionSwitch
    · have hperiodic :=
        manufactured_flip_candy_splice_periodic_of_approach_contact
          R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
          hold horientation hentryGrooved hApproach hApproachGrooved
          hApproachForeign hcrossed hmouthLink harms hcontact
      have hperiod : stepN w cycleSteps
          (outside, flipAt state (mouth / 3)) =
            some (outside, flipAt state (mouth / 3)) := by
        simpa [cycleSteps] using hperiodic.2
      have hlocal : EventuallyPeriodicWithin w
          (outside, flipAt state (mouth / 3)) (8 * N) :=
        eventuallyPeriodicWithin_of_period (by
          dsimp [cycleSteps]
          omega) hcycleLe hperiod
      exact (hlocal.prepend hreach).weaken (by omega)
    · have hApproachForeignOld : ∀ passage ∈ approach,
          passageSwitch passage ≠ R.actionSwitch := by
        intro passage hpassage hEq
        exact hcontact ⟨passage, hpassage, hEq⟩
      have hperiodic :=
        manufactured_flip_candy_splice_periodic_of_approach_foreign
          R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
          hold horientation hentryGrooved hApproach hApproachForeign
          hApproachForeignOld hcrossed hmouthLink
      obtain ⟨settled, hcycleLead, hcyclePeriod⟩ := hperiodic.2
      have hcycleLead' : stepN w cycleSteps
          (outside, flipAt state (mouth / 3)) = some settled := by
        simpa [cycleSteps] using hcycleLead
      have hcyclePeriod' : stepN w cycleSteps settled = some settled := by
        simpa [cycleSteps] using hcyclePeriod
      have hlocal : EventuallyPeriodicWithin w
          (outside, flipAt state (mouth / 3)) (16 * N) :=
        ⟨cycleSteps, cycleSteps, settled, by
          dsimp [cycleSteps]
          omega, by omega, hcycleLead', hcyclePeriod'⟩
      exact (hlocal.prepend hreach).weaken (by omega)

/-- Uniform tight wrapper for either action of the retained reflector. -/
theorem ManufacturedReflector.ChangedForwardMerge.within_eighteen
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.ChangedForwardMerge B) :
    EventuallyPeriodicWithin w (g, B.activatedState) (18 * N) := by
  cases B with
  | stay R => exact (hmerge.stay_within_sixteen hN).weaken (by omega)
  | flip R => exact hmerge.flip_within_eighteen hN

/-- Damaged support is repaired or absorbed within 22*N. The complete route
branch, rather than a changed forward merge, is now the bottleneck. -/
theorem manufactured_pair_protected_repair_within_twenty_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    EventuallyPeriodicWithin w (g, B.activatedState) (22 * N) := by
  rcases manufactured_pair_protected_repair_quantitative_outcomes
      hN A B hA hB with hperiodic | hrest
  · exact hperiodic.weaken (by omega)
  · rcases hrest with hfacing | hrest
    · exact (hfacing.within_twelve hN).weaken (by omega)
    · rcases hrest with hchanged | hcomplete
      · exact (hchanged.within_eighteen hN).weaken (by omega)
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        exact A.completed_route_with_pair_support_within hN B
          B.baseState B.activatedState finalState hA hrepair
          hAfinal hBfinal

/-- Tight global lasso with a known incoming edge. -/
theorem long_run_eventually_periodic_within_twenty_six
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1) :
    EventuallyPeriodicWithin w start (26 * N + 2) := by
  rcases long_run_within_or_damaged_pair hN hlive hentry with
    hperiodic | hdamaged
  · exact hperiodic.weaken (by omega)
  · obtain ⟨A, B, stateA, stateB, firstTravel, secondTravel,
      hfirstLe, hsecondLe, _hbaseA, _hactivatedA,
      hreachA, hgroovesA, hbaseB, hactivatedB,
      hreachB, hgroovesB, _hpreservesB,
      _hnotGrooved, _hcontact⟩ := hdamaged
    have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
      simpa [hbaseB] using hgroovesA
    have hBatActivated :
        PathGrooves B.toSupported.paths B.activatedState := by
      simpa [← hactivatedB] using hgroovesB
    have hlocal := manufactured_pair_protected_repair_within_twenty_two
      hN A B hAatBase hBatActivated
    have hreach : stepN w (firstTravel + secondTravel) start =
        some (start.1, B.activatedState) := by
      rw [stepN_add, hreachA]
      simpa [hactivatedB] using hreachB
    exact (hlocal.prepend hreach).weaken (by omega)

/-- Entry-free tight global lasso. -/
theorem long_run_eventually_periodic_within_twenty_six_without_entry
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (3 * N + 3) start = some finish) :
    EventuallyPeriodicWithin w start (26 * N + 3) := by
  have hsplit : 3 * N + 3 = 1 + (3 * N + 2) := by omega
  rw [hsplit, stepN_add] at hlive
  cases hone : stepN w 1 start with
  | none =>
      rw [hone] at hlive
      contradiction
  | some middle =>
      rw [hone] at hlive
      simp only [Option.bind_some] at hlive
      rcases start with ⟨startPort, startState⟩
      have honeStep : stepN w 1 (startPort, startState) =
          some middle := hone
      simp only [stepN, step] at hone
      let localStep := arrive startState startPort
      cases hlink : w.link localStep.1 with
      | none =>
          simp [localStep, hlink] at hone
      | some entry =>
          have hmiddle : middle = (entry, localStep.2) := by
            simpa [localStep, hlink] using hone.symm
          subst middle
          have hlocal := long_run_eventually_periodic_within_twenty_six
            hN hlive hlink
          exact (hlocal.prepend honeStep).weaken (by omega)

/-- **GENERAL LINEAR STATE LAW, TIGHT QUANTITATIVE FORM.**
Any raw N-switch lazy-point track exposes at most 26*N+3 distinct tongue
vectors to one train. The coefficient-one StateLaw remains open. -/
theorem state_law_linear_twenty_six
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (c0 : Nat × Tongues) (ks : List Nat)
    (hlive : ∀ k ∈ ks, (stepN w k c0).isSome)
    (hnd : (ks.map fun k =>
      VectorCount.restrict N (tonguesAt w c0 k)).Nodup) :
    ks.length ≤ 26 * N + 3 := by
  cases hlong : stepN w (3 * N + 3) c0 with
  | some finish =>
      have hperiodic :=
        long_run_eventually_periodic_within_twenty_six_without_entry
          hN hlong
      exact hperiodic.tongue_vector_count ks hlive hnd
  | none =>
      have hksNodup : ks.Nodup := by
        have hmapped : (ks.map id).Nodup := by
          apply nodup_map_fibre_tight ks id
            (fun k => VectorCount.restrict N (tonguesAt w c0 k))
          · intro i _hi j _hj hij
            have hij' : i = j := by simpa using hij
            rw [hij']
          · exact hnd
        simpa using hmapped
      have hlt : ∀ k ∈ ks, k < 3 * N + 3 := by
        intro k hk
        by_cases hsmall : k < 3 * N + 3
        · exact hsmall
        · exfalso
          have hkge : 3 * N + 3 ≤ k := by omega
          have hkEq : k = (3 * N + 3) + (k - (3 * N + 3)) := by
            omega
          have hnone : stepN w k c0 = none := by
            rw [hkEq, stepN_add, hlong]
            simp
          have hkLive := hlive k hk
          simp [hnone] at hkLive
      have hshort := nodup_nat_lt_length hksNodup hlt
      omega

end GeneralN
