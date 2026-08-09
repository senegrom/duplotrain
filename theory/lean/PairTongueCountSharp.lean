import TrackThetaTighter
import ManufacturedPairNovelty
import NoveltyAwareLasso

/-!
# Tongue-count sharpening for reflector pairs

Physical travel is a poor proxy for tongue-vector novelty.  A complete
manufactured-reflector traversal has exactly two tongue phases, regardless
of its geometric length.  If the endpoint starts a bounded lasso, the second
phase is already time zero of that lasso.  Thus the complete prefix costs
only one additional vector above the lasso history.
-/

namespace GeneralN

private theorem pairsharp_zero_novelty_cover_of_mem
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (times : List Nat) (history : List (List Bool))
    (hmem : ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈ history) :
    NoveltyCoverOn w N start times history 0 := by
  refine ⟨[], by simp, ?_⟩
  intro k hk
  simpa using hmem k hk

/-- A complete manufactured-reflector traversal followed by a `cap`-lasso
exposes at most `cap+1` distinct restricted tongue vectors.  The entire
reflector traversal contributes only its incoming vector beyond the suffix
history, because its outgoing action-state is exactly suffix time zero. -/
theorem ManufacturedReflector.traversal_then_lasso_distinct_le_succ
    {w : Wiring} {N g e cap : Nat}
    (A : ManufacturedReflector w g e)
    (state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state)
    (hlocal : EventuallyPeriodicWithin w
      (e, A.toSupported.action.apply state) cap)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k (g, state)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, state))).Nodup) :
    times.length ≤ cap + 1 := by
  let travel := A.toSupported.travel
  let outgoing := A.toSupported.action.apply state
  let incomingVector := VectorCount.restrict N state
  let outgoingVector := VectorCount.restrict N outgoing
  let tailHistory := hlocal.tongueHistory N
  let tailReduced := tailHistory.erase outgoingVector
  let history := [incomingVector, outgoingVector] ++ tailReduced
  have hrun : stepN w travel (g, state) = some (e, outgoing) := by
    dsimp [travel, outgoing]
    exact (A.toSupported.run state hpaths).1
  have houtTail : outgoingVector ∈ tailHistory := by
    have hm := hlocal.mem_tongueHistory (N := N) (k := 0)
    have hzero : restrictedTonguesAt w N (e, outgoing) 0 =
        outgoingVector := by
      dsimp [outgoingVector]
      simp [restrictedTonguesAt, tonguesAt, stepN]
    rw [← hzero]
    simpa [tailHistory, outgoing] using hm
  have hmem : ∀ k ∈ times,
      restrictedTonguesAt w N (g, state) k ∈ history := by
    intro k hk
    by_cases hprefix : k ≤ travel
    · have hphase := A.travel_two_phase_tongues state hpaths hprefix
      rcases hphase with hin | hout
      · dsimp [history]
        simp [restrictedTonguesAt, hin, incomingVector]
      · dsimp [history]
        simp [restrictedTonguesAt, hout, outgoingVector, outgoing]
    · let d := k - travel
      have hkEq : k = travel + d := by
        dsimp [d]
        omega
      have hkLive := hlive k hk
      have hlocalLive : ∃ finish,
          stepN w d (e, outgoing) = some finish := by
        cases hd : stepN w d (e, outgoing) with
        | none =>
            have hnone : stepN w k (g, state) = none := by
              rw [hkEq, stepN_add, hrun]
              simp [hd]
            rw [hnone] at hkLive
            simp at hkLive
        | some finish => exact ⟨finish, rfl⟩
      have hshift := tonguesAt_add_of_reaches hrun hlocalLive
      have hm := hlocal.mem_tongueHistory (N := N) (k := d)
      have hm' : restrictedTonguesAt w N (e, outgoing) d ∈
          tailHistory := by
        simpa [tailHistory, outgoing] using hm
      have heq : restrictedTonguesAt w N (g, state) k =
          restrictedTonguesAt w N (e, outgoing) d := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      by_cases houtEq :
          restrictedTonguesAt w N (e, outgoing) d = outgoingVector
      · dsimp [history]
        simp [houtEq]
      · apply List.mem_append_right [incomingVector, outgoingVector]
        dsimp [tailReduced]
        exact (List.mem_erase_of_ne houtEq).mpr hm'
  have hcover := pairsharp_zero_novelty_cover_of_mem times history hmem
  have hcountRaw := noveltyCoverOn_distinct_count hcover hnd
  have hcount : times.length ≤ history.length := by
    simpa using hcountRaw
  have htailLen : tailHistory.length = cap := by
    simp [tailHistory, EventuallyPeriodicWithin.tongueHistory]
  have htailReducedLen : tailReduced.length = tailHistory.length - 1 := by
    dsimp [tailReduced]
    exact List.length_erase_of_mem houtTail
  have hcapPos : 0 < cap := by
    obtain ⟨lead, period, settled, hperiodPos, hcap,
      _hlead, _hperiod⟩ := hlocal
    omega
  have hhistoryLen : history.length ≤ cap + 1 := by
    dsimp [history]
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [htailReducedLen, htailLen]
    omega
  exact Nat.le_trans hcount hhistoryLen

/-- Any opposite manufactured reflector pair with both supports grooved
exposes at most `12*N+3` distinct restricted tongue vectors at arbitrary live
sample times.  The only branch whose physical lasso costs `14*N+2` is the
one-sided intersection seen from the wrong endpoint; its extra reflector
traversal has only two tongue phases, one of which is the lasso boundary. -/
theorem manufactured_pair_tongue_vector_count_twelve_succ_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k (g, state)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, state))).Nodup) :
    times.length ≤ 12 * N + 3 := by
  classical
  have hnd' : (times.map (fun k =>
      VectorCount.restrict N (tonguesAt w (g, state) k))).Nodup := by
    exact hnd
  cases A with
  | stay SA =>
      cases B with
      | stay SB =>
          have hlocal := manufactured_pair_within_eight_mul_switches_of_avoids
            hN (.stay SA) (.stay SB) state hA hB
              (by trivial) (by trivial)
          have hc := hlocal.tongue_vector_count times hlive hnd'
          omega
      | flip FB =>
          change PathGrooves
            [SA.runway, [(SA.mouth, SA.arm)]] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
              [SA.runway, [(SA.mouth, SA.arm)]]
          · have hlocal := manufactured_pair_within_eight_mul_switches_of_avoids
              hN (.stay SA) (.flip FB) state hA hB
                (by trivial) hBA
            have hc := hlocal.tongue_vector_count times hlive hnd'
            omega
          · have hcontact := contact_of_not_avoids_flip hBA
            have hlocal := manufactured_flip_then_stay_within_eight
              hN FB SA state hB hA hcontact
            have hlocal' : EventuallyPeriodicWithin w
                (e, (ManufacturedReflector.stay SA).toSupported.action.apply state)
                (8 * N) := by
              simpa [ManufacturedReflector.toSupported,
                ManufacturedStayReflector.toSupported, LocalAction.apply]
                using hlocal
            have hc := ManufacturedReflector.traversal_then_lasso_distinct_le_succ
              (ManufacturedReflector.stay SA) state hA hlocal'
                times hlive hnd
            omega
  | flip FA =>
      cases B with
      | stay SB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves
            [SB.runway, [(SB.mouth, SB.arm)]] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [SB.runway, [(SB.mouth, SB.arm)]]
          · have hlocal := manufactured_pair_within_eight_mul_switches_of_avoids
              hN (.flip FA) (.stay SB) state hA hB
                hAB (by trivial)
            have hc := hlocal.tongue_vector_count times hlive hnd'
            omega
          · have hcontact := contact_of_not_avoids_flip hAB
            have hlocal := manufactured_flip_then_stay_within_eight
              hN FA SB state hA hB hcontact
            have hc := hlocal.tongue_vector_count times hlive hnd'
            omega
      | flip FB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [FB.runway, FB.candy]
          · by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
                [FA.runway, FA.candy]
            · have hlocal := manufactured_pair_within_eight_mul_switches_of_avoids
                hN (.flip FA) (.flip FB) state hA hB hAB hBA
              have hc := hlocal.tongue_vector_count times hlive hnd'
              omega
            · have hcontactBA := contact_of_not_avoids_flip hBA
              have hArun := (FA.toSupported.run state hA)
              have hA' : PathGrooves [FA.runway, FA.candy]
                  (flipAt state FA.actionSwitch) := hArun.2
              have hB' : PathGrooves [FB.runway, FB.candy]
                  (flipAt state FA.actionSwitch) :=
                hB.after_avoiding_action hAB
              have hlocal :=
                manufactured_one_sided_theta_within_twelve_succ_two
                  hN FB FA (flipAt state FA.actionSwitch)
                    hB' hA' hcontactBA hAB
              have hlocal' : EventuallyPeriodicWithin w
                  (e, (ManufacturedReflector.flip FA).toSupported.action.apply state)
                  (12 * N + 2) := by
                simpa [ManufacturedReflector.toSupported,
                  ManufacturedFlipReflector.toSupported, LocalAction.apply]
                  using hlocal
              have hc := ManufacturedReflector.traversal_then_lasso_distinct_le_succ
                (ManufacturedReflector.flip FA) state hA hlocal'
                  times hlive hnd
              omega
          · have hcontactAB := contact_of_not_avoids_flip hAB
            by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
                [FA.runway, FA.candy]
            · have hlocal := manufactured_one_sided_theta_within_twelve_succ_two
                hN FA FB state hA hB hcontactAB hBA
              have hc := hlocal.tongue_vector_count times hlive hnd'
              omega
            · have hcontactBA := contact_of_not_avoids_flip hBA
              have hlocal := manufactured_two_sided_theta_within_twelve_succ_two
                hN FA FB state hA hB hcontactAB hcontactBA
              have hc := hlocal.tongue_vector_count times hlive hnd'
              omega

end GeneralN
