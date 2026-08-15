import TrackQuantitativeRouteSharp
import PairTongueCountFour
import TrackStayContactAllTime
import TwoJourneyTailCountSharp

/-!
# Every manufactured reflector pair costs at most four tongue vectors

The final travel-shaped pair cases are the intersecting stay/flip geometries.
`TrackStayContactAllTime` proves that each of those has only two absolute
phases.  Consequently every opposite manufactured pair has a flat four-vector
bound, and complete repair costs only one switch-simple route plus four.
-/

namespace GeneralN

/-- Every opposite manufactured reflector pair exposes at most four distinct
restricted tongue vectors, for arbitrary sample times. -/
theorem manufactured_pair_tongue_vector_count_four_all
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, state))).Nodup) :
    times.length ≤ 4 := by
  classical
  cases A with
  | stay SA =>
      cases B with
      | stay SB =>
          exact manufactured_pair_avoid_distinct_le_four
            (.stay SA) (.stay SB) state hA hB
              (by trivial) (by trivial) times hnd
      | flip FB =>
          change PathGrooves
            [SA.runway, [(SA.mouth, SA.arm)]] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
              [SA.runway, [(SA.mouth, SA.arm)]]
          · exact manufactured_pair_avoid_distinct_le_four
              (.stay SA) (.flip FB) state hA hB
                (by trivial) hBA times hnd
          · have hcontact := contact_of_not_avoids_flip hBA
            have hc := manufactured_stay_then_flip_contact_distinct_le_two
              SA FB state hA hB hcontact times hnd
            omega
  | flip FA =>
      cases B with
      | stay SB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves
            [SB.runway, [(SB.mouth, SB.arm)]] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [SB.runway, [(SB.mouth, SB.arm)]]
          · exact manufactured_pair_avoid_distinct_le_four
              (.flip FA) (.stay SB) state hA hB
                hAB (by trivial) times hnd
          · have hcontact := contact_of_not_avoids_flip hAB
            have hc := manufactured_flip_then_stay_distinct_le_two
              FA SB state hA hB hcontact times hnd
            omega
      | flip FB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          exact manufactured_flip_pair_distinct_le_four
            FA FB state hA hB times hnd

/-- The flat four-vector pair count is inherited by every reached suffix. -/
theorem manufactured_pair_reached_tongue_vector_count_four_all
    {w : Wiring} {N g e shift : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    {middle : Nat × Tongues}
    (hreach : stepN w shift (g, state) = some middle)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k middle).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N middle)).Nodup) :
    times.length ≤ 4 := by
  let lifted := times.map (fun k => shift + k)
  have hliftLive : ∀ j ∈ lifted,
      (stepN w j (g, state)).isSome := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
    have hkLive := hlive k hk
    rw [stepN_add, hreach]
    exact hkLive
  have hvector : lifted.map
      (restrictedTonguesAt w N (g, state)) =
      times.map (restrictedTonguesAt w N middle) := by
    dsimp [lifted]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hkLive := hlive k hk
    cases htail : stepN w k middle with
    | none =>
        rw [htail] at hkLive
        simp at hkLive
    | some finish =>
        have hshift := tonguesAt_add_of_reaches hreach ⟨finish, htail⟩
        unfold restrictedTonguesAt
        exact congrArg (VectorCount.restrict N) hshift
  have hliftNodup :
      (lifted.map (restrictedTonguesAt w N (g, state))).Nodup := by
    rw [hvector]
    exact hnd
  have hbound := manufactured_pair_tongue_vector_count_four_all
    A B state hA hB lifted hliftNodup
  simpa [lifted] using hbound

/-- Complete repair exposes at most `N+4` distinct restricted tongue vectors:
one switch-simple repair route followed by a flat four-vector pair tail. -/
theorem ManufacturedReflector.completed_route_with_pair_support_distinct_le_n_succ_four
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (base state finalState : Tongues)
    (hbasePaths : PathGrooves A.toSupported.paths base)
    (hrepair : PhysicalTrace w (g, state)
      (A.orientedRoute state)
      (A.orientedFinish state, finalState))
    (hAfinal : PathGrooves A.toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k (g, state)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, state))).Nodup) :
    times.length ≤ N + 4 := by
  obtain ⟨reference, _hreferencePaths, hroute, hfinish,
      hreferenceGrooved, _hguard⟩ :=
    A.current_route_reference base state hbasePaths
  have hfinalGrooved :
      PassagesGrooved finalState (A.orientedRoute state) :=
    hrepair.grooved_of_switchSimple (A.orientedRoute_simple state)
  have hfinalReferenceGrooved :
      PassagesGrooved finalState (A.orientedRoute reference) := by
    rw [hroute]
    exact hfinalGrooved
  have hreferenceGrooved' :
      PassagesGrooved reference (A.orientedRoute reference) := by
    rw [hroute]
    exact hreferenceGrooved
  have horiented := A.oriented_data_eq_of_route_grooved
    reference finalState hreferenceGrooved' hfinalReferenceGrooved
  have hrouteFinal := A.orientedRoute_trace finalState hAfinal
  have hrouteFinal' : PhysicalTrace w (g, finalState)
      (A.orientedRoute state)
      (A.orientedFinish state, finalState) := by
    rw [horiented.1, horiented.2, hroute, hfinish] at hrouteFinal
    exact hrouteFinal
  let L := (A.orientedRoute state).length
  let endpoint : Nat × Tongues := (A.orientedFinish state, finalState)
  have hrepairReach : stepN w L (g, state) = some endpoint := by
    simpa [L, endpoint] using hrepair.sound
  have hpairReach : stepN w L (g, finalState) = some endpoint := by
    simpa [L, endpoint] using hrouteFinal'.sound
  have hLLe : L ≤ N := by
    dsimp [L]
    exact hrepair.simple_length_le hN
      (A.orientedRoute_simple state)
  have htimesNodup : times.Nodup :=
    tailsharp_nodup_of_map_nodup
      (restrictedTonguesAt w N (g, state)) hnd
  let preTimes := times.filter (fun k => decide (k < L))
  let tailTimes := times.filter (fun k => decide (L ≤ k))
  let shifted := tailTimes.map (fun k => k - L)
  have hpreNodup : preTimes.Nodup := by
    dsimp [preTimes]
    exact nodup_filter_nat _ htimesNodup
  have hpreLt : ∀ k ∈ preTimes, k < L := by
    intro k hk
    exact of_decide_eq_true (List.mem_filter.mp hk).2
  have hpreBound : preTimes.length ≤ L :=
    nodup_nat_lt_length hpreNodup hpreLt
  have htailVector : shifted.map
      (restrictedTonguesAt w N endpoint) =
      tailTimes.map (restrictedTonguesAt w N (g, state)) := by
    dsimp [shifted]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hkGe : L ≤ k :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkEq : k = L + (k - L) := by omega
    have hkLive := hlive k hkTimes
    have hrun : stepN w k (g, state) =
        stepN w (k - L) endpoint := by
      rw [hkEq, stepN_add, hrepairReach]
      simp
    cases htailRun : stepN w (k - L) endpoint with
    | none =>
        rw [hrun, htailRun] at hkLive
        simp at hkLive
    | some finish =>
        have hglobal : stepN w k (g, state) = some finish := by
          rw [hrun, htailRun]
        simp [Function.comp_apply, restrictedTonguesAt, tonguesAt,
          hglobal, htailRun]
  have htailNodup :
      (tailTimes.map (restrictedTonguesAt w N (g, state))).Nodup := by
    dsimp [tailTimes]
    exact tailsharp_nodup_map_filter _ hnd
  have hshiftedNodup :
      (shifted.map (restrictedTonguesAt w N endpoint)).Nodup := by
    rw [htailVector]
    exact htailNodup
  have hshiftedLive : ∀ d ∈ shifted,
      (stepN w d endpoint).isSome := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkGe : L ≤ k :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    have hkEq : k = L + (k - L) := by omega
    have hkLive := hlive k hkTimes
    rw [hkEq, stepN_add, hrepairReach] at hkLive
    exact hkLive
  have htailBound : shifted.length ≤ 4 :=
    manufactured_pair_reached_tongue_vector_count_four_all
      A B finalState hAfinal hBfinal hpairReach shifted
        hshiftedLive hshiftedNodup
  have htailLength : tailTimes.length = shifted.length := by
    simp [shifted]
  have hpartition := tailsharp_lt_ge_partition L times
  dsimp [preTimes, tailTimes] at hpartition hpreBound htailLength
  omega

end GeneralN
