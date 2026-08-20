import StateLawTwoSixUltra

/-!
# Exact top-level lift for the `N+4` state law

This file isolates the final arbitrary-start bookkeeping.  It assumes exactly
the two physical inputs needed by that bookkeeping:

* every run whose incoming edge is already known has at most `N+4` distinct
  restricted tongue vectors; and
* a productive first passage satisfies `ProductiveInitialBoundaryNAddFour`.

Under those assumptions the raw arbitrary-start statement
`StateLawNAddFour` follows with no additional state charged at time zero.
-/

namespace GeneralN

/-- **THE SHARP STATE-LAW TARGET.**  A single train on any raw lazy-point
wiring with `N` switches visits at most `N+4` pairwise-distinct restricted
tongue vectors. -/
def StateLawNAddFour : Prop :=
  forall (w : Wiring) (N : Nat),
    (forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) ->
    forall (start : Nat × Tongues) (times : List Nat),
      (forall k, k ∈ times -> (stepN w k start).isSome) ->
      (times.map (fun k => VectorCount.restrict N
        (tonguesAt w start k))).Nodup ->
      times.length <= N + 4


/-- The exact productive arbitrary-start boundary target needed by the raw
`N+4` state law. -/
def ProductiveInitialBoundaryNAddFour (w : Wiring) (N : Nat) : Prop :=
  forall {g e k0 : Nat} {original base : Tongues},
    w.link e = some g ->
    e = 3 * k0 ->
    k0 < N ->
    base = flipAt original k0 ->
    forall times : List Nat,
      (forall k, k ∈ times ->
        (stepN w k (g, base)).isSome) ->
      (VectorCount.restrict N original ::
        times.map (restrictedTonguesAt w N (g, base))).Nodup ->
      times.length + 1 <= N + 4


/-- The exact `N+4` hypothesis for a run whose incoming edge is known. -/
def KnownIncomingEdgeNAddFour (w : Wiring) (N : Nat) : Prop :=
  forall {e : Nat} {localStart : Nat × Tongues},
    w.link e = some localStart.1 ->
    forall localTimes : List Nat,
      (forall k, k ∈ localTimes ->
        (stepN w k localStart).isSome) ->
      (localTimes.map
        (restrictedTonguesAt w N localStart)).Nodup ->
      localTimes.length <= N + 4

/-- Exact arbitrary-start lift.  A quiet first passage is absorbed into the
known-edge run by adjoining its time zero.  A productive first passage is
handled by `ProductiveInitialBoundaryNAddFour`, which counts the original
time-zero vector together with the shifted known-edge samples. -/
theorem arbitrary_start_distinct_le_N_add_four_of_known_edge_and_productive_boundary
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (hknown : KnownIncomingEdgeNAddFour w N)
    (hproductive : ProductiveInitialBoundaryNAddFour w N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= N + 4 := by
  rcases start with ⟨startPort, startState⟩
  have htimesNodup : times.Nodup :=
    sample_times_nodup_of_map_nodup
      (restrictedTonguesAt w N (startPort, startState)) hnd
  rcases harrive : arrive startState startPort with ⟨localPort, localState⟩
  cases hlink : w.link localPort with
  | none =>
      have hone : stepN w 1 (startPort, startState) = none := by
        simp [stepN, step, harrive, hlink]
      have hlen : times.length <= 1 :=
        nodup_nat_lt_length htimesNodup (by
          intro k hk
          by_cases hk0 : k = 0
          · omega
          · have hkLive := hlive k hk
            rw [stepN_none_of_none_at_le hone (by omega)] at hkLive
            simp at hkLive)
      omega
  | some entry =>
      have hone : stepN w 1 (startPort, startState) =
          some (entry, localState) := by
        simp [stepN, step, harrive, hlink]
      let positive := times.erase 0
      let shifted := positive.map (fun k => k - 1)
      have hshiftVector : shifted.map
            (restrictedTonguesAt w N (entry, localState)) =
          positive.map
            (restrictedTonguesAt w N (startPort, startState)) := by
        dsimp [shifted]
        rw [List.map_map]
        apply List.map_congr_left
        intro k hk
        have hkData := (htimesNodup.mem_erase_iff).mp hk
        have hkPos : 0 < k := by omega
        simpa [Function.comp_apply] using
          (restrictedTonguesAt_sub_of_reach
            (N := N) hone (by omega) (hlive k hkData.2)).symm
      have hshiftedNodup :
          (shifted.map
            (restrictedTonguesAt w N (entry, localState))).Nodup := by
        rw [hshiftVector]
        dsimp [positive]
        exact (List.erase_sublist.map _).nodup hnd
      have hshiftedLive : forall d, d ∈ shifted ->
          (stepN w d (entry, localState)).isSome := by
        intro d hd
        obtain ⟨k, hk, hkd⟩ := List.mem_map.mp hd
        have hkData := (htimesNodup.mem_erase_iff).mp hk
        have hkPos : 0 < k := by omega
        have hkLive := hlive k hkData.2
        rw [show k = 1 + (k - 1) by omega,
          stepN_add, hone] at hkLive
        simpa [hkd] using hkLive
      by_cases hzero : 0 ∈ times
      · have htimesLength : shifted.length + 1 = times.length := by
          simpa [shifted, positive, Nat.add_comm] using
            (List.perm_cons_erase hzero).length_eq.symm
        have haugmentedNodup :
            (VectorCount.restrict N startState ::
              shifted.map (restrictedTonguesAt w N
                (entry, localState))).Nodup := by
          rw [hshiftVector]
          simpa [positive, restrictedTonguesAt, tonguesAt, stepN] using
            hnd.perm ((List.perm_cons_erase hzero).map
              (restrictedTonguesAt w N (startPort, startState)))
        by_cases hsame : localState = startState
        · let augmented := 0 :: shifted
          have haugmentedLive : forall d, d ∈ augmented ->
              (stepN w d (entry, localState)).isSome := by
            intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · simp [stepN]
            · exact hshiftedLive d hd
          have haugmentedLocalNodup :
              (augmented.map (restrictedTonguesAt w N
                (entry, localState))).Nodup := by
            simpa [augmented, restrictedTonguesAt, tonguesAt,
              stepN, hsame] using haugmentedNodup
          have hbound := hknown
            (e := localPort)
            (localStart := (entry, localState))
            hlink augmented haugmentedLive haugmentedLocalNodup
          have hlength : augmented.length = shifted.length + 1 := by
            simp [augmented]
          omega
        · let k0 := startPort / 3
          have hchanged : localState k0 ≠ startState k0 := by
            intro heq
            apply hsame
            funext j
            by_cases hj : j = k0
            · subst j
              exact heq
            · exact arrive_preserves_other harrive hj
          have htrailing := changed_arrival_is_trailing
            harrive hchanged
          have he : localPort = 3 * k0 := htrailing.2.1
          have hk0 : k0 < N := by
            have hp := (hN localPort entry hlink).1
            dsimp [k0] at he
            omega
          have hbaseShift : localState = flipAt startState k0 :=
            changed_arrival_eq_flipAt harrive hchanged
          have hbound := hproductive hlink he hk0 hbaseShift
            shifted hshiftedLive haugmentedNodup
          omega
      · have htimesLength : shifted.length = times.length := by
          simpa [shifted, positive] using congrArg List.length
            (List.erase_of_not_mem hzero)
        have hbound := hknown
          (e := localPort)
          (localStart := (entry, localState))
          hlink shifted hshiftedLive hshiftedNodup
        omega

end GeneralN
