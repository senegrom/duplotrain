import TrackFiniteAlternation
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


/-!
## The productive arbitrary-start boundary at `N+4`

The exact raw boundary target is the `N+4` analogue of
`ProductiveInitialBoundaryCap`.  This file closes the branch in which the
initially written switch is a productive first writer of the second
manufactured reflector and the resulting return prefix closes a stable
simple cycle.

The complementary branch is retained as a literal support-contact
certificate: a passage of the old switch-simple lead and a passage of the
returned prefix name the same switch.  No counting conclusion about that
contact is assumed here.
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


private theorem top_nodup_map_eq_of_mem
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) {xs : List alpha}
    (hnd : (xs.map f).Nodup) {a b : alpha}
    (ha : a ∈ xs) (hb : b ∈ xs) (heq : f a = f b) : a = b := by
  induction xs generalizing a b with
  | nil => cases ha
  | cons x rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp ha with ha | ha
      · rcases List.mem_cons.mp hb with hb | hb
        · subst a
          subst b
          rfl
        · subst a
          exfalso
          apply hnd.1
          exact List.mem_map.mpr ⟨b, hb, heq.symm⟩
      · rcases List.mem_cons.mp hb with hb | hb
        · subst b
          exfalso
          apply hnd.1
          exact List.mem_map.mpr ⟨a, ha, heq⟩
        · exact ih hnd.2 ha hb heq

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
  cases hone : stepN w 1 (startPort, startState) with
  | none =>
      have hzero : forall k, k ∈ times -> k = 0 := by
        intro k hk
        by_cases hk0 : k = 0
        · exact hk0
        · have hkPos : 0 < k := by omega
          have hkEq : k = 1 + (k - 1) := by omega
          have hnone : stepN w k (startPort, startState) = none := by
            rw [hkEq, stepN_add, hone]
            simp
          have hkLive := hlive k hk
          simp [hnone] at hkLive
      have hlen : times.length <= 1 :=
        nodup_nat_lt_length htimesNodup (by
          intro k hk
          have hk0 := hzero k hk
          omega)
      omega
  | some middle =>
      have honeStep : stepN w 1 (startPort, startState) = some middle :=
        hone
      simp only [stepN, step] at hone
      let localStep := arrive startState startPort
      cases hlink : w.link localStep.1 with
      | none =>
          simp [localStep, hlink] at hone
      | some entry =>
          have hmiddle : middle = (entry, localStep.2) := by
            simpa [localStep, hlink] using hone.symm
          subst middle
          let positive := times.filter (fun k => decide (0 < k))
          let shifted := positive.map (fun k => k - 1)
          let zeroTimes := times.filter (fun k => decide (k = 0))
          have hshiftVector : shifted.map
                (restrictedTonguesAt w N (entry, localStep.2)) =
              positive.map
                (restrictedTonguesAt w N (startPort, startState)) := by
            dsimp [shifted]
            rw [List.map_map]
            apply List.map_congr_left
            intro k hk
            have hkPos : 0 < k :=
              of_decide_eq_true (List.mem_filter.mp hk).2
            have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
            have hkEq : k = 1 + (k - 1) := by omega
            have hkLive := hlive k hkTimes
            have hrun : stepN w k (startPort, startState) =
                stepN w (k - 1) (entry, localStep.2) := by
              rw [hkEq, stepN_add, honeStep]
              simp
            cases htail : stepN w (k - 1) (entry, localStep.2) with
            | none =>
                rw [hrun, htail] at hkLive
                simp at hkLive
            | some finish =>
                have hglobal : stepN w k (startPort, startState) =
                    some finish := by rw [hrun, htail]
                simp [Function.comp_apply, restrictedTonguesAt,
                  tonguesAt, hglobal, htail]
          have hpositiveNodup :
              (positive.map
                (restrictedTonguesAt w N
                  (startPort, startState))).Nodup := by
            dsimp [positive]
            exact tailsharp_nodup_map_filter _ hnd
          have hshiftedNodup :
              (shifted.map
                (restrictedTonguesAt w N
                  (entry, localStep.2))).Nodup := by
            rw [hshiftVector]
            exact hpositiveNodup
          have hshiftedLive : forall d, d ∈ shifted ->
              (stepN w d (entry, localStep.2)).isSome := by
            intro d hd
            obtain ⟨k, hk, hkd⟩ := List.mem_map.mp hd
            have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
            have hkPos : 0 < k :=
              of_decide_eq_true (List.mem_filter.mp hk).2
            have hkEq : k = 1 + (k - 1) := by omega
            have hkLive := hlive k hkTimes
            rw [hkEq, stepN_add, honeStep] at hkLive
            have hlocal :
                (stepN w (k - 1) (entry, localStep.2)).isSome := by
              simpa using hkLive
            simpa [hkd] using hlocal
          have hpositiveLength : positive.length = shifted.length := by
            simp [shifted]
          have hzeroBound : zeroTimes.length <= 1 := by
            dsimp [zeroTimes]
            exact kel_zero_filter_length_le_one htimesNodup
          have hpartition : zeroTimes.length + positive.length =
              times.length := by
            simpa [zeroTimes, positive] using
              kel_zero_positive_partition times
          by_cases hzero : 0 ∈ times
          · have hzeroMem : 0 ∈ zeroTimes := by
              dsimp [zeroTimes]
              exact List.mem_filter.mpr ⟨hzero, decide_eq_true rfl⟩
            have hzeroLengthNe : zeroTimes.length ≠ 0 := by
              intro hlen
              cases hz : zeroTimes with
              | nil => rw [hz] at hzeroMem; cases hzeroMem
              | cons z rest => simp [hz] at hlen
            have hzeroLength : zeroTimes.length = 1 := by omega
            have hzeroVector :
                restrictedTonguesAt w N (startPort, startState) 0 =
                  VectorCount.restrict N startState := by
              simp [restrictedTonguesAt, tonguesAt, stepN]
            have haugmentedNodup :
                (VectorCount.restrict N startState ::
                  shifted.map (restrictedTonguesAt w N
                    (entry, localStep.2))).Nodup := by
              rw [List.nodup_cons]
              constructor
              · intro hm
                rw [hshiftVector] at hm
                obtain ⟨k, hk, heq⟩ := List.mem_map.mp hm
                have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
                have heq' : restrictedTonguesAt w N
                    (startPort, startState) 0 =
                    restrictedTonguesAt w N
                      (startPort, startState) k :=
                  hzeroVector.trans heq.symm
                have htimeEq := top_nodup_map_eq_of_mem
                  (restrictedTonguesAt w N (startPort, startState))
                  hnd hzero hkTimes heq'
                have hkPos : 0 < k :=
                  of_decide_eq_true (List.mem_filter.mp hk).2
                omega
              · exact hshiftedNodup
            by_cases hsame : localStep.2 = startState
            · let augmented := 0 :: shifted
              have haugmentedLive : forall d, d ∈ augmented ->
                  (stepN w d (entry, localStep.2)).isSome := by
                intro d hd
                rcases List.mem_cons.mp hd with rfl | hd
                · simp [stepN]
                · exact hshiftedLive d hd
              have hlocalZero : restrictedTonguesAt w N
                    (entry, localStep.2) 0 =
                  VectorCount.restrict N startState := by
                simp [restrictedTonguesAt, tonguesAt, stepN, hsame]
              have haugmentedLocalNodup :
                  (augmented.map (restrictedTonguesAt w N
                    (entry, localStep.2))).Nodup := by
                dsimp [augmented]
                rw [hlocalZero]
                exact haugmentedNodup
              have hbound := hknown
                (e := localStep.1)
                (localStart := (entry, localStep.2))
                hlink augmented haugmentedLive haugmentedLocalNodup
              have hlength : augmented.length = shifted.length + 1 := by
                simp [augmented]
              omega
            · let k0 := startPort / 3
              have harrive : arrive startState startPort =
                  (localStep.1, localStep.2) := by simp [localStep]
              have hchanged : localStep.2 k0 ≠ startState k0 := by
                intro heq
                apply hsame
                funext j
                by_cases hj : j = k0
                · subst j
                  exact heq
                · exact arrive_preserves_other harrive hj
              have htrailing := changed_arrival_is_trailing
                harrive hchanged
              have he : localStep.1 = 3 * k0 := htrailing.2.1
              have hk0 : k0 < N := by
                have hp := (hN localStep.1 entry hlink).1
                dsimp [k0] at he
                omega
              have hbaseShift : localStep.2 =
                  flipAt startState k0 :=
                changed_arrival_eq_flipAt harrive hchanged
              have hbound := hproductive hlink he hk0 hbaseShift
                shifted hshiftedLive haugmentedNodup
              omega
          · have hzeroLength : zeroTimes.length = 0 := by
              cases hz : zeroTimes with
              | nil => simp
              | cons z rest =>
                  have hzmem : z ∈ zeroTimes := by
                    rw [hz]
                    exact List.mem_cons_self
                  have hzdata := List.mem_filter.mp hzmem
                  have hz0 : z = 0 := of_decide_eq_true hzdata.2
                  subst z
                  exact (hzero hzdata.1).elim
            have hbound := hknown
              (e := localStep.1)
              (localStart := (entry, localStep.2))
              hlink shifted hshiftedLive hshiftedNodup
            omega

/-- **Top-level exact wrapper.**  If the two stated `N+4` obligations hold
for every finite raw wiring, then the sharp raw state law holds. -/
theorem stateLawNAddFour_of_known_edge_and_productive_boundary
    (hknown : forall (w : Wiring) (N : Nat),
      (forall p q, w.link p = some q ->
        p < 3 * N ∧ q < 3 * N) ->
      KnownIncomingEdgeNAddFour w N)
    (hproductive : forall (w : Wiring) (N : Nat),
      (forall p q, w.link p = some q ->
        p < 3 * N ∧ q < 3 * N) ->
      ProductiveInitialBoundaryNAddFour w N) :
    StateLawNAddFour := by
  intro w N hN start times hlive hnd
  change (times.map (restrictedTonguesAt w N start)).Nodup at hnd
  exact
    arbitrary_start_distinct_le_N_add_four_of_known_edge_and_productive_boundary
      hN (hknown w N hN) (hproductive w N hN)
        start times hlive hnd

end GeneralN
