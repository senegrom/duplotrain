import KnownEdgeNAddFourFrontier
import ChangedContactNAddFour

/-!
# Close the changed-contact arm of the known-edge `N+4` frontier

The sharp probe decomposition exposes two residuals.  This file eliminates
the changed-contact residual using the runway-retrace contradiction, leaving
only the protected pair.
-/

namespace GeneralN

/-- Lift a local novelty cover after the first manufacturing journey to the
complete run.  Kept here so this closure does not depend on the still-moving
partial-second-run frontier file.  Public: the boundary-saving layer reuses
it from a separate file. -/
theorem changedContact_local_novelty_count
    {w : Wiring} {N g e budget : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup)
    (hlocal : NoveltyCoverOn w N (e, A.activatedState)
      (times.map (fun k => k -
        (A.exploration.length + A.runway.length + 1)))
      (C.history N) budget) :
    times.length <= N + 3 + budget := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localTimes := times.map (fun k => k - firstTravel)
  have hreach : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hlocal' : NoveltyCoverOn w N (e, A.activatedState)
      localTimes (C.history N) budget := by
    simpa [localTimes, firstTravel] using hlocal
  obtain ⟨fresh, hfresh, hlocalMem⟩ := hlocal'
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times (C.history N) budget := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hfirst : k <= firstTravel
    · apply List.mem_append_left
      unfold PartialSecondRunSharp.ChangedContact.history
      apply List.mem_append_left
      unfold ManufacturedReflector.continuationHistory
      apply List.mem_append_left
      apply A.mem_sharpHistoryCore_of_mem
      exact A.manufacturing_journey_mem_sharpHistory hA (by
        simpa [firstTravel] using hfirst)
    · let d := k - firstTravel
      have hdMem : d ∈ localTimes := by
        dsimp [d, localTimes]
        exact List.mem_map.mpr ⟨k, hk, rfl⟩
      have hm := hlocalMem d hdMem
      have hshift := restrictedTonguesAt_sub_of_reach
        (N := N) hreach (by omega) (hlive k hk)
      rw [hshift]
      exact hm
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistory := C.history_length_le_N_add_three hN hA
  omega

/-- Every sharp changed contact is bounded by `N+4`.  Backward contacts and
stay-reflector contacts already have zero local novelty; the flip-reflector
case is exactly the runway-retrace theorem. -/
theorem PartialSecondRunSharp.ChangedContact.all_run_distinct_le_N_add_four
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length <= N + 4 := by
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · have hsmall := C.backward_all_run_distinct_le_N_add_three
      hN hA hbackward times hlive hnd
    omega
  · cases A with
    | stay R =>
        let localTimes := times.map (fun k => k -
          ((ManufacturedReflector.stay R).exploration.length +
            (ManufacturedReflector.stay R).runway.length + 1))
        have hlocal := C.forward_stay_all_time_zero_novelty
          (N := N) hforward hrepair hrestored localTimes
        have hbound := changedContact_local_novelty_count
          hN C hA times hlive hnd hlocal
        omega
    | flip R =>
        exact C.changed_all_run_distinct_le_N_add_four
          hN hA times hlive hnd

/-- A literal changed-contact residual from the known-edge decomposition is
therefore closed at `N+4`. -/
theorem KnownEdgeChangedContact.all_run_distinct_le_N_add_four
    {w : Wiring} {N e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {start : Nat × Tongues}
    (D : KnownEdgeChangedContact w e start)
    (times : List Nat)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= N + 4 := by
  have hliveA : forall k, k ∈ times ->
      (stepN w k (start.1, D.A.baseState)).isSome := by
    simpa [D.base] using hlive
  have hndA : (times.map
      (restrictedTonguesAt w N
        (start.1, D.A.baseState))).Nodup := by
    simpa [D.base] using hnd
  exact D.contact.all_run_distinct_le_N_add_four
    hN D.grooves times hliveA hndA

/-- **Known-edge `N+4`, with one exact residual.**  The changed-contact arm
is closed; a reached support-protected opposite-reflector pair is the sole
remaining branch. -/
theorem known_edge_N_add_four_or_protected_pair
    {w : Wiring} {N e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= N + 4 ∨
      Nonempty (KnownEdgeProtectedPair w e start) := by
  rcases known_edge_N_add_four_or_changed_contact_or_protected_pair
      hN hentry times hlive hnd with hsmall | hchanged | hpair
  · exact Or.inl hsmall
  · obtain ⟨D⟩ := hchanged
    exact Or.inl (D.all_run_distinct_le_N_add_four
      hN times hlive hnd)
  · exact Or.inr hpair

/-- The genuinely protected pair residual: the first reflector's support is
still grooved at the second reflector's pre-return state. -/
structure KnownEdgeFullyProtectedPair
    (w : Wiring) (e : Nat) (start : Nat × Tongues) : Type where
  pair : KnownEdgeProtectedPair w e start
  preGrooves : PathGrooves pair.A.toSupported.paths pair.B.preReturn.2


def KnownEdgeProtectedPairNAddFourLaw : Prop :=
  forall {w : Wiring} {N e : Nat},
    (forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) ->
    forall {start : Nat × Tongues},
      KnownEdgeProtectedPair w e start ->
      forall times : List Nat,
        (forall k, k ∈ times -> (stepN w k start).isSome) ->
        (times.map
          (restrictedTonguesAt w N start)).Nodup ->
        times.length <= N + 4

/-- Closing the protected-pair law closes the entire known-edge `N+4`
theorem; the changed-contact branch has no remaining hypothesis. -/
theorem known_edge_all_run_distinct_le_N_add_four_of_protected_pair
    (hpairLaw : KnownEdgeProtectedPairNAddFourLaw)
    {w : Wiring} {N e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= N + 4 := by
  rcases known_edge_N_add_four_or_protected_pair
      hN hentry times hlive hnd with hsmall | hpair
  · exact hsmall
  · exact hpairLaw hN (Classical.choice hpair) times hlive hnd

end GeneralN
