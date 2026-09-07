import KnownEdgeNAddFourFrontier
import ChangedContactNAddFour

/-!
# Close the changed-contact arm of the known-edge `N+4` frontier

The sharp probe decomposition exposes two residuals.  This file eliminates
the changed-contact residual using the runway-retrace contradiction, leaving
only the protected pair.
-/

namespace GeneralN

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
  rcases C.direction with hbackward | hforward
  · have hsmall := C.backward_all_run_distinct_le_N_add_three
      hN hA hbackward times hlive hnd
    omega
  · cases A with
    | stay R =>
        let localTimes := times.map (fun k => k -
          ((ManufacturedReflector.stay R).exploration.length +
            (ManufacturedReflector.stay R).runway.length + 1))
        have hlocal := C.forward_stay_zero_novelty
          (N := N) hforward localTimes
        have hcount := C.changed_all_run_distinct_le_compressedLead_add_budget
          hA times hlive hnd (by simpa [localTimes] using hlocal)
        have hlength := C.compressedLead_length_le hN hA
        omega
    | flip R =>
        rcases C.changed_N_add_four_or_runway_residual
            hN hA times hlive hnd with hbound | hresidual
        · exact hbound
        · exact hresidual.elim fun F => (F.impossible hN hA).elim


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

end GeneralN
