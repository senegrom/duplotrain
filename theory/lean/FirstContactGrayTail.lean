import TwoHistoryUnionCharge
import StateLawTwoSharp
import ProtectedRepairFour

/-!
# First-contact continuation

The endpoint-groove-preserved branch does not need a recursive residual.
Switch simplicity makes every productive writer in the second exploration
survive to its pre-return endpoint.  Consequently every such writer is
outside the first reflector's reusable support, and the two sets of
coordinates are charged once.  `TwoHistoryUnionCharge` packages this as an
`N+3` construction history.  The uniform protected-repair theorem supplies
the four-corner tail; its initial corner is already in that history, so the
whole raw trajectory has at most `N+6` distinct tongue vectors.
-/

namespace GeneralN

/-- **Stable first-contact branch, raw all-times form.**

Suppose two opposite manufactured reflectors are traversed in sequence.  If
the first reflector's support is still grooved at the second reflector's
pre-return endpoint, then every pairwise-distinct family of restricted tongue
vectors sampled anywhere on the complete trajectory has size at most `N+6`.

There is no tail certificate in this statement.  The four-vector tail is the
unconditional `manufactured_pair_protected_repair_distinct_le_four`; the
coefficient-one prefix is discharged by the permanent-writer bridge in
`TwoHistoryUnionCharge`.
-/
theorem ManufacturedReflector.preReturn_grooved_all_run_distinct_le_N_add_six
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length <= N + 6 := by
  have hreachA := A.manufacturing_journey_reaches_activated hA
  have hreachB := B.manufacturing_journey_reaches_activated hB
  have hreachB' : stepN w
      (B.exploration.length + B.runway.length + 1)
      (e, A.activatedState) = some (g, B.activatedState) := by
    rw [← hbase]
    exact hreachB
  have hAatBase :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  have htail : forall tailTimes : List Nat,
      (forall k, List.Mem k tailTimes ->
        (stepN w k (g, B.activatedState)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup ->
      tailTimes.length <= 4 := by
    intro tailTimes htailLive htailNodup
    exact manufactured_pair_protected_repair_distinct_le_four
      A B hAatBase hB tailTimes htailLive htailNodup
  exact
    two_manufacturing_journeys_preserved_support_then_four_tail_le_N_add_six
      hN A B A.activatedState B.activatedState
      rfl rfl hreachA hA hbase rfl hreachB' hB hpre htail
      times hlive hnd

end GeneralN
