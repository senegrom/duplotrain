import BoundaryResidualSharpening
import KnownEdgeNAddFourComplete

/-!
# Sharp `N+4` state law

This file eliminates the saving residual isolated by
`BoundaryResidualSharpening` and closes the remaining arbitrary-start unit.
The known-incoming-edge theorem was already `N+4`; the result below proves
that the time-zero vector of a productive first passage is always historical.
-/

namespace GeneralN

/-- The productive arbitrary-start boundary fits the exact `N+4` budget. -/
theorem productiveInitialBoundaryNAddFour
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    ProductiveInitialBoundaryNAddFour w N := by
  unfold ProductiveInitialBoundaryNAddFour
  intro g e k0 original base hentry hstem hk0 hbase
    times hlive hnd
  rcases productive_initial_boundary_N_add_four_or_saving_saturation
      hN (knownIncomingEdgeNAddFour hN) hentry hstem hk0
        original base hbase times hlive hnd with hbound | hsaving
  · exact hbound
  · obtain ⟨S⟩ := hsaving
    exact (S.impossible hN).elim

/-- **Sharp state law.**  A single train on any finite `N`-switch lazy-point
layout visits at most `N+4` pairwise-distinct tongue vectors. -/
theorem state_law_N_add_four : StateLawNAddFour := by
  intro w N hN start times hlive hnd
  change (times.map (restrictedTonguesAt w N start)).Nodup at hnd
  exact
    arbitrary_start_distinct_le_N_add_four_of_known_edge_and_productive_boundary
      hN (knownIncomingEdgeNAddFour hN)
        (productiveInitialBoundaryNAddFour hN) start times hlive hnd

end GeneralN
