import ProtectedPairNAddFour
import StateLawNAddFourTop

/-!
# The unconditional known-incoming-edge `N + 4` theorem

The changed-contact branch was already closed in
`KnownEdgeNAddFourChangedClosed`.  `ProtectedPairNAddFour` closes the only
remaining fully protected pair.  This file packages those two physical cases
as the exact raw hypothesis expected by the top-level arbitrary-start lift.
-/

namespace GeneralN

/-- A train whose incoming track edge is known visits at most `N + 4`
pairwise-distinct restricted tongue vectors.  This is unconditional over raw
finite lazy-point wirings. -/
theorem knownIncomingEdgeNAddFour
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    KnownIncomingEdgeNAddFour w N := by
  intro e start hentry times hlive hnd
  exact known_edge_all_run_distinct_le_N_add_four_of_protected_pair
    knownEdgeProtectedPairNAddFourLaw hN hentry times hlive hnd

end GeneralN
