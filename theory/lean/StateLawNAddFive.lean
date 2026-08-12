import KnownEdgeNAddFourComplete
import ArbitraryStartDirectLift

/-!
# The state law at `N + 5`

`knownIncomingEdgeNAddFour` bounds every run whose incoming physical edge
is known by `N + 4`, unconditionally.  Shifting an arbitrary start past
its first successful step (`arbitrary_start_distinct_le_succ_of_all_known_edge`)
costs at most the time-zero vector.  Together: a single train on any
`N`-switch lazy-point layout visits at most `N + 5` distinct tongue
vectors — one above the proved `N + 4` lower bound
(`state_law_lower_bound`), superseding the `N + 6` form of `stateLaw`.
-/

namespace GeneralN

/-- **THE STATE LAW, AT `N + 5`.**  A single train on any `N`-switch
lazy-point layout visits at most `N + 5` distinct tongue vectors. -/
theorem state_law_N_add_five
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (c0 : Nat × Tongues) (ks : List Nat)
    (hlive : ∀ k ∈ ks, (stepN w k c0).isSome)
    (hnd : (ks.map fun k =>
      VectorCount.restrict N (tonguesAt w c0 k)).Nodup) :
    ks.length ≤ N + 5 := by
  change (ks.map (restrictedTonguesAt w N c0)).Nodup at hnd
  exact arbitrary_start_distinct_le_succ_of_all_known_edge
    (cap := N + 4) (knownIncomingEdgeNAddFour hN) c0 ks hlive hnd

/-- The historically stated `N + 6` target follows a fortiori. -/
theorem stateLaw_via_N_add_five : StateLaw := by
  intro w N hN c0 ks hlive hnd
  have h := state_law_N_add_five w N hN c0 ks hlive hnd
  omega

end GeneralN
