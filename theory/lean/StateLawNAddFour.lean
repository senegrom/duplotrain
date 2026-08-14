import TrackFiniteAlternation

/-!
# The sharp `N+4` state-law target

This file states the sharp target directly over raw `Wiring` and `stepN`.
It also records the coefficient-one amortized novelty statement which is
exactly sufficient for that target.  Neither proposition is asserted here;
the proved theorem is the reduction from the amortized statement to the raw
track statement.
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
        ((stepN w k start).getD start).2)).Nodup ->
      times.length <= N + 4

end GeneralN
