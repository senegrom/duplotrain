import TrackNoveltyCover

/-!
# State-count targets independent of the upper-bound proof

The reusable upper-bound statement depends only on the raw model and vector
counting interface.
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


end GeneralN
