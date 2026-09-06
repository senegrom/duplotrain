import TrackNoveltyCover

/-!
# State-count targets independent of the upper-bound proof

Keep these statements below both the current proof and the retained
shifted-start proof, so stating the theorem does not import that old proof.
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

end GeneralN
