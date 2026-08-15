import TrackNoveltyCover

/-!
# The productive arbitrary-start boundary at `N+4`

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
end GeneralN
