import GeneralN

/-!
# Restricted tongue vectors

The counting language of the state law: `VectorCount.restrict N u` reads
the positions of the first `N` tongues as a boolean list, and `tonguesAt`
reads the tongue vector at time `k` of a run.  The law itself is stated
and proved in `StateLaw.lean`.
-/

namespace VectorCount

open GeneralN (Tongues)

/-- The tongue vector restricted to the first `N` switches. -/
def restrict (N : Nat) (u : Tongues) : List Bool :=
  (List.range N).map u

end VectorCount

namespace GeneralN

/-- The tongue vector at time `k` of the run from `c0`. -/
def tonguesAt (w : Wiring) (c0 : Nat × Tongues) (k : Nat) : Tongues :=
  ((stepN w k c0).getD c0).2


end GeneralN
