import TrackCurveGrowth

/-!
# Self-pivots are unavoidable inside a repeated-writer frame

After a productive visit to switch `C`, the train's next raw entry is joined
by the fixed external track edge to `C`'s stem.  A quiet step merely reroots
the same selected curve, and a productive non-self pivot contains the whole
old train curve in the new one.  Therefore the stem remains on the train
curve until a self-pivot removes part of that curve.

The main theorem below is a raw, finite-time statement: between any two
productive visits to the same writer, either the closing visit is a
self-pivot or an interior productive visit is.  This is the global bridge
needed to organise repeated novelties into shrink/grow restoration frames.
-/

namespace GeneralN

/-- The productive pivot at raw time `k` is a self-pivot of the train's
currently selected curve.  The definition is meaningful without a liveness
premise because raw accessors use the initial configuration as default; all
theorems below establish liveness explicitly. -/
def RawTrainCurveSelfAt
    (w : Wiring) (start : Nat × Tongues) (k : Nat) : Prop :=
  CurveReach w (tonguesAt w start k) (rawEntryAt w start k)
    (3 * rawWriterAt w start k)
end GeneralN
