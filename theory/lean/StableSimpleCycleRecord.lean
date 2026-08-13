import TrackTrace

/-!
# A reached stable switch-simple cycle, as raw data

The record a second-probe cycle settlement hands to the boundary
dichotomy: the transient lap and the stable lap with their traces.
Extracted so the dichotomy does not depend on the Mellit trace-retaining
programme that originally produced it.
-/

namespace GeneralN

structure ReachedStableSimpleCycle
    (w : Wiring) (start : Nat × Tongues) : Type where
  shift : Nat
  atRepeat : Nat × Tongues
  cycle : List Passage
  settled : Tongues
  reached : stepN w shift start = some atRepeat
  nonempty : cycle ≠ []
  transient : PhysicalTrace w atRepeat cycle (atRepeat.1, settled)
  stable : PhysicalTrace w (atRepeat.1, settled) cycle
    (atRepeat.1, settled)
  simple : SwitchSimple cycle

end GeneralN
