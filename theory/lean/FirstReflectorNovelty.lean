import TrackNoveltyCover

/-!
# Novelty of one manufactured-reflector activation

The first repeated switch in a switch-simple exploration manufactures either
a stay reflector or a flip reflector.  Its forced activation is not a second
long source of states: it is the contact step followed by the exact reverse of
the old runway.  Consequently the complete activation contributes at most one
new tongue vector, independently of the runway length.

This is a local raw-track theorem.  It does not claim the still-open global
`StateLaw`; the remaining global work is to combine the two manufactured
explorations and the protected-repair residual without charging overlapping
support twice.
-/

namespace GeneralN

/-- The runway is among the support paths retained by a manufactured
reflector, so a grooved support state grooves the runway itself. -/
theorem ManufacturedReflector.runway_grooved
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) {state : Tongues}
    (hpaths : PathGrooves A.toSupported.paths state) :
    PassagesGrooved state A.runway :=
  hpaths A.runway A.runway_mem_support

end GeneralN
