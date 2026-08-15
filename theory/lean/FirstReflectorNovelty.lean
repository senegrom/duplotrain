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

/-- The local return passage of either manufactured-reflector constructor
contacts the retained runway at its mouth and produces the advertised
activated state. -/
theorem ManufacturedReflector.return_arrive_mouth
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    arrive A.preReturn.2 A.preReturn.1 =
      (A.mouthConfig.1, A.activatedState) := by
  cases A with
  | flip R =>
      exact R.crossed
  | stay R =>
      obtain ⟨after, hhead⟩ := R.coreTrace.head_arrive.2
      have hsound := R.coreTrace.sound
      have hafter : after = R.returnState := by
        simp [stepN, step, hhead, R.selfLink] at hsound
        exact hsound
      have hback := arrive_back R.mouthState R.mouth
      rw [hhead, hafter] at hback
      exact hback

/-- The runway is among the support paths retained by a manufactured
reflector, so a grooved support state grooves the runway itself. -/
theorem ManufacturedReflector.runway_grooved
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) {state : Tongues}
    (hpaths : PathGrooves A.toSupported.paths state) :
    PassagesGrooved state A.runway :=
  hpaths A.runway A.runway_mem_support


