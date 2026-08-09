import ExternalLobeRoundtrip

/-!
# The external-reflector orbit

The local four-step roundtrip iterates as soon as the two lobe edges remain
occupied.  The resulting orbit is confined to six physical slots:

    support endpoint s,
    the two endpoints of the first lobe,
    support endpoint bar s,
    the two endpoints of the second lobe.

This is the external-lobe analogue of the four-slot dogbone absorption.  It is
exactly the obstruction needed to show that, before the first bounded tail,
a variable tree support component cannot have every cell mouth-paired to an
active lobe root.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Phase description of the external-reflector tail. -/
def ExternalReflectorTailFrom
    (k s a b : Nat) : Prop :=
  ∀ n,
    e (k + 4*n) = s ∧
    (e (k + 4*n + 1) = m.bar a ∨
      e (k + 4*n + 1) = a) ∧
    e (k + 4*n + 2) = m.bar s ∧
    (e (k + 4*n + 3) = m.bar b ∨
      e (k + 4*n + 3) = b)

/-- **External-reflector absorption.**  Persistent occupancy of the two lobe
edges makes the four-step roundtrip iterate forever. -/
theorem external_lobe_orbit_phases
    (hrun : IsRun m e r0)
    {k s a b : Nat}
    (hstart : e k = s)
    (haCell : m.cellOf a = m.star (m.cellOf s))
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (hbCell : m.cellOf b = m.star (m.cellOf (m.bar s)))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (haOcc : ∀ j, k ≤ j → Occupied m e r0 j a)
    (hbOcc : ∀ j, k ≤ j → Occupied m e r0 j b) :
    ExternalReflectorTailFrom m e r0 k s a b := by
  have hstarts : ∀ n, e (k + 4*n) = s := by
    intro n
    induction n with
    | zero => simpa using hstart
    | succ n ih =>
        let q := k + 4*n
        have hq : k ≤ q := by
          dsimp [q]
          omega
        have hround := external_lobe_roundtrip_of_occupied
          m e r0 hrun (k := q) (s := s) (a := a) (b := b)
          ih haCell haLobe hbCell hbLobe
          (haOcc q hq) (hbOcc (q+2) (by omega))
        have hret : e (q+4) = s := hround.2.2.2
        have hidx : q+4 = k + 4*(n+1) := by
          dsimp [q]
          omega
        rwa [hidx] at hret
  intro n
  let q := k + 4*n
  have hq : k ≤ q := by
    dsimp [q]
    omega
  have hround := external_lobe_roundtrip_of_occupied
    m e r0 hrun (k := q) (s := s) (a := a) (b := b)
    (hstarts n) haCell haLobe hbCell hbLobe
    (haOcc q hq) (hbOcc (q+2) (by omega))
  dsimp [q] at hround
  exact ⟨hstarts n, hround.1, hround.2.1,
    hround.2.2.1⟩

/-- A persistent pair of adjacent external lobe reflectors therefore supplies
an explicit bounded-tail certificate. -/
theorem external_lobe_orbit_certificate
    (hrun : IsRun m e r0)
    {k s a b : Nat}
    (hstart : e k = s)
    (haCell : m.cellOf a = m.star (m.cellOf s))
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (hbCell : m.cellOf b = m.star (m.cellOf (m.bar s)))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (haOcc : ∀ j, k ≤ j → Occupied m e r0 j a)
    (hbOcc : ∀ j, k ≤ j → Occupied m e r0 j b) :
    ∃ s a b, ExternalReflectorTailFrom m e r0 k s a b := by
  exact ⟨s, a, b,
    external_lobe_orbit_phases m e r0 hrun hstart
      haCell haLobe hbCell hbLobe haOcc hbOcc⟩

end Echo
