import CertifiedLobeAbsorption

/-!
# External-lobe reflector roundtrip

A lobe need not be mouth-paired directly with another lobe.  If a non-lobe
cell `c` has a lobe as its mouth partner, then entering `c` through a support
slot `s` has a simple effect:

1. the machine reads the lobe register and enters the opposite lobe endpoint;
2. that lobe writes itself;
3. reading `c`, which has just stored `s`, sends the walk across the same
   support edge to `bar s`.

Thus such a mouth pair acts as a reflector attached to the support vertex.
Two adjacent support vertices carrying these external reflectors make a
four-step roundtrip.  This is the local dynamical fact needed to reserve one
unpaired cell in every variable tree component and improve the component
exponent from `7/10` to `2/3`.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- One externally lobed support vertex reflects the walk across the edge by
which it entered. -/
theorem external_lobe_reflects
    (hrun : IsRun m e r0)
    {k s a : Nat}
    (hstart : e k = s)
    (haCell : m.cellOf a = m.star (m.cellOf s))
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (hregA : reg m e r0 k (m.star (m.cellOf s)) = a ∨
      reg m e r0 k (m.star (m.cellOf s)) = m.bar a) :
    (e (k+1) = m.bar a ∨ e (k+1) = a) ∧
      e (k+2) = m.bar s := by
  have hnext : e (k+1) = m.bar a ∨ e (k+1) = a := by
    rw [hrun k, hstart]
    rcases hregA with hregA | hregA
    · left
      rw [hregA]
    · right
      rw [hregA, m.bar_invol]
  have hnextCell :
      m.cellOf (e (k+1)) = m.star (m.cellOf s) := by
    rcases hnext with hnext | hnext
    · rw [hnext, haLobe, haCell]
    · rw [hnext, haCell]
  have hwrite : reg m e r0 k (m.cellOf s) = s := by
    calc
      reg m e r0 k (m.cellOf s) = e k := by
        apply reg_write m e r0
        rw [hstart]
      _ = s := hstart
  have hforeign :
      m.cellOf (e (k+1)) ≠ m.cellOf s := by
    intro h
    apply m.star_ne (m.cellOf s)
    exact hnextCell.symm.trans h
  have hkeep : reg m e r0 (k+1) (m.cellOf s) = s := by
    rw [reg_skip m e r0 hforeign, hwrite]
  constructor
  · exact hnext
  · calc
      e (k+2) = m.bar
          (reg m e r0 (k+1)
            (m.star (m.cellOf (e (k+1))))) := hrun (k+1)
      _ = m.bar (reg m e r0 (k+1) (m.cellOf s)) := by
            rw [hnextCell, m.star_invol]
      _ = m.bar s := by rw [hkeep]

/-- **External-reflector roundtrip.**  If both endpoints of a support edge
have lobe mouth partners, the walk returns to its original support endpoint
in four steps.  The two intervening lobe entries lie on the corresponding
lobe edges. -/
theorem external_lobe_roundtrip
    (hrun : IsRun m e r0)
    {k s a b : Nat}
    (hstart : e k = s)
    (haCell : m.cellOf a = m.star (m.cellOf s))
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (hbCell : m.cellOf b = m.star (m.cellOf (m.bar s)))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hregA : reg m e r0 k (m.star (m.cellOf s)) = a ∨
      reg m e r0 k (m.star (m.cellOf s)) = m.bar a)
    (hregB : reg m e r0 (k+2)
        (m.star (m.cellOf (m.bar s))) = b ∨
      reg m e r0 (k+2)
        (m.star (m.cellOf (m.bar s))) = m.bar b) :
    (e (k+1) = m.bar a ∨ e (k+1) = a) ∧
    e (k+2) = m.bar s ∧
    (e (k+3) = m.bar b ∨ e (k+3) = b) ∧
    e (k+4) = s := by
  have hfirst := external_lobe_reflects m e r0 hrun
    hstart haCell haLobe hregA
  have hsecond := external_lobe_reflects m e r0 hrun
    hfirst.2 hbCell hbLobe hregB
  exact ⟨hfirst.1, hfirst.2, hsecond.1, by
    simpa only [m.bar_invol] using hsecond.2⟩

/-- Occupancy of a lobe edge supplies exactly the register disjunction needed
by the reflector theorem. -/
theorem external_lobe_register_cases
    {k a c : Nat}
    (haCell : m.cellOf a = c)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (hocc : Occupied m e r0 k a) :
    reg m e r0 k c = a ∨ reg m e r0 k c = m.bar a := by
  have hcases := standalone_occupied_lobe_cases m e r0 haLobe hocc
  simpa [haCell] using hcases

/-- Occupied lobe partners at the two relevant read times give the fully
geometric roundtrip certificate. -/
theorem external_lobe_roundtrip_of_occupied
    (hrun : IsRun m e r0)
    {k s a b : Nat}
    (hstart : e k = s)
    (haCell : m.cellOf a = m.star (m.cellOf s))
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (hbCell : m.cellOf b = m.star (m.cellOf (m.bar s)))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (haOcc : Occupied m e r0 k a)
    (hbOcc : Occupied m e r0 (k+2) b) :
    (e (k+1) = m.bar a ∨ e (k+1) = a) ∧
    e (k+2) = m.bar s ∧
    (e (k+3) = m.bar b ∨ e (k+3) = b) ∧
    e (k+4) = s := by
  apply external_lobe_roundtrip m e r0 hrun
    hstart haCell haLobe hbCell hbLobe
  · exact external_lobe_register_cases m e r0
      haCell haLobe haOcc
  · exact external_lobe_register_cases m e r0
      hbCell hbLobe hbOcc

end Echo
