import PersistentLobeSeparationStandalone

/-!
# An occupied lobe forces a two-step partner bounce

This is the local dynamical mechanism needed to control how many varying lobe
roots one ordinary support-tree component can steer.

If the current entry lies in the mouth partner of a cell carrying an occupied
lobe, the next step must enter one endpoint of that lobe.  The following step
then reads back the current entry from the untouched partner register and
jumps to its `bar` endpoint.  Thus the cell-level excursion is forced and the
slot sequence satisfies

    e (k+2) = bar (e k).

No fixed-support or periodicity hypothesis is needed.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Occupied-lobe partner bounce.** -/
theorem occupied_lobe_partner_bounce
    (hrun : IsRun m e r0)
    {k a : Nat}
    (hlobe : m.cellOf (m.bar a) = m.cellOf a)
    (hpartner : m.cellOf (e k) = m.star (m.cellOf a))
    (hocc : Occupied m e r0 k a) :
    m.cellOf (e (k+1)) = m.cellOf a ∧
      e (k+2) = m.bar (e k) := by
  have hreadCell :
      m.star (m.cellOf (e k)) = m.cellOf a := by
    rw [hpartner, m.star_invol]
  have hstep := hrun k
  rw [hreadCell] at hstep
  have hregCases := standalone_occupied_lobe_cases m e r0 hlobe hocc
  have hnext : e (k+1) = m.bar a ∨ e (k+1) = a := by
    rcases hregCases with ha | hb
    · left
      rw [ha] at hstep
      exact hstep
    · right
      rw [hb, m.bar_invol] at hstep
      exact hstep
  have hnextCell : m.cellOf (e (k+1)) = m.cellOf a := by
    rcases hnext with h | h
    · rw [h, hlobe]
    · rw [h]
  have hdifferent :
      m.cellOf (e (k+1)) ≠ m.cellOf (e k) := by
    rw [hnextCell, hpartner]
    exact (m.star_ne (m.cellOf a)).symm
  have hskip :
      reg m e r0 (k+1) (m.cellOf (e k)) =
        reg m e r0 k (m.cellOf (e k)) :=
    reg_skip m e r0 hdifferent
  have hcurrent :
      reg m e r0 k (m.cellOf (e k)) = e k :=
    reg_write m e r0 rfl
  have hstored :
      reg m e r0 (k+1) (m.cellOf (e k)) = e k :=
    hskip.trans hcurrent
  have hreadBack :
      m.star (m.cellOf (e (k+1))) = m.cellOf (e k) := by
    rw [hnextCell]
    exact hpartner.symm
  have hstep2 := hrun (k+1)
  rw [hreadBack, hstored] at hstep2
  constructor
  · exact hnextCell
  · simpa [Nat.add_assoc] using hstep2

end Echo
