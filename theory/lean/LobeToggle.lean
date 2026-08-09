import LobePartnerBounce

/-!
# Occupied lobes are parity counters for partner-cell visits

An occupied lobe has only two possible register values.  Whenever its mouth
partner is entered, the next echo step enters the opposite lobe endpoint and
therefore toggles the register.  Conversely, an entry through either lobe
endpoint has the mouth-partner cell as its forced predecessor.

These identities turn each active lobe bit into a visit-parity bit of its
partner support component.  They are the coupling needed to improve on the
independent-bit `7/10` estimate.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A partner visit enters one of the two endpoints of an occupied lobe. -/
theorem occupied_lobe_partner_next_endpoint
    (hrun : IsRun m e r0)
    {k a : Nat}
    (hlobe : m.cellOf (m.bar a) = m.cellOf a)
    (hpartner : m.cellOf (e k) = m.star (m.cellOf a))
    (hocc : Occupied m e r0 k a) :
    e (k+1) = a ∨ e (k+1) = m.bar a := by
  have hreadCell :
      m.star (m.cellOf (e k)) = m.cellOf a := by
    rw [hpartner, m.star_invol]
  have hstep := hrun k
  rw [hreadCell] at hstep
  rcases standalone_occupied_lobe_cases m e r0 hlobe hocc with ha | hb
  · right
    rw [ha] at hstep
    exact hstep
  · left
    rw [hb, m.bar_invol] at hstep
    exact hstep

/-- A partner visit toggles the occupied lobe register exactly. -/
theorem occupied_lobe_partner_toggle
    (hrun : IsRun m e r0)
    {k a : Nat}
    (hlobe : m.cellOf (m.bar a) = m.cellOf a)
    (hpartner : m.cellOf (e k) = m.star (m.cellOf a))
    (hocc : Occupied m e r0 k a) :
    reg m e r0 (k+1) (m.cellOf a) =
      m.bar (reg m e r0 k (m.cellOf a)) := by
  have hreadCell :
      m.star (m.cellOf (e k)) = m.cellOf a := by
    rw [hpartner, m.star_invol]
  have hstep := hrun k
  rw [hreadCell] at hstep
  have hnext := occupied_lobe_partner_next_endpoint
    m e r0 hrun hlobe hpartner hocc
  have hnextCell : m.cellOf (e (k+1)) = m.cellOf a := by
    rcases hnext with h | h
    · rw [h]
    · rw [h, hlobe]
  calc
    reg m e r0 (k+1) (m.cellOf a) = e (k+1) :=
      reg_write m e r0 hnextCell
    _ = m.bar (reg m e r0 k (m.cellOf a)) := hstep

/-- Entering either endpoint of a lobe identifies the preceding cell as its
mouth partner. -/
theorem lobe_endpoint_predecessor_partner
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k a : Nat}
    (hlobe : m.cellOf (m.bar a) = m.cellOf a)
    (hnext : e (k+1) = a ∨ e (k+1) = m.bar a) :
    m.cellOf (e k) = m.star (m.cellOf a) := by
  have hfar := new_far_cell m e r0 hrun hr0 k
  have hstar : m.star (m.cellOf (e k)) = m.cellOf a := by
    rcases hnext with h | h
    · rw [h, hlobe] at hfar
      exact hfar.symm
    · rw [h, m.bar_invol] at hfar
      exact hfar.symm
  have hs := congrArg m.star hstar
  rw [m.star_invol] at hs
  exact hs

/-- If a persistent occupied lobe register changes in one step, that change
was caused by an entry into its mouth-partner cell. -/
theorem occupied_lobe_change_has_partner_predecessor
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k a : Nat}
    (hlobe : m.cellOf (m.bar a) = m.cellOf a)
    (hoccNext : Occupied m e r0 (k+1) a)
    (hchange : reg m e r0 (k+1) (m.cellOf a) ≠
      reg m e r0 k (m.cellOf a)) :
    m.cellOf (e k) = m.star (m.cellOf a) := by
  have harrival : m.cellOf (e (k+1)) = m.cellOf a := by
    apply Classical.byContradiction
    intro hne
    exact hchange (reg_skip m e r0 hne)
  have hnewReg : reg m e r0 (k+1) (m.cellOf a) = e (k+1) :=
    reg_write m e r0 harrival
  have hcases := standalone_occupied_lobe_cases
    m e r0 hlobe hoccNext
  have hnext : e (k+1) = a ∨ e (k+1) = m.bar a := by
    rw [hnewReg] at hcases
    exact hcases
  exact lobe_endpoint_predecessor_partner
    m e r0 hrun hr0 hlobe hnext

end Echo
