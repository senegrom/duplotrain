import ExternalLobeRoundtrip

/-!
# External lobe reflection, without named endpoints

The essential mechanism can be stated more invariantly.  Whenever the entry
at time `k+1` lies on a lobe edge, that step immediately reflects the walk
back across the support edge used at time `k`:

    e(k+2) = bar(e k).

Thus two successive support vertices whose mouth partners currently select
lobe edges return the walk to its starting support entry in four steps.  This
form is convenient for the component-reservation proof because it does not
require choosing persistent names for the two lobe endpoints.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The current entry lies on an internal/lobe jump edge. -/
def LobeEntryAt (k : Nat) : Prop :=
  m.cellOf (m.bar (e k)) = m.cellOf (e k)

/-- A cell currently selects one endpoint of an occupied lobe edge. -/
def OccupiedLobeAt (k c : Nat) : Prop :=
  ∃ a,
    m.cellOf a = c ∧
    m.cellOf (m.bar a) = m.cellOf a ∧
    Occupied m e r0 k a

/-- **A lobe entry reflects the preceding support entry.** -/
theorem lobe_entry_reflects
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k : Nat}
    (hlobe : LobeEntryAt m e (k+1)) :
    e (k+2) = m.bar (e k) := by
  have hw := witness m e r0 hrun hr0 k
  have hnextCell :
      m.cellOf (e (k+1)) = m.star (m.cellOf (e k)) := by
    calc
      m.cellOf (e (k+1)) = m.cellOf (m.bar (e (k+1))) := hlobe.symm
      _ = m.star (m.cellOf (e k)) := hw.1
  have hwrite : reg m e r0 k (m.cellOf (e k)) = e k :=
    reg_write m e r0 rfl
  have hforeign :
      m.cellOf (e (k+1)) ≠ m.cellOf (e k) := by
    intro h
    apply m.star_ne (m.cellOf (e k))
    exact hnextCell.symm.trans h
  have hkeep :
      reg m e r0 (k+1) (m.cellOf (e k)) = e k := by
    rw [reg_skip m e r0 hforeign, hwrite]
  calc
    e (k+2) = m.bar
        (reg m e r0 (k+1)
          (m.star (m.cellOf (e (k+1))))) := hrun (k+1)
    _ = m.bar (reg m e r0 (k+1) (m.cellOf (e k))) := by
          rw [hnextCell, m.star_invol]
    _ = m.bar (e k) := by rw [hkeep]

/-- Occupancy of a lobe edge in the mouth-partner cell forces the next entry
to be a lobe entry. -/
theorem next_lobe_of_occupied_partner
    (hrun : IsRun m e r0)
    {k : Nat}
    (hocc : OccupiedLobeAt m e r0 k
      (m.star (m.cellOf (e k)))) :
    LobeEntryAt m e (k+1) := by
  rcases hocc with ⟨a, haCell, haLobe, haOcc⟩
  have hreg := external_lobe_register_cases m e r0
    haCell haLobe haOcc
  have hnext : e (k+1) = m.bar a ∨ e (k+1) = a := by
    rw [hrun k]
    rcases hreg with hreg | hreg
    · left
      rw [hreg]
    · right
      rw [hreg, m.bar_invol]
  unfold LobeEntryAt
  rcases hnext with hnext | hnext
  · rw [hnext, m.bar_invol, haLobe]
  · rw [hnext, haLobe]

/-- Two successive lobe entries give a four-step support roundtrip. -/
theorem two_lobe_entries_roundtrip
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k : Nat}
    (hfirst : LobeEntryAt m e (k+1))
    (hsecond : LobeEntryAt m e (k+3)) :
    e (k+2) = m.bar (e k) ∧ e (k+4) = e k := by
  have h2 := lobe_entry_reflects m e r0 hrun hr0 hfirst
  have h4 := lobe_entry_reflects m e r0 hrun hr0 hsecond
  constructor
  · exact h2
  · rw [h2, m.bar_invol] at h4
    exact h4

/-- **Adjacent external reflectors roundtrip.**  It is enough that the mouth
partner of the current support cell carries an occupied lobe, and that the
same is true after the first reflection. -/
theorem two_occupied_external_lobes_roundtrip
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k : Nat}
    (hfirst : OccupiedLobeAt m e r0 k
      (m.star (m.cellOf (e k))))
    (hsecond : OccupiedLobeAt m e r0 (k+2)
      (m.star (m.cellOf (e (k+2))))) :
    e (k+2) = m.bar (e k) ∧ e (k+4) = e k := by
  have hl1 := next_lobe_of_occupied_partner m e r0 hrun hfirst
  have hl2 := next_lobe_of_occupied_partner m e r0 hrun hsecond
  exact two_lobe_entries_roundtrip m e r0 hrun hr0 hl1 hl2

end Echo
