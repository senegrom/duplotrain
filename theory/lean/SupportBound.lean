import PairBound

/-!
# Monotone jump-edge support

A jump edge is `Occupied` when at least one of its two slot endpoints is the
current register value of its cell.  The occupied support can only shrink:
a step can move a confirmation onto a previously-unconfirmed arrival slot,
but the opposite endpoint of that jump edge was necessarily confirmed just
before the step (`head_confirmed`).  Hence a completely empty jump edge can
never become occupied later.

This is a set-valued monovariant, strictly stronger than the previously proved
non-increase of the *number* of token ends.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- At least one endpoint of the jump edge represented by `s` is confirmed. -/
def Occupied (k s : Nat) : Prop :=
  Confirmed m e r0 k s ∨ Confirmed m e r0 k (m.bar s)

noncomputable instance (k s : Nat) : Decidable (Occupied m e r0 k s) := by
  classical
  unfold Occupied Confirmed
  infer_instance

/-- Occupancy is independent of which endpoint represents the jump edge. -/
theorem occupied_bar (k s : Nat) :
    Occupied m e r0 k (m.bar s) ↔ Occupied m e r0 k s := by
  unfold Occupied
  rw [m.bar_invol]
  exact or_comm

/-- **Occupied support is pointwise non-increasing.** If a jump edge is
occupied after a step, it was already occupied before that step. -/
theorem occupied_nonincreasing
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k s : Nat) :
    Occupied m e r0 (k+1) s → Occupied m e r0 k s := by
  intro hocc
  rcases hocc with hs | hb
  · rcases (confirmed_step m e r0 k s).mp hs with he | ⟨_, hold⟩
    · subst s
      exact Or.inr (head_confirmed m e r0 hrun hr0 k)
    · exact Or.inl hold
  · rcases (confirmed_step m e r0 k (m.bar s)).mp hb with he | ⟨_, hold⟩
    · have hh := head_confirmed m e r0 hrun hr0 k
      have hsold : Confirmed m e r0 k s := by
        rw [← he, m.bar_invol] at hh
        exact hh
      exact Or.inl hsold
    · exact Or.inr hold

/-- Contrapositive form: once a jump edge is empty, it stays empty for the
next step.  Iterating this gives permanent disappearance. -/
theorem empty_stays_empty
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k s : Nat) (hempty : ¬ Occupied m e r0 k s) :
    ¬ Occupied m e r0 (k+1) s := by
  intro h
  exact hempty (occupied_nonincreasing m e r0 hrun hr0 k s h)

/-- Once empty, an edge remains empty at every later time. -/
theorem empty_forever
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k j s : Nat} (hkj : k ≤ j) (hempty : ¬ Occupied m e r0 k s) :
    ¬ Occupied m e r0 j s := by
  obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j-k, by omega⟩
  induction d with
  | zero => simpa using hempty
  | succ n ih =>
      have ih' : ¬ Occupied m e r0 (k+n) s := ih (by omega)
      have hstep := empty_stays_empty m e r0 hrun hr0 (k+n) s ih'
      simpa [Nat.add_assoc] using hstep

end Echo
