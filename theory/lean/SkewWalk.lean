import EdgeReversal

/-!
# The echo machine as a skew-symmetric pointer-reversal walk

A slot `x` is regarded as a directed arc.  Its head is `cellOf x`; its tail
is `star (cellOf (bar x))`.  The involution `bar` sends an arc to its
star-reversed mate.  The current registers select one outgoing arc at every
cell.  A machine step traverses the selected arc and installs its mate at the
mate of the destination.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Head cell of the arc represented by a slot. -/
def arcHead (x : Nat) : Nat := m.cellOf x

/-- Tail cell of the arc represented by a slot. -/
def arcTail (x : Nat) : Nat := m.star (m.cellOf (m.bar x))

/-- The outgoing arc currently selected at cell `c`. -/
def rotor (k c : Nat) : Nat :=
  m.bar (reg m e r0 k (m.star c))

/-- Taking the mate reverses an arc and applies `star` to both endpoints. -/
theorem arcTail_bar (x : Nat) :
    arcTail m (m.bar x) = m.star (arcHead m x) := by
  unfold arcTail arcHead
  rw [m.bar_invol]

/-- The head of the mate is the mate of the original tail. -/
theorem arcHead_bar (x : Nat) :
    arcHead m (m.bar x) = m.star (arcTail m x) := by
  unfold arcHead arcTail
  rw [m.star_invol]

/-- The entries of a well-formed run form a directed walk in the fixed skew
arc graph. -/
theorem arc_path
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) :
    arcTail m (e (k+1)) = arcHead m (e k) := by
  unfold arcTail arcHead
  have hw := (witness m e r0 hrun hr0 k).1
  have hs := congrArg m.star hw
  rw [m.star_invol] at hs
  exact hs

/-- The run follows the selected rotor at its current head cell. -/
theorem rotor_current (hrun : IsRun m e r0) (k : Nat) :
    rotor m e r0 k (arcHead m (e k)) = e (k+1) := by
  unfold rotor arcHead
  exact (hrun k).symm

/-- Immediately after traversing an arc, the rotor at the mate of its head is
its mate arc.  This is the one-line pointer reversal rule. -/
theorem rotor_mate_after (k : Nat) :
    rotor m e r0 (k+1) (m.star (arcHead m (e (k+1))))
      = m.bar (e (k+1)) := by
  unfold rotor arcHead
  rw [m.star_invol, reg_write m e r0 rfl]

/-- Every state stores the mate of its incoming arc at the mate of the current
head. -/
theorem rotor_incoming_mate (k : Nat) :
    rotor m e r0 k (m.star (arcHead m (e k))) = m.bar (e k) := by
  unfold rotor arcHead
  rw [m.star_invol, reg_write m e r0 rfl]

/-- A step changes no rotor except the one at the mate of its destination. -/
theorem rotor_skip {k c : Nat}
    (hne : c ≠ m.star (arcHead m (e (k+1)))) :
    rotor m e r0 (k+1) c = rotor m e r0 k c := by
  have hcell : m.cellOf (e (k+1)) ≠ m.star c := by
    intro h
    have hs := congrArg m.star h
    rw [m.star_invol] at hs
    exact hne hs.symm
  unfold rotor
  rw [reg_skip m e r0 hcell]

/-- If consecutive entries lie in different cells, the new state still stores
the preceding entry in the preceding cell; equivalently the predecessor arc
can be recovered from the corresponding mate rotor. -/
theorem recover_previous_of_head_ne {k : Nat}
    (hne : arcHead m (e (k+1)) ≠ arcHead m (e k)) :
    m.bar (rotor m e r0 (k+1) (m.star (arcHead m (e k)))) = e k := by
  unfold rotor arcHead
  have hs : m.cellOf (e (k+1)) ≠ m.cellOf (e k) := hne
  rw [m.star_invol, reg_skip m e r0 hs, reg_write m e r0 rfl,
    m.bar_invol]

end Echo
