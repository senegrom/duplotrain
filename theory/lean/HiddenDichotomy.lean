import HiddenAbsorb

/-!
# Hidden moves: lobe flip or permanent support loss

The cell projection forgets parallel jump edges.  This file closes the local
case split quantitatively.  A productive move invisible in the cell projection
is either

* a flip across the two endpoints of one lobe edge; or
* it empties the overwritten jump edge immediately.

By `empty_forever`, the second kind can occur only once per physical jump edge.
Thus every hidden non-lobe state change is charged to the monotone support
budget; all recurrent hidden behaviour is made entirely of lobe flips.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The overwritten edge is occupied before the write, because its old register
endpoint is confirmed. -/
theorem old_edge_occupied_before
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (k : Nat) :
    Occupied m e r0 k (oldSlot m e r0 k) := by
  left
  unfold oldSlot
  exact old_register_confirmed m e r0 hr0 k _

/-- A hidden productive move between different parallel edges empties its old
edge immediately. -/
theorem hidden_different_empties_old
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) (hp : ProductiveStep m e r0 k)
    (hpar : ParallelEdge m (oldSlot m e r0 k) (e (k+1)))
    (hdiff : ¬ SameEdge m (oldSlot m e r0 k) (e (k+1))) :
    ¬ Occupied m e r0 (k+1) (oldSlot m e r0 k) := by
  intro hpres
  exact hdiff (parallel_preserved_sameEdge m e r0 hrun hr0 k hp hpar hpres)


def SupportFixedStep (k : Nat) : Prop :=
  ∀ s, Occupied m e r0 (k+1) s ↔ Occupied m e r0 k s

/-- Inside a fixed-support step, every productive cell-projection stall is a
lobe flip. -/
theorem hidden_fixed_is_lobe
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) (hp : ProductiveStep m e r0 k)
    (hstall : ∀ c, nextCell m e r0 (k+1) c = nextCell m e r0 k c)
    (hfixed : SupportFixedStep m e r0 k) :
    e (k+1) = m.bar (oldSlot m e r0 k) ∧
    m.cellOf (m.bar (e (k+1))) = m.cellOf (e (k+1)) ∧
    m.cellOf (e (k+1)) = m.star (m.cellOf (e k)) := by
  have hbefore := old_edge_occupied_before m e r0 hr0 k
  have hafter : Occupied m e r0 (k+1) (oldSlot m e r0 k) :=
    (hfixed (oldSlot m e r0 k)).mpr hbefore
  exact hidden_preserved_lobe m e r0 hrun hr0 k hp hstall hafter

end Echo
