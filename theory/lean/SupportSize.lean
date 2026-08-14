import ThreeQuarterArithmetic
import SupportMove

/-!
# Occupied support has at most as many edges as cells

Choose one confirmed endpoint of every occupied jump edge.  Two distinct edge
representatives cannot choose confirmed endpoints in the same cell, because a
cell has exactly one confirmed slot.  This injects occupied support edges into
cells.

This is the cardinality half of the pseudoforest structure and also bounds the
number of monotone support epochs by `#cells + 1`.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A list contains at most one representative of each physical jump edge. -/
def EdgeRepresentatives (edges : List Nat) : Prop :=
  edges.Nodup ∧
  ∀ s, s ∈ edges → ∀ t, t ∈ edges → SameEdge m s t → s = t

/-- Pick a confirmed endpoint when the edge is occupied. -/
noncomputable def chosenEndpoint
    (m : Machine) (e r0 : Nat → Nat) (k s : Nat) : Nat := by
  classical
  exact if Confirmed m e r0 k s then s else m.bar s

theorem chosenEndpoint_sameEdge (k s : Nat) :
    SameEdge m s (chosenEndpoint m e r0 k s) := by
  classical
  unfold chosenEndpoint
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem chosenEndpoint_confirmed {k s : Nat}
    (hocc : Occupied m e r0 k s) :
    Confirmed m e r0 k (chosenEndpoint m e r0 k s) := by
  classical
  unfold chosenEndpoint
  split <;> rename_i h
  · exact h
  · exact hocc.resolve_left h

/-- Same-edge is transitive. -/
theorem sameEdge_trans {a b c : Nat}
    (hab : SameEdge m a b) (hbc : SameEdge m b c) :
    SameEdge m a c := by
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · exact Or.inl (hbc.trans hab)
  · subst b
    exact Or.inr hbc
  · subst c
    exact Or.inr hab
  · subst b
    rw [m.bar_invol] at hbc
    exact Or.inl hbc

private theorem nodup_subset_length_nat {l S : List Nat}
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ S) : l.length ≤ S.length := by
  induction l generalizing S with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ S.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

end Echo
