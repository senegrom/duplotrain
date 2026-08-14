import EdgeReversal

/-!
# Consequences of the exact edge-reversal rule

The cell-level state changes at only one source.  A transition

    a -> b

writes the mirror arrow

    star b -> star a.

That arrow remains in place until cell `b` is entered again.  Hence a later
visit to `star b`, with no intervening visit to `b`, is forced to return to
`star a`.  This is the local LIFO / nesting fact needed for a pumping bound.

The file also separates genuinely cell-level productive steps from hidden
slot-level writes: if the newly installed mirror arrow already had its new
value, then the entire cell projection is unchanged.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

theorem nextCell_stable {i c : Nat} :
    ∀ d, (∀ l, i < l → l ≤ i + d →
      m.cellOf (e l) ≠ m.star c) →
      nextCell m e r0 (i+d) c = nextCell m e r0 i c := by
  intro d hno
  unfold nextCell
  rw [reg_stable m e r0 d hno]


theorem nextCell_stall_of_mirror_present
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat)
    (hpresent : nextCell m e r0 k
      (m.star (m.cellOf (e (k+1)))) = m.star (m.cellOf (e k))) :
    ∀ c, nextCell m e r0 (k+1) c = nextCell m e r0 k c := by
  intro c
  rw [nextCell_update m e r0 hrun hr0 k c]
  by_cases hc : c = m.star (m.cellOf (e (k+1)))
  · rw [if_pos hc, hc]
    exact hpresent.symm
  · rw [if_neg hc]

end Echo
