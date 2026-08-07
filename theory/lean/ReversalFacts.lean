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

/-- The finite projection of the arrow function onto a list of cells. -/
def cellSnap (cells : List Nat) (k : Nat) : List Nat :=
  cells.map (nextCell m e r0 k)

/-- A cell-level arrow is stable over an interval containing no write to its
underlying register cell. -/
theorem nextCell_stable {i c : Nat} :
    ∀ d, (∀ l, i < l → l ≤ i + d →
      m.cellOf (e l) ≠ m.star c) →
      nextCell m e r0 (i+d) c = nextCell m e r0 i c := by
  intro d hno
  unfold nextCell
  rw [reg_stable m e r0 d hno]

/-- After `a -> b`, the installed arrow `star b -> star a` survives every
later step until the next entry into cell `b`. -/
theorem mirror_arrow_stable
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k d : Nat)
    (hno : ∀ l, k+1 < l → l ≤ k+1+d →
      m.cellOf (e l) ≠ m.cellOf (e (k+1))) :
    nextCell m e r0 (k+1+d) (m.star (m.cellOf (e (k+1)))) =
      m.star (m.cellOf (e k)) := by
  calc
    nextCell m e r0 (k+1+d) (m.star (m.cellOf (e (k+1))))
        = nextCell m e r0 (k+1) (m.star (m.cellOf (e (k+1)))) := by
            apply nextCell_stable m e r0 d
            intro l hl1 hl2
            rw [m.star_invol]
            exact hno l hl1 hl2
    _ = m.star (m.cellOf (e k)) :=
      reversed_arrow m e r0 hrun hr0 k

/-- **Forced mirror return.**  If no `b`-entry occurs after a transition
`a -> b`, then a later visit to `star b` must immediately go to `star a`. -/
theorem forced_mirror_return
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k d : Nat)
    (hno : ∀ l, k+1 < l → l ≤ k+1+d →
      m.cellOf (e l) ≠ m.cellOf (e (k+1)))
    (hcur : m.cellOf (e (k+1+d)) =
      m.star (m.cellOf (e (k+1)))) :
    m.cellOf (e (k+1+d+1)) = m.star (m.cellOf (e k)) := by
  calc
    m.cellOf (e (k+1+d+1))
        = nextCell m e r0 (k+1+d) (m.cellOf (e (k+1+d))) :=
            (cell_step m e r0 hrun (k+1+d)).symm
    _ = nextCell m e r0 (k+1+d)
          (m.star (m.cellOf (e (k+1)))) := by rw [hcur]
    _ = m.star (m.cellOf (e k)) :=
      mirror_arrow_stable m e r0 hrun hr0 k d hno

/-- The only source whose cell-level arrow can change at step `k` is the
mirror of the arrival cell. -/
theorem nextCell_changed_source
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k c : Nat}
    (hchg : nextCell m e r0 (k+1) c ≠ nextCell m e r0 k c) :
    c = m.star (m.cellOf (e (k+1))) := by
  by_contra hne
  exact hchg (nextCell_skip m e r0 hne)

/-- If the mirror arrow already points backwards, the step makes no change at
all to the cell-level arrow function.  Such a step may still change a slot
inside one cell; this is exactly the hidden lobe/parallel-edge fibre. -/
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

/-- The finite cell projection is unchanged in the hidden-fibre case. -/
theorem cellSnap_stall_of_mirror_present
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) (k : Nat)
    (hpresent : nextCell m e r0 k
      (m.star (m.cellOf (e (k+1)))) = m.star (m.cellOf (e k))) :
    cellSnap m e r0 cells (k+1) = cellSnap m e r0 cells k := by
  unfold cellSnap
  apply List.map_congr_left
  intro c _
  exact nextCell_stall_of_mirror_present m e r0 hrun hr0 k hpresent c

end Echo
