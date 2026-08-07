import SlotBound

/-!
# Productive-slot replay: boundary facts

If the same delivered slot occurs twice, the source cell is forced by the
entry (`predecessor_cell`) and the destination is of course fixed.  After the
two deliveries the registers of both boundary cells agree.  Consequently any
failure of full snapshot replay must be carried entirely by other cells.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- After any entry `e(k+1)`, its own cell's register is that entry. -/
theorem arrival_register (k : Nat) :
    reg m e r0 (k+1) (m.cellOf (e (k+1))) = e (k+1) := by
  exact reg_write m e r0 rfl

/-- Equal delivered entries give equal destination registers immediately
after the corresponding transitions. -/
theorem repeated_entry_destination_equal {i j : Nat}
    (heq : e (i+1) = e (j+1)) :
    reg m e r0 (i+1) (m.cellOf (e (i+1))) =
      reg m e r0 (j+1) (m.cellOf (e (i+1))) := by
  rw [arrival_register m e r0 i]
  have hj := arrival_register m e r0 j
  rw [← heq] at hj
  exact hj.symm

/-- Equal delivered entries also give equal registers in the source cell
(the cell containing the `bar` partner) after the transitions.  If source and
destination coincide this is just the write itself; otherwise the source
register is untouched and equals `bar s` at both occurrences. -/
theorem repeated_entry_source_equal
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j : Nat} (heq : e (i+1) = e (j+1)) :
    reg m e r0 (i+1) (m.cellOf (m.bar (e (i+1)))) =
      reg m e r0 (j+1) (m.cellOf (m.bar (e (i+1)))) := by
  let s := e (i+1)
  let src := m.cellOf (m.bar s)
  let dst := m.cellOf s
  have heq' : e (j+1) = s := heq.symm
  by_cases hsd : src = dst
  · have hi : reg m e r0 (i+1) dst = s := arrival_register m e r0 i
    have hj0 : reg m e r0 (j+1) (m.cellOf (e (j+1))) = e (j+1) :=
      arrival_register m e r0 j
    have hj : reg m e r0 (j+1) dst = s := by
      simpa [dst, s, heq'] using hj0
    simpa [src, dst, s, hsd] using hi.trans hj.symm
  · have hsrc_i : src ≠ m.cellOf (e (i+1)) := by
      simpa [dst, s] using hsd
    have hsrc_j : src ≠ m.cellOf (e (j+1)) := by
      simpa [heq'] using hsrc_i
    have hi0 := head_confirmed m e r0 hrun hr0 i
    have hj0 := head_confirmed m e r0 hrun hr0 j
    unfold Confirmed at hi0 hj0
    have hi : reg m e r0 i src = m.bar s := by
      simpa [src, s] using hi0
    have hj : reg m e r0 j src = m.bar s := by
      simpa [src, s, heq'] using hj0
    have hskip_i := reg_skip m e r0 (k := i) (c := src) hsrc_i.symm
    have hskip_j := reg_skip m e r0 (k := j) (c := src) hsrc_j.symm
    rw [hskip_i, hskip_j, hi, hj]

/-- For a snapshot whose listed cells are all boundary cells of a repeated
entry, replay is automatic.  This is the base case for a nesting induction. -/
theorem repeated_entry_boundary_snapshot
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {i j : Nat}
    (heq : e (i+1) = e (j+1))
    (hboundary : ∀ c ∈ cells,
      c = m.cellOf (e (i+1)) ∨ c = m.cellOf (m.bar (e (i+1)))) :
    snap m e r0 cells (i+1) = snap m e r0 cells (j+1) := by
  unfold snap
  apply List.map_congr_left
  intro c hc
  rcases hboundary c hc with hd | hs
  · subst c
    exact repeated_entry_destination_equal m e r0 heq
  · subst c
    exact repeated_entry_source_equal m e r0 hrun hr0 heq

end Echo
