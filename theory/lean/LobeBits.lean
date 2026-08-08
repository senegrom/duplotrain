import GrayTailAggregation

/-!
# Boolean coding of active occupied lobes

An occupied lobe edge has both endpoints in one cell, so that cell's register
is one of the two endpoints.  One Boolean therefore records the complete
register value of an active lobe cell.  This module proves the corresponding
replay theorem for a finite list of lobe cells.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Boolean coordinate of a lobe register relative to a chosen endpoint. -/
def lobeBit (slotOf : Nat → Nat) (k c : Nat) : Bool :=
  decide (reg m e r0 k c = m.bar (slotOf c))

/-- Boolean vector of a finite lobe-cell list. -/
def lobeBits (slotOf : Nat → Nat) (cells : List Nat) (k : Nat) : List Bool :=
  cells.map (lobeBit m e r0 slotOf k)

theorem lobeBits_length (slotOf : Nat → Nat) (cells : List Nat) (k : Nat) :
    (lobeBits m e r0 slotOf cells k).length = cells.length := by
  simp [lobeBits]

/-- Equal lobe bits force equal register values at one occupied lobe cell. -/
theorem lobeBit_eq_reg_eq
    (slotOf : Nat → Nat) {i j c : Nat}
    (hcell : m.cellOf (slotOf c) = c)
    (hlobe : LobeSlot m (slotOf c))
    (hiOcc : Occupied m e r0 i (slotOf c))
    (hjOcc : Occupied m e r0 j (slotOf c))
    (hbit : lobeBit m e r0 slotOf i c = lobeBit m e r0 slotOf j c) :
    reg m e r0 i c = reg m e r0 j c := by
  have hi := occupied_lobe_register m e r0 hlobe hiOcc
  have hj := occupied_lobe_register m e r0 hlobe hjOcc
  rw [hcell] at hi hj
  by_cases hib : reg m e r0 i c = m.bar (slotOf c)
  · have hleft : lobeBit m e r0 slotOf i c = true := by
      unfold lobeBit
      exact decide_eq_true hib
    have hright : lobeBit m e r0 slotOf j c = true :=
      hbit.symm.trans hleft
    have hjb : reg m e r0 j c = m.bar (slotOf c) := by
      unfold lobeBit at hright
      exact of_decide_eq_true hright
    exact hib.trans hjb.symm
  · have hleft : lobeBit m e r0 slotOf i c = false := by
      unfold lobeBit
      exact decide_eq_false hib
    have hright : lobeBit m e r0 slotOf j c = false :=
      hbit.symm.trans hleft
    have hjn : reg m e r0 j c ≠ m.bar (slotOf c) := by
      unfold lobeBit at hright
      exact of_decide_eq_false hright
    have hin : reg m e r0 i c = slotOf c := hi.resolve_right hib
    have hjv : reg m e r0 j c = slotOf c := hj.resolve_right hjn
    exact hin.trans hjv.symm

/-- Replay of all active lobe registers from equality of their Boolean code. -/
theorem lobeBits_eq_snap_eq
    (slotOf : Nat → Nat) :
    ∀ (cells : List Nat) {i j : Nat},
      (∀ c ∈ cells, m.cellOf (slotOf c) = c) →
      (∀ c ∈ cells, LobeSlot m (slotOf c)) →
      (∀ c ∈ cells, Occupied m e r0 i (slotOf c)) →
      (∀ c ∈ cells, Occupied m e r0 j (slotOf c)) →
      lobeBits m e r0 slotOf cells i = lobeBits m e r0 slotOf cells j →
      snap m e r0 cells i = snap m e r0 cells j := by
  intro cells
  induction cells with
  | nil => intro i j hc hl hi hj hb; rfl
  | cons c rest ih =>
      intro i j hcell hlobe hiOcc hjOcc hbits
      unfold lobeBits at hbits
      simp only [List.map_cons, List.cons.injEq] at hbits
      unfold snap
      simp only [List.map_cons]
      have hhead : reg m e r0 i c = reg m e r0 j c :=
        lobeBit_eq_reg_eq m e r0 slotOf
          (hcell c List.mem_cons_self)
          (hlobe c List.mem_cons_self)
          (hiOcc c List.mem_cons_self)
          (hjOcc c List.mem_cons_self)
          hbits.1
      have htail := ih
        (fun x hx => hcell x (List.mem_cons_of_mem _ hx))
        (fun x hx => hlobe x (List.mem_cons_of_mem _ hx))
        (fun x hx => hiOcc x (List.mem_cons_of_mem _ hx))
        (fun x hx => hjOcc x (List.mem_cons_of_mem _ hx))
        hbits.2
      rw [hhead]
      unfold snap at htail
      exact congrArg (fun t => reg m e r0 j c :: t) htail

end Echo
