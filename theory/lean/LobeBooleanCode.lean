import AbstractSparseEpochBound

/-!
# Exact Boolean code for occupied lobe registers

If both endpoints of a jump edge lie in one cell and that edge is occupied,
the cell register equals one of the two endpoints.  The Boolean predicate
"the register is the bar endpoint" therefore determines the register exactly.
A list of active lobe representatives contributes one exact Boolean coordinate
per cell.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Cells represented by lobe slots. -/
def booleanLobeCells (lobes : List Nat) : List Nat :=
  lobes.map m.cellOf

/-- One Boolean per lobe: `true` means the bar endpoint is selected. -/
open Classical in
noncomputable def booleanLobeCode
    (lobes : List Nat) (k : Nat) : List Bool :=
  lobes.map (fun a =>
    decide (reg m e r0 k (m.cellOf a) = m.bar a))

theorem booleanLobeCode_length (lobes : List Nat) (k : Nat) :
    (booleanLobeCode m e r0 lobes k).length = lobes.length := by
  simp [booleanLobeCode]

/-- Occupancy plus the lobe equation restricts the register to the two coded
endpoints. -/
theorem occupied_lobe_register_cases
    {k a : Nat}
    (hloop : m.cellOf (m.bar a) = m.cellOf a)
    (hocc : Occupied m e r0 k a) :
    reg m e r0 k (m.cellOf a) = a ∨
      reg m e r0 k (m.cellOf a) = m.bar a := by
  rcases hocc with ha | hb
  · left
    unfold Confirmed at ha
    exact ha
  · right
    unfold Confirmed at hb
    rw [hloop] at hb
    exact hb

/-- Equal lobe bits replay every represented lobe register. -/
theorem booleanLobeCode_eq_regs
    (lobes : List Nat) {i j : Nat}
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hiOcc : ∀ a ∈ lobes, Occupied m e r0 i a)
    (hjOcc : ∀ a ∈ lobes, Occupied m e r0 j a)
    (hcode : booleanLobeCode m e r0 lobes i =
      booleanLobeCode m e r0 lobes j) :
    ∀ a ∈ lobes,
      reg m e r0 i (m.cellOf a) =
        reg m e r0 j (m.cellOf a) := by
  classical
  induction lobes with
  | nil => simp
  | cons a rest ih =>
      simp only [booleanLobeCode, List.map_cons] at hcode
      have hhead := congrArg List.head? hcode
      have htail := congrArg List.tail hcode
      simp only [List.head?_cons] at hhead
      simp only [List.tail_cons] at htail
      have haLoop := hloop a List.mem_cons_self
      have hiA := occupied_lobe_register_cases m e r0
        haLoop (hiOcc a List.mem_cons_self)
      have hjA := occupied_lobe_register_cases m e r0
        haLoop (hjOcc a List.mem_cons_self)
      have hrestLoop : ∀ b ∈ rest,
          m.cellOf (m.bar b) = m.cellOf b := by
        intro b hb
        exact hloop b (List.mem_cons_of_mem _ hb)
      have hiRest : ∀ b ∈ rest, Occupied m e r0 i b := by
        intro b hb
        exact hiOcc b (List.mem_cons_of_mem _ hb)
      have hjRest : ∀ b ∈ rest, Occupied m e r0 j b := by
        intro b hb
        exact hjOcc b (List.mem_cons_of_mem _ hb)
      have hrest := ih hrestLoop hiRest hjRest htail
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · rcases hiA with hiEq | hiEq <;>
          rcases hjA with hjEq | hjEq
        · exact hiEq.trans hjEq.symm
        · by_cases hab : a = m.bar a
          · exact hiEq.trans hab.trans hjEq.symm
          · exfalso
            simp [hiEq, hjEq, hab] at hhead
        · by_cases hab : a = m.bar a
          · exact hiEq.trans hab.symm.trans hjEq.symm
          · exfalso
            have hne : m.bar a ≠ a := by
              intro h
              exact hab h.symm
            simp [hiEq, hjEq, hab, hne] at hhead
        · exact hiEq.trans hjEq.symm
      · exact hrest b hb

/-- Equality of the Boolean code is equality of the lobe-cell snapshot. -/
theorem booleanLobeCode_eq_snap
    (lobes : List Nat) {i j : Nat}
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hiOcc : ∀ a ∈ lobes, Occupied m e r0 i a)
    (hjOcc : ∀ a ∈ lobes, Occupied m e r0 j a)
    (hcode : booleanLobeCode m e r0 lobes i =
      booleanLobeCode m e r0 lobes j) :
    snap m e r0 (booleanLobeCells m lobes) i =
      snap m e r0 (booleanLobeCells m lobes) j := by
  unfold snap booleanLobeCells
  simp only [List.map_map]
  apply List.map_congr_left
  intro a ha
  exact booleanLobeCode_eq_regs m e r0 lobes
    hloop hiOcc hjOcc hcode a ha

end Echo
