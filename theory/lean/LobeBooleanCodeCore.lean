import SupportMove

/-!
# Exact one-bit code for occupied lobe registers

An occupied lobe edge has both endpoints in one cell, so that cell's register
is one of the two endpoints.  The Boolean predicate saying that the bar
endpoint is selected therefore determines the register exactly.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Cells represented by lobe slots. -/
def coreLobeCells (lobes : List Nat) : List Nat :=
  lobes.map m.cellOf

/-- One Boolean per lobe representative. -/
open Classical in
noncomputable def coreLobeBits
    (lobes : List Nat) (k : Nat) : List Bool :=
  lobes.map (fun a =>
    decide (reg m e r0 k (m.cellOf a) = m.bar a))

theorem coreLobeBits_length (lobes : List Nat) (k : Nat) :
    (coreLobeBits m e r0 lobes k).length = lobes.length := by
  simp [coreLobeBits]

/-- Occupancy restricts the register to the two lobe endpoints. -/
theorem core_occupied_lobe_cases
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

private theorem core_map_eq_at_mem
    {α β : Type} {xs : List α} {p q : α → β}
    (h : xs.map p = xs.map q) {x : α} (hx : x ∈ xs) :
    p x = q x := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hh := congrArg List.head? h
        simpa using hh
      · have ht := congrArg List.tail h
        simp only [List.map_cons, List.tail_cons] at ht
        exact ih ht hx

/-- Equal lobe bits force equal registers at one occupied lobe. -/
theorem core_lobe_reg_eq_of_bit_eq
    {i j a : Nat}
    (hloop : m.cellOf (m.bar a) = m.cellOf a)
    (hiOcc : Occupied m e r0 i a)
    (hjOcc : Occupied m e r0 j a)
    (hbit :
      decide (reg m e r0 i (m.cellOf a) = m.bar a) =
      decide (reg m e r0 j (m.cellOf a) = m.bar a)) :
    reg m e r0 i (m.cellOf a) =
      reg m e r0 j (m.cellOf a) := by
  rcases core_occupied_lobe_cases m e r0 hloop hiOcc with
      hi | hi <;>
    rcases core_occupied_lobe_cases m e r0 hloop hjOcc with
      hj | hj
  · exact hi.trans hj.symm
  · by_cases hab : a = m.bar a
    · exact hi.trans hab.trans hj.symm
    · exfalso
      simp [hi, hj, hab] at hbit
  · by_cases hab : a = m.bar a
    · exact hi.trans hab.symm.trans hj.symm
    · have hba : m.bar a ≠ a := by
        intro h
        exact hab h.symm
      exfalso
      simp [hi, hj, hab, hba] at hbit
  · exact hi.trans hj.symm

/-- Equality of the Boolean list replays every represented lobe register. -/
theorem coreLobeBits_eq_regs
    (lobes : List Nat) {i j : Nat}
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hiOcc : ∀ a ∈ lobes, Occupied m e r0 i a)
    (hjOcc : ∀ a ∈ lobes, Occupied m e r0 j a)
    (hcode : coreLobeBits m e r0 lobes i =
      coreLobeBits m e r0 lobes j) :
    ∀ a ∈ lobes,
      reg m e r0 i (m.cellOf a) =
        reg m e r0 j (m.cellOf a) := by
  classical
  intro a ha
  unfold coreLobeBits at hcode
  have hbit := core_map_eq_at_mem hcode ha
  exact core_lobe_reg_eq_of_bit_eq m e r0
    (hloop a ha) (hiOcc a ha) (hjOcc a ha) hbit

/-- Snapshot form. -/
theorem coreLobeBits_eq_snap
    (lobes : List Nat) {i j : Nat}
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hiOcc : ∀ a ∈ lobes, Occupied m e r0 i a)
    (hjOcc : ∀ a ∈ lobes, Occupied m e r0 j a)
    (hcode : coreLobeBits m e r0 lobes i =
      coreLobeBits m e r0 lobes j) :
    snap m e r0 (coreLobeCells m lobes) i =
      snap m e r0 (coreLobeCells m lobes) j := by
  unfold snap coreLobeCells
  simp only [List.map_map]
  apply List.map_congr_left
  intro a ha
  exact coreLobeBits_eq_regs m e r0 lobes
    hloop hiOcc hjOcc hcode a ha

end Echo
