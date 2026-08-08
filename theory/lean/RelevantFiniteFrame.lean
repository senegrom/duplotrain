import MonotoneSupport

/-!
# Constructible finite relevant frames

A globally well-formed Nat-indexed echo machine necessarily has infinitely
many confirmed initial registers, so a finite list cannot contain *every*
confirmed cell.  The earlier `CompleteFiniteEpochFrame` condition is therefore
too strong for concrete compilation.

A relevant frame records only the finite cells and slots ever used by the run:

* every actual entry lies in `slots`;
* every listed slot belongs to a listed cell;
* `slots` is closed under the jump involution; and
* initial registers of listed cells lie in `slots`.

Registers of listed cells then remain listed.  Registers of unlisted cells are
never written and remain constant.  Hence occupancy of every unlisted physical
edge is constant, while occupancy of listed edges is controlled by the finite
support vector.  Fixed relevant support therefore implies the original global
`PairedSupportFixed` proposition without listing infinitely many inert cells.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A finite subsystem containing every dynamically relevant cell and slot. -/
structure RelevantFiniteFrame (cells slots : List Nat) where
  cells_nodup : cells.Nodup
  slots_nodup : slots.Nodup
  star_closed : ∀ c ∈ cells, m.star c ∈ cells
  bar_closed : ∀ s ∈ slots, m.bar s ∈ slots
  slot_cell : ∀ s ∈ slots, m.cellOf s ∈ cells
  entry_slot : ∀ k, e k ∈ slots
  initial_slot : ∀ c ∈ cells, r0 c ∈ slots

/-- Every entry cell is relevant. -/
theorem relevant_entry_cell
    {cells slots : List Nat}
    (frame : RelevantFiniteFrame m e r0 cells slots) (k : Nat) :
    m.cellOf (e k) ∈ cells :=
  frame.slot_cell (e k) (frame.entry_slot k)

/-- Registers of relevant cells always contain relevant slots. -/
theorem relevant_reg_mem
    {cells slots : List Nat}
    (frame : RelevantFiniteFrame m e r0 cells slots) :
    ∀ k c, c ∈ cells → reg m e r0 k c ∈ slots := by
  intro k
  induction k with
  | zero =>
      intro c hc
      by_cases hwrite : m.cellOf (e 0) = c
      · simp [reg, hwrite, frame.entry_slot]
      · simp [reg, hwrite, frame.initial_slot c hc]
  | succ n ih =>
      intro c hc
      by_cases hwrite : m.cellOf (e (n + 1)) = c
      · simp [reg, hwrite, frame.entry_slot]
      · simp [reg, hwrite, ih c hc]

/-- Registers of irrelevant cells are never written. -/
theorem irrelevant_reg_eq_initial
    {cells slots : List Nat}
    (frame : RelevantFiniteFrame m e r0 cells slots) :
    ∀ k c, c ∉ cells → reg m e r0 k c = r0 c := by
  intro k
  induction k with
  | zero =>
      intro c hc
      have hwrite : m.cellOf (e 0) ≠ c := by
        intro h
        apply hc
        rw [← h]
        exact relevant_entry_cell m e r0 frame 0
      simp [reg, hwrite]
  | succ n ih =>
      intro c hc
      have hwrite : m.cellOf (e (n + 1)) ≠ c := by
        intro h
        apply hc
        rw [← h]
        exact relevant_entry_cell m e r0 frame (n + 1)
      simp [reg, hwrite, ih c hc]

/-- An unlisted slot belonging to a relevant cell can never be confirmed. -/
theorem unlisted_relevant_not_confirmed
    {cells slots : List Nat}
    (frame : RelevantFiniteFrame m e r0 cells slots)
    {k s : Nat}
    (hs : s ∉ slots) (hc : m.cellOf s ∈ cells) :
    ¬ Confirmed m e r0 k s := by
  intro hconf
  have hmem := relevant_reg_mem m e r0 frame k (m.cellOf s) hc
  unfold Confirmed at hconf
  rw [hconf] at hmem
  exact hs hmem

/-- Confirmation of an unlisted slot is time-independent. -/
theorem unlisted_confirmed_iff
    {cells slots : List Nat}
    (frame : RelevantFiniteFrame m e r0 cells slots)
    {i j s : Nat} (hs : s ∉ slots) :
    Confirmed m e r0 i s ↔ Confirmed m e r0 j s := by
  by_cases hc : m.cellOf s ∈ cells
  · have hi := unlisted_relevant_not_confirmed
      m e r0 frame hs hc (k := i)
    have hj := unlisted_relevant_not_confirmed
      m e r0 frame hs hc (k := j)
    exact ⟨fun h => False.elim (hi h),
      fun h => False.elim (hj h)⟩
  · unfold Confirmed
    rw [irrelevant_reg_eq_initial m e r0 frame i (m.cellOf s) hc,
      irrelevant_reg_eq_initial m e r0 frame j (m.cellOf s) hc]

/-- If one endpoint of an unlisted edge were listed, bar closure would list
the other endpoint too. -/
theorem bar_not_mem_of_not_mem
    {cells slots : List Nat}
    (frame : RelevantFiniteFrame m e r0 cells slots)
    {s : Nat} (hs : s ∉ slots) : m.bar s ∉ slots := by
  intro hb
  have hs' := frame.bar_closed (m.bar s) hb
  rw [m.bar_invol] at hs'
  exact hs hs'

/-- Occupancy of an unlisted physical edge is time-independent. -/
theorem unlisted_occupied_iff
    {cells slots : List Nat}
    (frame : RelevantFiniteFrame m e r0 cells slots)
    {i j s : Nat} (hs : s ∉ slots) :
    Occupied m e r0 i s ↔ Occupied m e r0 j s := by
  have hbar := bar_not_mem_of_not_mem m e r0 frame hs
  have hsIff := unlisted_confirmed_iff
    m e r0 frame (i := i) (j := j) hs
  have hbIff := unlisted_confirmed_iff
    m e r0 frame (i := i) (j := j) hbar
  unfold Occupied
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl (hsIff.mp h)
    · exact Or.inr (hbIff.mp h)
  · intro h
    rcases h with h | h
    · exact Or.inl (hsIff.mpr h)
    · exact Or.inr (hbIff.mpr h)

/-- Support fixed only on the finite relevant slot list. -/
def RelevantSupportFixed
    (lo hi : Nat) (slots : List Nat) : Prop :=
  ∀ k, lo ≤ k → k < hi →
    ∀ s ∈ slots,
      Occupied m e r0 k s ↔ Occupied m e r0 (k + 1) s

/-- **Finite relevant support implies global support fixedness.** -/
theorem pairedSupportFixed_of_relevant
    {cells slots : List Nat}
    (frame : RelevantFiniteFrame m e r0 cells slots)
    {lo hi : Nat}
    (hfixed : RelevantSupportFixed m e r0 lo hi slots) :
    PairedSupportFixed m e r0 lo hi := by
  intro k hkLo hkHi s
  by_cases hs : s ∈ slots
  · exact hfixed k hkLo hkHi s hs
  · exact unlisted_occupied_iff m e r0 frame hs

/-- Equality of finite support snapshots gives occupancy equivalence at every
listed slot. -/
theorem relevant_occupied_iff_of_supportSnap_eq
    (slots : List Nat) {i j : Nat}
    (hsnap : supportSnap m e r0 slots i =
      supportSnap m e r0 slots j) :
    ∀ s ∈ slots,
      Occupied m e r0 i s ↔ Occupied m e r0 j s := by
  intro s hs
  unfold supportSnap at hsnap
  have hbool : decide (Occupied m e r0 i s) =
      decide (Occupied m e r0 j s) := by
    induction slots with
    | nil => cases hs
    | cons a rest ih =>
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · have hh := congrArg List.head? hsnap
          simpa using hh
        · have ht := congrArg List.tail hsnap
          simp only [List.map_cons, List.tail_cons] at ht
          exact ih ht hs
  constructor
  · intro hi
    apply of_decide_eq_true
    rw [← hbool]
    exact decide_eq_true hi
  · intro hj
    apply of_decide_eq_true
    rw [hbool]
    exact decide_eq_true hj

/-- Equal endpoint support, together with global monotonicity, fixes every
relevant support coordinate throughout the interval. -/
theorem relevantSupportFixed_of_endpoint_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (slots : List Nat) {lo hi : Nat}
    (hend : supportSnap m e r0 slots lo =
      supportSnap m e r0 slots hi) :
    RelevantSupportFixed m e r0 lo hi slots := by
  intro k hkLo hkHi s hs
  have hlohi : lo ≤ hi := by omega
  have hloK : Occupied m e r0 lo s → Occupied m e r0 k s := by
    intro hlo
    have hHi :=
      (relevant_occupied_iff_of_supportSnap_eq
        m e r0 slots hend s hs).mp hlo
    exact occupied_later_earlier m e r0 hrun hr0
      (by omega) hHi
  have hkLoOcc : Occupied m e r0 k s →
      Occupied m e r0 lo s := by
    intro hk
    exact occupied_later_earlier m e r0 hrun hr0 hkLo hk
  have hSuccHi : Occupied m e r0 hi s →
      Occupied m e r0 (k + 1) s := by
    intro hHi
    exact occupied_later_earlier m e r0 hrun hr0
      (by omega) hHi
  constructor
  · intro hk
    have hlo := hkLoOcc hk
    have hHi :=
      (relevant_occupied_iff_of_supportSnap_eq
        m e r0 slots hend s hs).mp hlo
    exact hSuccHi hHi
  · intro hk1
    exact occupied_later_earlier m e r0 hrun hr0
      (Nat.le_succ k) hk1

/-- Equal finite support endpoints yield the original global support-fixed
hypothesis through a constructible relevant frame. -/
theorem pairedSupportFixed_of_endpoint_supportSnap
    {cells slots : List Nat}
    (frame : RelevantFiniteFrame m e r0 cells slots)
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat}
    (hend : supportSnap m e r0 slots lo =
      supportSnap m e r0 slots hi) :
    PairedSupportFixed m e r0 lo hi :=
  pairedSupportFixed_of_relevant m e r0 frame
    (relevantSupportFixed_of_endpoint_eq
      m e r0 hrun hr0 slots hend)

end Echo
