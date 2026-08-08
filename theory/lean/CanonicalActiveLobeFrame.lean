import CanonicalSupportFrame
import ActiveLobeCoverCore
import SupportRelativePointwiseReplay
import PersistentLobeSeparationStandalone

/-!
# Canonical active lobes in a finite fixed-support epoch

A finite epoch frame lists all represented cells and all slots their registers
can select.  At one reference time we choose the canonical occupied jump-edge
representatives.  An edge is an active lobe exactly when it is internal to one
cell and that cell is written during the interval.

The resulting lobe list is canonical.  It has one entry per active lobe cell,
is occupied throughout the fixed-support interval, is actually visited, and
yields the complete support-relative replay cover.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Finite data covering every represented register throughout an epoch. -/
structure FiniteEpochFrame
    (lo hi : Nat) (cells slots : List Nat) where
  cells_nodup : cells.Nodup
  slots_nodup : slots.Nodup
  star_closed : ∀ c ∈ cells, m.star c ∈ cells
  bar_closed : ∀ s ∈ slots, m.bar s ∈ slots
  bar_ne : ∀ s ∈ slots, m.bar s ≠ s
  slot_cell : ∀ s ∈ slots, m.cellOf s ∈ cells
  selected : ∀ k, lo ≤ k → k ≤ hi → ∀ c ∈ cells,
    reg m e r0 k c ∈ slots

/-- Canonical occupied lobe representatives whose cells are written. -/
open Classical in
noncomputable def canonicalActiveLobes
    (lo hi : Nat) (slots : List Nat) (k0 : Nat) : List Nat :=
  (canonicalSupportEdges m e r0 slots k0).filter fun a =>
    m.cellOf (m.bar a) = m.cellOf a ∧
      CellWrittenIn m e r0 lo hi (m.cellOf a)

theorem mem_canonicalActiveLobes_iff
    {lo hi k0 : Nat} {slots : List Nat} {a : Nat} :
    a ∈ canonicalActiveLobes m e r0 lo hi slots k0 ↔
      a ∈ canonicalSupportEdges m e r0 slots k0 ∧
      m.cellOf (m.bar a) = m.cellOf a ∧
      CellWrittenIn m e r0 lo hi (m.cellOf a) := by
  classical
  simp [canonicalActiveLobes]

/-- Same-edge representatives preserve the lobe property. -/
theorem lobe_of_sameEdge
    {s t : Nat} (hst : SameEdge m s t)
    (hloop : m.cellOf (m.bar s) = m.cellOf s) :
    m.cellOf (m.bar t) = m.cellOf t := by
  rcases hst with rfl | rfl
  · exact hloop
  · rw [m.bar_invol]
    exact hloop.symm

/-- A lobe edge and any same-edge representative have the same cell. -/
theorem cell_eq_of_sameEdge_lobe
    {s t : Nat} (hst : SameEdge m s t)
    (hloop : m.cellOf (m.bar s) = m.cellOf s) :
    m.cellOf t = m.cellOf s := by
  rcases hst with rfl | rfl
  · rfl
  · exact hloop

/-- Two ordered canonical representatives of one physical edge are equal. -/
theorem canonicalSupport_sameEdge_eq
    {slots : List Nat} {k0 a b : Nat}
    (ha : a ∈ canonicalSupportEdges m e r0 slots k0)
    (hb : b ∈ canonicalSupportEdges m e r0 slots k0)
    (hab : SameEdge m a b) : a = b := by
  rcases hab with h | h
  · exact h.symm
  · have halt := canonicalSupportEdges_ordered m e r0 slots k0 a ha
    have hblt := canonicalSupportEdges_ordered m e r0 slots k0 b hb
    rw [h, m.bar_invol] at hblt
    omega

/-- A support representative belongs to the original finite slot list. -/
theorem canonicalSupportEdge_mem_slots
    {slots : List Nat} {k0 s : Nat}
    (hs : s ∈ canonicalSupportEdges m e r0 slots k0) :
    s ∈ slots := by
  classical
  have hc : s ∈ canonicalEdgesCore m slots :=
    (List.mem_filter.mp hs).1
  exact (mem_canonicalEdgesCore_iff.mp hc).1

/-- Occupancy of a lobe places at least one endpoint in the cell's register. -/
theorem occupied_lobes_same_cell_sameEdge
    {k a b : Nat}
    (haLoop : m.cellOf (m.bar a) = m.cellOf a)
    (hbLoop : m.cellOf (m.bar b) = m.cellOf b)
    (haOcc : Occupied m e r0 k a)
    (hbOcc : Occupied m e r0 k b)
    (hcell : m.cellOf a = m.cellOf b) :
    SameEdge m a b := by
  have ha := standalone_occupied_lobe_cases m e r0 haLoop haOcc
  have hb := standalone_occupied_lobe_cases m e r0 hbLoop hbOcc
  rw [hcell] at ha
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Or.inl (hb.symm.trans ha)
  · have h := congrArg m.bar (ha.symm.trans hb)
    have hba : b = m.bar a := by
      have hab : m.bar a = b := by
        simpa only [m.bar_invol] using h
      exact hab.symm
    exact Or.inr hba
  · exact Or.inr (hb.symm.trans ha)
  · have h := congrArg m.bar (hb.symm.trans ha)
    exact Or.inl (by simpa only [m.bar_invol] using h)

private theorem map_nodup_of_injective_on
    {α β : Type} (f : α → β) :
    ∀ {xs : List α}, xs.Nodup →
      (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) →
      (xs.map f).Nodup := by
  intro xs hnd hinj
  induction xs with
  | nil => simp
  | cons a rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
        have hab := hinj a List.mem_cons_self b
          (List.mem_cons_of_mem _ hb) hfb.symm
        exact hnd.1 (hab ▸ hb)
      · exact ih hnd.2
          (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx)
            y (List.mem_cons_of_mem _ hy))

/-- The canonical active-lobe representatives are duplicate-free. -/
theorem canonicalActiveLobes_nodup
    {lo hi k0 : Nat} {slots : List Nat}
    (hnd : slots.Nodup) :
    (canonicalActiveLobes m e r0 lo hi slots k0).Nodup := by
  classical
  exact (canonicalSupportEdges_nodup m e r0 hnd k0).filter _

/-- Distinct canonical active lobes lie in distinct cells. -/
theorem canonicalActiveLobeCells_nodup
    {lo hi k0 : Nat} {slots : List Nat}
    (hnd : slots.Nodup) :
    (standaloneActiveLobeCells m
      (canonicalActiveLobes m e r0 lo hi slots k0)).Nodup := by
  unfold standaloneActiveLobeCells
  apply map_nodup_of_injective_on m.cellOf
    (canonicalActiveLobes_nodup m e r0 hnd)
  intro a ha b hb hcell
  have haData := (mem_canonicalActiveLobes_iff m e r0).mp ha
  have hbData := (mem_canonicalActiveLobes_iff m e r0).mp hb
  have haOcc := canonicalSupportEdges_occupied_at_ref m e r0
    slots k0 a haData.1
  have hbOcc := canonicalSupportEdges_occupied_at_ref m e r0
    slots k0 b hbData.1
  have hab := occupied_lobes_same_cell_sameEdge m e r0
    haData.2.1 hbData.2.1 haOcc hbOcc hcell
  exact canonicalSupport_sameEdge_eq m e r0
    haData.1 hbData.1 hab

/-- Every canonical active-lobe cell belongs to the represented cell list. -/
theorem canonicalActiveLobeCells_subset
    {lo hi k0 : Nat} {cells slots : List Nat}
    (frame : FiniteEpochFrame m e r0 lo hi cells slots) :
    ∀ c ∈ standaloneActiveLobeCells m
      (canonicalActiveLobes m e r0 lo hi slots k0), c ∈ cells := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  have haSupport :=
    ((mem_canonicalActiveLobes_iff m e r0).mp ha).1
  exact frame.slot_cell a
    (canonicalSupportEdge_mem_slots m e r0 haSupport)

/-- The represented universe contains each active lobe and its mouth partner. -/
theorem canonicalActiveLobeCells_closed
    {lo hi k0 : Nat} {cells slots : List Nat}
    (frame : FiniteEpochFrame m e r0 lo hi cells slots) :
    ∀ c ∈ standaloneActiveLobeCells m
      (canonicalActiveLobes m e r0 lo hi slots k0),
      c ∈ cells ∧ m.star c ∈ cells := by
  intro c hc
  have hsub := canonicalActiveLobeCells_subset m e r0 frame c hc
  exact ⟨hsub, frame.star_closed c hsub⟩

/-- Canonical active lobes are genuine loop edges. -/
theorem canonicalActiveLobes_loop
    {lo hi k0 : Nat} {slots : List Nat} :
    ∀ a ∈ canonicalActiveLobes m e r0 lo hi slots k0,
      m.cellOf (m.bar a) = m.cellOf a := by
  intro a ha
  exact ((mem_canonicalActiveLobes_iff m e r0).mp ha).2.1

/-- Canonical active lobes remain occupied throughout a fixed-support epoch. -/
theorem canonicalActiveLobes_occupied
    {lo hi k0 : Nat} {slots : List Nat}
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi) :
    ∀ k, lo ≤ k → k ≤ hi →
      ∀ a ∈ canonicalActiveLobes m e r0 lo hi slots k0,
        Occupied m e r0 k a := by
  intro k hkLo hkHi a ha
  have haSupport :=
    ((mem_canonicalActiveLobes_iff m e r0).mp ha).1
  have ha0 := canonicalSupportEdges_occupied_at_ref m e r0
    slots k0 a haSupport
  have hs := pairedSupportFixed_between m e r0 hfixed
    hk0.1 hk0.2 hkLo hkHi a
  exact hs.mp ha0

/-- Every canonical active lobe is visited during the interval. -/
theorem canonicalActiveLobes_visited
    {lo hi k0 : Nat} {slots : List Nat}
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi) :
    ∀ a ∈ canonicalActiveLobes m e r0 lo hi slots k0,
      StandaloneLobeVisited m e r0 lo hi a := by
  intro a ha
  have hdata := (mem_canonicalActiveLobes_iff m e r0).mp ha
  rcases hdata.2.2 with ⟨k, hkLo, hkHi, hkCell⟩
  have hocc := canonicalActiveLobes_occupied m e r0
    hfixed hk0 k (Nat.le_of_lt hkLo) hkHi a ha
  have hcases := standalone_occupied_lobe_cases m e r0
    hdata.2.1 hocc
  have hwrite : reg m e r0 k (m.cellOf a) = e k := by
    rw [← hkCell]
    exact reg_write m e r0 rfl
  refine ⟨k, Nat.le_of_lt hkLo, hkHi, ?_⟩
  rcases hcases with hcases | hcases
  · exact Or.inl (hwrite.symm.trans hcases)
  · exact Or.inr (hwrite.symm.trans hcases)

/-- An occupied lobe edge in a represented cell has an endpoint in the finite
slot list. -/
theorem occupied_lobe_mem_slots
    {lo hi k c a : Nat} {cells slots : List Nat}
    (frame : FiniteEpochFrame m e r0 lo hi cells slots)
    (hkLo : lo ≤ k) (hkHi : k ≤ hi)
    (hc : c ∈ cells)
    (haCell : m.cellOf a = c)
    (haLoop : m.cellOf (m.bar a) = c)
    (haOcc : Occupied m e r0 k a) :
    a ∈ slots := by
  have hloop : m.cellOf (m.bar a) = m.cellOf a := by
    rw [haCell]
    exact haLoop
  have hcases := standalone_occupied_lobe_cases m e r0 hloop haOcc
  rw [haCell] at hcases
  have hsel := frame.selected k hkLo hkHi c hc
  rcases hcases with hcases | hcases
  · rw [hcases] at hsel
    exact hsel
  · rw [hcases] at hsel
    have hb := frame.bar_closed (m.bar a) hsel
    simpa only [m.bar_invol] using hb

/-- Any written cell with an occupied lobe at the reference time has a
canonical active-lobe representative. -/
theorem exists_canonicalActiveLobe
    {lo hi k0 c a : Nat} {cells slots : List Nat}
    (frame : FiniteEpochFrame m e r0 lo hi cells slots)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi)
    (hc : c ∈ cells)
    (haCell : m.cellOf a = c)
    (haLoop : m.cellOf (m.bar a) = c)
    (haOcc : Occupied m e r0 k0 a)
    (hw : CellWrittenIn m e r0 lo hi c) :
    ∃ g, g ∈ canonicalActiveLobes m e r0 lo hi slots k0 ∧
      m.cellOf g = c := by
  have haSlots := occupied_lobe_mem_slots m e r0 frame
    hk0.1 hk0.2 hc haCell haLoop haOcc
  rcases slot_has_canonicalEdgeCore m frame.bar_closed frame.bar_ne
      haSlots with ⟨g, hg, hag⟩
  have hgOcc : Occupied m e r0 k0 g :=
    (occupied_sameEdge_iff m e r0 hag).mp haOcc
  have hgSupport : g ∈ canonicalSupportEdges m e r0 slots k0 := by
    classical
    exact List.mem_filter.mpr ⟨hg, hgOcc⟩
  have haLobe : m.cellOf (m.bar a) = m.cellOf a := by
    rw [haCell]
    exact haLoop
  have hgLobe := lobe_of_sameEdge m hag haLobe
  have hgCell : m.cellOf g = c := by
    exact (cell_eq_of_sameEdge_lobe m hag haLobe).trans haCell
  have hwg : CellWrittenIn m e r0 lo hi (m.cellOf g) := by
    rw [hgCell]
    exact hw
  refine ⟨g, ?_, hgCell⟩
  exact (mem_canonicalActiveLobes_iff m e r0).mpr
    ⟨hgSupport, hgLobe, hwg⟩

/-- **The canonical active-lobe list gives a complete support-relative replay
cover.** -/
theorem canonical_support_replay_cover
    {lo hi k0 : Nat} {cells slots : List Nat}
    (frame : FiniteEpochFrame m e r0 lo hi cells slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi) :
    PairedSupportReplayCover m e r0 lo hi cells
      (canonicalActiveLobes m e r0 lo hi slots k0) := by
  intro c hc
  by_cases hw : CellWrittenIn m e r0 lo hi c
  · by_cases hlobe : ∃ a,
        m.cellOf a = c ∧ m.cellOf (m.bar a) = c ∧
          Occupied m e r0 k0 a
    · rcases hlobe with ⟨a, haCell, haLoop, haOcc⟩
      rcases exists_canonicalActiveLobe m e r0 frame hk0 hc
          haCell haLoop haOcc hw with ⟨g, hg, hgc⟩
      exact Or.inl ⟨g, hg, hgc⟩
    · apply Or.inr
      apply Or.inl
      intro k hkLo hkHi s hsCell hsLoop hsOcc
      have hsupport := pairedSupportFixed_between m e r0 hfixed
        hk0.1 hk0.2 hkLo hkHi s
      have hs0 : Occupied m e r0 k0 s := hsupport.mpr hsOcc
      exact hlobe ⟨s, hsCell, hsLoop, hs0⟩
  · exact Or.inr (Or.inr
      (pairedPointFrozen_of_noWrite m e r0 hw))

end Echo
