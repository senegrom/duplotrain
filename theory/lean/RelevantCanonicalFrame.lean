import RelevantFiniteFrame
import CanonicalProjectedEpochFrame

/-!
# Canonical strict epochs from a relevant finite frame

The canonical active-lobe and projected-coordinate construction only needs a
finite selected-register frame.  The former global `confirmed_cell` field was
used in two places:

1. to show a full edge is represented; and
2. to show an endpoint of an already represented projected edge has a listed
   cell.

For (1) it suffices to assume that full edges have relevant cells.  For (2)
the endpoint is already in the bar-closed slot list, so `slot_cell` proves the
claim directly.  This file supplies those corrected versions and recovers the
same per-epoch strict bound from a constructible relevant subsystem.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Relevant frames used for canonical edge representatives have no fixed
points of `bar` on their finite physical slot universe. -/
structure ProperRelevantFiniteFrame (cells slots : List Nat)
    extends RelevantFiniteFrame m e r0 cells slots where
  bar_ne : ∀ s ∈ slots, m.bar s ≠ s

/-- A proper relevant frame supplies the older finite selected-register frame
on every interval. -/
def ProperRelevantFiniteFrame.toFiniteEpochFrame
    {cells slots : List Nat}
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (lo hi : Nat) : FiniteEpochFrame m e r0 lo hi cells slots where
  cells_nodup := frame.cells_nodup
  slots_nodup := frame.slots_nodup
  star_closed := frame.star_closed
  bar_closed := frame.bar_closed
  bar_ne := frame.bar_ne
  slot_cell := frame.slot_cell
  selected := fun k hkLo hkHi c hc =>
    relevant_reg_mem m e r0 frame.toRelevantFiniteFrame k c hc

/-- Every full edge occurring in an interval belongs to a relevant cell. -/
def FullEdgesRelevant
    (lo hi : Nat) (cells : List Nat) : Prop :=
  ∀ k, lo ≤ k → k ≤ hi →
    ∀ f, Full m e r0 k f → m.cellOf f ∈ cells

/-- A confirmed slot of a relevant cell belongs to the finite slot list. -/
theorem confirmed_slot_mem_relevant
    {cells slots : List Nat}
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    {k x : Nat}
    (hc : m.cellOf x ∈ cells)
    (hconf : Confirmed m e r0 k x) : x ∈ slots := by
  have hmem := relevant_reg_mem m e r0
    frame.toRelevantFiniteFrame k (m.cellOf x) hc
  unfold Confirmed at hconf
  rwa [hconf] at hmem

/-- Every full edge is represented by the canonical projected support edges,
provided full edges are relevant. -/
theorem relevant_canonicalProjected_allFull_represented
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi k0 : Nat} {cells slots : List Nat}
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0 lo hi cells)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi) :
    PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi)
      (canonicalProjectedEdges m e r0 lo hi slots k0) := by
  intro k hk f hfull
  have hfCell := hfullRelevant k hk.1 hk.2 f hfull
  have hfSlot := confirmed_slot_mem_relevant
    m e r0 frame hfCell hfull.1
  rcases slot_has_canonicalEdgeCore m frame.bar_closed frame.bar_ne
      hfSlot with ⟨g, hg, hfg⟩
  have hfOcc : Occupied m e r0 k f := Or.inl hfull.1
  have hgOccK : Occupied m e r0 k g :=
    (occupied_sameEdge_iff m e r0 hfg).mp hfOcc
  have hs := pairedSupportFixed_between m e r0 hfixed
    hk0.1 hk0.2 hk.1 hk.2 g
  have hgOcc0 : Occupied m e r0 k0 g := hs.mpr hgOccK
  have hgSupport : g ∈ canonicalSupportEdges m e r0 slots k0 := by
    classical
    exact List.mem_filter.mpr ⟨hg, decide_eq_true hgOcc0⟩
  have hgNotActive :
      g ∉ canonicalActiveLobes m e r0 lo hi slots k0 := by
    intro hga
    have hgLoop :=
      ((mem_canonicalActiveLobes_iff m e r0).mp hga).2.1
    have hgFull := pairedFull_of_sameEdge m e r0 hfg hfull
    have hgSlot := canonicalSupportEdge_mem_slots m e r0 hgSupport
    exact (lobe_not_full_of_bar_ne m e r0
      (frame.bar_ne g hgSlot) hgLoop) hgFull
  exact ⟨g,
    (mem_canonicalProjectedEdges_iff m e r0).mpr
      ⟨hgSupport, hgNotActive⟩,
    hfg⟩

/-- Every projected register is represented, using only finite selected
register closure. -/
theorem relevant_canonicalProjected_selected
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi k0 : Nat} {cells slots : List Nat}
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi) :
    ∀ k, lo ≤ k → k ≤ hi →
      ∀ c ∈ canonicalProjectedCells m e r0 lo hi cells slots k0,
        reg m e r0 k c ∈ standaloneEdgeEnds m
          (canonicalProjectedEdges m e r0 lo hi slots k0) := by
  intro k hkLo hkHi c hc
  have hcData := (mem_canonicalProjectedCells_iff m e r0).mp hc
  let s := reg m e r0 k c
  have hsSlot : s ∈ slots := by
    dsimp [s]
    exact relevant_reg_mem m e r0 frame.toRelevantFiniteFrame
      k c hcData.1
  rcases slot_has_canonicalEdgeCore m frame.bar_closed frame.bar_ne
      hsSlot with ⟨g, hg, hsg⟩
  have hsConf : Confirmed m e r0 k s := by
    dsimp [s]
    exact old_register_confirmed m e r0 hr0 k c
  have hsOcc : Occupied m e r0 k s := Or.inl hsConf
  have hgOccK : Occupied m e r0 k g :=
    (occupied_sameEdge_iff m e r0 hsg).mp hsOcc
  have hsupport := pairedSupportFixed_between m e r0 hfixed
    hk0.1 hk0.2 hkLo hkHi g
  have hgOcc0 : Occupied m e r0 k0 g := hsupport.mpr hgOccK
  have hgSupport : g ∈ canonicalSupportEdges m e r0 slots k0 := by
    classical
    exact List.mem_filter.mpr ⟨hg, decide_eq_true hgOcc0⟩
  have hgNotActive :
      g ∉ canonicalActiveLobes m e r0 lo hi slots k0 := by
    intro hga
    have hgLoop :=
      ((mem_canonicalActiveLobes_iff m e r0).mp hga).2.1
    have hgs : SameEdge m g s := sameEdge_symm m hsg
    have hcellGS := cell_eq_of_sameEdge_lobe m hgs hgLoop
    have hsCell : m.cellOf s = c := by
      dsimp [s]
      exact reg_cell m e r0 hr0 k c
    have hgCell : m.cellOf g = c := hcellGS.symm.trans hsCell
    apply hcData.2
    exact List.mem_map.mpr ⟨g, hga, hgCell⟩
  have hgProjected :
      g ∈ canonicalProjectedEdges m e r0 lo hi slots k0 :=
    (mem_canonicalProjectedEdges_iff m e r0).mpr
      ⟨hgSupport, hgNotActive⟩
  have hends := core_rep_endpoints_mem m hgProjected
  rcases hsg with hsg | hsg
  · simpa [s, hsg] using hends.1
  · have hb := congrArg m.bar hsg
    have hbar : m.bar g = s := by
      simpa only [m.bar_invol] using hb
    simpa [s, hbar] using hends.2

/-- Confirmed endpoints of represented projected edges have projected cells,
without any global finite-confirmed-cell assumption. -/
theorem relevant_canonicalProjected_confirmed_cell
    {lo hi k0 : Nat} {cells slots : List Nat}
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi) :
    ∀ k, lo ≤ k → k ≤ hi →
      ∀ x ∈ standaloneEdgeEnds m
        (canonicalProjectedEdges m e r0 lo hi slots k0),
        Confirmed m e r0 k x →
        m.cellOf x ∈ canonicalProjectedCells m e r0
          lo hi cells slots k0 := by
  intro k hkLo hkHi x hx hconf
  rcases core_mem_edgeEnds_cases m hx with
    ⟨g, hgProjected, hxg⟩
  have hgData :=
    (mem_canonicalProjectedEdges_iff m e r0).mp hgProjected
  have hgSlot := canonicalSupportEdge_mem_slots
    m e r0 hgData.1
  have hxSlot : x ∈ slots := by
    rcases hxg with hxg | hxg
    · rw [← hxg]
      exact hgSlot
    · rw [← hxg]
      exact frame.bar_closed g hgSlot
  have hxCell : m.cellOf x ∈ cells := frame.slot_cell x hxSlot
  apply (mem_canonicalProjectedCells_iff m e r0).mpr
  refine ⟨hxCell, ?_⟩
  intro hxActive
  obtain ⟨a, ha, haCell⟩ := List.mem_map.mp hxActive
  have haData := (mem_canonicalActiveLobes_iff m e r0).mp ha
  have haOcc := canonicalActiveLobes_occupied m e r0
    hfixed hk0 k hkLo hkHi a ha
  have hgx : SameEdge m g x := by
    rcases hxg with hxg | hxg
    · exact Or.inl hxg.symm
    · exact Or.inr hxg.symm
  have hga : SameEdge m g a := by
    rcases haOcc with haConf | hbarConf
    · have hxa : x = a :=
        confirmed_same_cell_eq m e r0 hconf haConf haCell.symm
      have hxaEdge : SameEdge m x a := by
        rw [hxa]
        exact Or.inl rfl
      exact sameEdge_trans_projected m hgx hxaEdge
    · have hloop := haData.2.1
      have hcellBar : m.cellOf x = m.cellOf (m.bar a) := by
        calc
          m.cellOf x = m.cellOf a := haCell.symm
          _ = m.cellOf (m.bar a) := hloop.symm
      have hxb : x = m.bar a :=
        confirmed_same_cell_eq m e r0 hconf hbarConf hcellBar
      have hxaEdge : SameEdge m x a := by
        rw [hxb]
        exact sameEdge_symm m (sameEdge_bar m a)
      exact sameEdge_trans_projected m hgx hxaEdge
  have hgaEq := canonicalSupport_sameEdge_eq m e r0
    hgData.1 haData.1 hga
  apply hgData.2
  rw [hgaEq]
  exact ha

/-- Relevant projected support edges remain occupied throughout the epoch. -/
theorem relevant_canonicalProjectedEdges_occupied
    {lo hi k0 : Nat} {slots : List Nat}
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi) :
    ∀ k, lo ≤ k → k ≤ hi →
      ∀ s ∈ canonicalProjectedEdges m e r0 lo hi slots k0,
        Occupied m e r0 k s :=
  canonicalProjectedEdges_occupied m e r0 hfixed hk0

/-- **Constructible canonical pre-absorption epoch bound.** -/
theorem relevant_canonical_preAbsorption_epoch_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi k0 : Nat)
    (cells slots ks : List Nat)
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0 lo hi cells)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi)
    (hnoTail : StandaloneNoFourTailIn m e r0 lo hi)
    (hks : ∀ k ∈ ks, lo ≤ k ∧ k ≤ hi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    blockCoreEighth ks.length ≤ 2^(7*cells.length+18) := by
  let finiteFrame := frame.toFiniteEpochFrame lo hi
  let lobes := canonicalActiveLobes m e r0 lo hi slots k0
  let projected := canonicalProjectedCells m e r0
    lo hi cells slots k0
  let edges := canonicalProjectedEdges m e r0 lo hi slots k0
  apply support_relative_preAbsorption_epoch_bound m e r0
    hrun hr0 lo hi cells projected edges lobes ks hfixed
  · dsimp [edges]
    exact relevant_canonicalProjected_allFull_represented
      m e r0 hr0 frame hfullRelevant hfixed hk0
  · dsimp [lobes]
    exact canonical_support_replay_cover m e r0
      finiteFrame hfixed hk0
  · dsimp [lobes, projected]
    exact canonicalProjectedCells_length m e r0 finiteFrame
  · exact frame.cells_nodup
  · dsimp [projected]
    exact canonicalProjectedCells_nodup m e r0 frame.cells_nodup
  · dsimp [edges]
    exact canonicalProjectedEdgeEnds_nodup m e r0 frame.slots_nodup
  · dsimp [projected, edges]
    exact relevant_canonicalProjected_selected
      m e r0 hr0 frame hfixed hk0
  · dsimp [projected, edges]
    exact relevant_canonicalProjected_confirmed_cell
      m e r0 frame hfixed hk0
  · dsimp [edges]
    exact relevant_canonicalProjectedEdges_occupied
      m e r0 hfixed hk0
  · dsimp [lobes]
    exact canonicalActiveLobeCells_nodup m e r0 frame.slots_nodup
  · dsimp [lobes]
    exact canonicalActiveLobeCells_closed m e r0 finiteFrame
  · dsimp [lobes]
    exact canonicalActiveLobes_loop m e r0
  · dsimp [lobes]
    exact canonicalActiveLobes_occupied m e r0 hfixed hk0
  · dsimp [lobes]
    exact canonicalActiveLobes_visited m e r0 hfixed hk0
  · exact hnoTail
  · exact hks
  · exact hnd

end Echo
