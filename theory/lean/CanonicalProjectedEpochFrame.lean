import CanonicalActiveLobeFrame
import SupportRelativeEpochStrictBound

/-!
# Canonical projected cells and edges

Remove the canonically active lobe cells from the represented cell universe,
and remove the corresponding lobe edges from the common occupied support.
Everything required by endpoint accounting is then automatic:

* projected cells and projected edge endpoints are duplicate-free;
* every projected register is represented;
* every full edge is represented;
* confirmed projected-edge endpoints lie in projected cells; and
* the active-lobe/projected-cell lengths partition the whole universe.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A finite epoch frame which also certifies that every confirmed slot belongs
to the represented cell universe. -/
structure CompleteFiniteEpochFrame
    (lo hi : Nat) (cells slots : List Nat)
    extends FiniteEpochFrame m e r0 lo hi cells slots where
  confirmed_cell : ∀ k, lo ≤ k → k ≤ hi → ∀ x,
    Confirmed m e r0 k x → m.cellOf x ∈ cells

/-- A confirmed slot in a complete frame lies in the finite slot universe. -/
theorem completeFrame_confirmed_slot
    {lo hi k x : Nat} {cells slots : List Nat}
    (frame : CompleteFiniteEpochFrame m e r0 lo hi cells slots)
    (hkLo : lo ≤ k) (hkHi : k ≤ hi)
    (hconf : Confirmed m e r0 k x) :
    x ∈ slots := by
  have hc := frame.confirmed_cell k hkLo hkHi x hconf
  have hs := frame.selected k hkLo hkHi (m.cellOf x) hc
  unfold Confirmed at hconf
  rw [hconf] at hs
  exact hs

/-- Cells not represented by a canonical active lobe. -/
open Classical in
noncomputable def canonicalProjectedCells
    (lo hi : Nat) (cells slots : List Nat) (k0 : Nat) : List Nat :=
  cells.filter fun c =>
    c ∉ standaloneActiveLobeCells m
      (canonicalActiveLobes m e r0 lo hi slots k0)

/-- Common support edges other than the canonical active lobes. -/
open Classical in
noncomputable def canonicalProjectedEdges
    (lo hi : Nat) (slots : List Nat) (k0 : Nat) : List Nat :=
  (canonicalSupportEdges m e r0 slots k0).filter fun s =>
    s ∉ canonicalActiveLobes m e r0 lo hi slots k0

theorem mem_canonicalProjectedCells_iff
    {lo hi k0 c : Nat} {cells slots : List Nat} :
    c ∈ canonicalProjectedCells m e r0 lo hi cells slots k0 ↔
      c ∈ cells ∧
      c ∉ standaloneActiveLobeCells m
        (canonicalActiveLobes m e r0 lo hi slots k0) := by
  classical
  simp [canonicalProjectedCells]

theorem mem_canonicalProjectedEdges_iff
    {lo hi k0 s : Nat} {slots : List Nat} :
    s ∈ canonicalProjectedEdges m e r0 lo hi slots k0 ↔
      s ∈ canonicalSupportEdges m e r0 slots k0 ∧
      s ∉ canonicalActiveLobes m e r0 lo hi slots k0 := by
  classical
  simp [canonicalProjectedEdges]

private theorem nodup_subset_length_projected
    {xs ys : List Nat}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ ys.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

private theorem filter_partition_length
    (p : Nat → Prop) [DecidablePred p] :
    ∀ xs : List Nat,
      (xs.filter p).length +
        (xs.filter (fun x => ¬ p x)).length = xs.length := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      by_cases hx : p x <;> simp [hx, ih]

private theorem active_filter_length
    {cells active : List Nat}
    (hcells : cells.Nodup)
    (hactive : active.Nodup)
    (hsub : ∀ c ∈ active, c ∈ cells) :
    (cells.filter (fun c => c ∈ active)).length = active.length := by
  classical
  have hfilterNodup :
      (cells.filter (fun c => c ∈ active)).Nodup :=
    hcells.filter _
  have hto : ∀ c ∈ active,
      c ∈ cells.filter (fun c => c ∈ active) := by
    intro c hc
    exact List.mem_filter.mpr ⟨hsub c hc, hc⟩
  have hfrom : ∀ c ∈ cells.filter (fun c => c ∈ active),
      c ∈ active := by
    intro c hc
    exact (List.mem_filter.mp hc).2
  have hle1 := nodup_subset_length_projected hactive hto
  have hle2 := nodup_subset_length_projected hfilterNodup hfrom
  omega

/-- Projected cells are duplicate-free. -/
theorem canonicalProjectedCells_nodup
    {lo hi k0 : Nat} {cells slots : List Nat}
    (hnd : cells.Nodup) :
    (canonicalProjectedCells m e r0 lo hi cells slots k0).Nodup := by
  classical
  exact hnd.filter _

/-- Active-lobe cells and projected cells partition the represented universe. -/
theorem canonicalProjectedCells_length
    {lo hi k0 : Nat} {cells slots : List Nat}
    (frame : FiniteEpochFrame m e r0 lo hi cells slots) :
    cells.length =
      (canonicalActiveLobes m e r0 lo hi slots k0).length +
      (canonicalProjectedCells m e r0 lo hi cells slots k0).length := by
  classical
  let active := standaloneActiveLobeCells m
    (canonicalActiveLobes m e r0 lo hi slots k0)
  have hactiveNodup : active.Nodup := by
    dsimp [active]
    exact canonicalActiveLobeCells_nodup m e r0 frame.slots_nodup
  have hactiveSub : ∀ c ∈ active, c ∈ cells := by
    dsimp [active]
    exact canonicalActiveLobeCells_subset m e r0 frame
  have hpositive := active_filter_length frame.cells_nodup
    hactiveNodup hactiveSub
  have hsplit := filter_partition_length
    (fun c => c ∈ active) cells
  have hactiveLen : active.length =
      (canonicalActiveLobes m e r0 lo hi slots k0).length := by
    simp [active, standaloneActiveLobeCells]
  dsimp [canonicalProjectedCells]
  change cells.length =
    (canonicalActiveLobes m e r0 lo hi slots k0).length +
      (cells.filter (fun c => c ∉ active)).length
  omega

/-- Projected edge representatives remain ordered and duplicate-free. -/
theorem canonicalProjectedEdgeEnds_nodup
    {lo hi k0 : Nat} {slots : List Nat}
    (hnd : slots.Nodup) :
    (standaloneEdgeEnds m
      (canonicalProjectedEdges m e r0 lo hi slots k0)).Nodup := by
  apply orderedEdgeEndsCore_nodup m
    (canonicalProjectedEdges m e r0 lo hi slots k0)
  · classical
    exact (canonicalSupportEdges_nodup m e r0 hnd k0).filter _
  · intro s hs
    have hsSupport :=
      ((mem_canonicalProjectedEdges_iff m e r0).mp hs).1
    exact canonicalSupportEdges_ordered m e r0 slots k0 s hsSupport

/-- A distinct-endpoint lobe edge cannot be full. -/
theorem lobe_not_full_of_bar_ne
    {k s : Nat}
    (hne : m.bar s ≠ s)
    (hloop : m.cellOf (m.bar s) = m.cellOf s) :
    ¬ Full m e r0 k s := by
  intro hfull
  have heq : m.bar s = s :=
    confirmed_same_cell_eq m e r0 hfull.2 hfull.1 hloop
  exact hne heq

/-- Every full edge is represented by a projected support edge. -/
theorem canonicalProjected_allFull_represented
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi k0 : Nat} {cells slots : List Nat}
    (frame : CompleteFiniteEpochFrame m e r0 lo hi cells slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi) :
    PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi)
      (canonicalProjectedEdges m e r0 lo hi slots k0) := by
  intro k hk f hfull
  have hfSlot := completeFrame_confirmed_slot m e r0 frame
    hk.1 hk.2 hfull.1
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
    exact List.mem_filter.mpr ⟨hg, hgOcc0⟩
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

/-- Every projected register is represented by a projected support edge. -/
theorem canonicalProjected_selected
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi k0 : Nat} {cells slots : List Nat}
    (frame : CompleteFiniteEpochFrame m e r0 lo hi cells slots)
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
    exact frame.selected k hkLo hkHi c hcData.1
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
    exact List.mem_filter.mpr ⟨hg, hgOcc0⟩
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
  · rw [hsg]
    exact hends.1
  · have hb := congrArg m.bar hsg
    have hbar : m.bar g = s := by
      simpa only [m.bar_invol] using hb
    rw [← hbar]
    exact hends.2

/-- Same-edge is transitive, locally for the endpoint argument below. -/
theorem sameEdge_trans_projected
    {a b c : Nat}
    (hab : SameEdge m a b) (hbc : SameEdge m b c) :
    SameEdge m a c := by
  rcases hab with hab | hab
  · subst b
    exact hbc
  · rcases hbc with hbc | hbc
    · exact Or.inr (hbc.trans hab)
    · left
      calc
        c = m.bar b := hbc
        _ = m.bar (m.bar a) := by rw [hab]
        _ = a := m.bar_invol a

/-- Confirmed projected-edge endpoints belong to projected cells. -/
theorem canonicalProjected_confirmed_cell
    {lo hi k0 : Nat} {cells slots : List Nat}
    (frame : CompleteFiniteEpochFrame m e r0 lo hi cells slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi) :
    ∀ k, lo ≤ k → k ≤ hi →
      ∀ x ∈ standaloneEdgeEnds m
        (canonicalProjectedEdges m e r0 lo hi slots k0),
        Confirmed m e r0 k x →
        m.cellOf x ∈ canonicalProjectedCells m e r0
          lo hi cells slots k0 := by
  intro k hkLo hkHi x hx hconf
  have hxCell : m.cellOf x ∈ cells :=
    frame.confirmed_cell k hkLo hkHi x hconf
  apply (mem_canonicalProjectedCells_iff m e r0).mpr
  refine ⟨hxCell, ?_⟩
  intro hxActive
  obtain ⟨a, ha, haCell⟩ := List.mem_map.mp hxActive
  have haData := (mem_canonicalActiveLobes_iff m e r0).mp ha
  have haOcc := canonicalActiveLobes_occupied m e r0
    hfixed hk0 k hkLo hkHi a ha
  rcases core_mem_edgeEnds_cases m hx with
    ⟨g, hgProjected, hxg⟩
  have hgData := (mem_canonicalProjectedEdges_iff m e r0).mp
    hgProjected
  have hgx : SameEdge m g x := by
    rcases hxg with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
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

/-- Projected support edges remain occupied throughout the epoch. -/
theorem canonicalProjectedEdges_occupied
    {lo hi k0 : Nat} {slots : List Nat}
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi) :
    ∀ k, lo ≤ k → k ≤ hi →
      ∀ s ∈ canonicalProjectedEdges m e r0 lo hi slots k0,
        Occupied m e r0 k s := by
  intro k hkLo hkHi s hs
  have hsSupport :=
    ((mem_canonicalProjectedEdges_iff m e r0).mp hs).1
  have hs0 := canonicalSupportEdges_occupied_at_ref m e r0
    slots k0 s hsSupport
  have hsupport := pairedSupportFixed_between m e r0 hfixed
    hk0.1 hk0.2 hkLo hkHi s
  exact hsupport.mp hs0

/-- **Completely canonical strict bound for one pre-absorption fixed-support
epoch.**  No edge list, active-lobe list, projected-cell list, or replay cover
is supplied by the caller. -/
theorem canonical_preAbsorption_epoch_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi k0 : Nat)
    (cells slots ks : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0 lo hi cells slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi)
    (hnoTail : StandaloneNoFourTailIn m e r0 lo hi)
    (hks : ∀ k ∈ ks, lo ≤ k ∧ k ≤ hi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    blockCoreEighth ks.length ≤ 2^(7*cells.length+18) := by
  let lobes := canonicalActiveLobes m e r0 lo hi slots k0
  let projected := canonicalProjectedCells m e r0
    lo hi cells slots k0
  let edges := canonicalProjectedEdges m e r0 lo hi slots k0
  apply support_relative_preAbsorption_epoch_bound m e r0
    hrun hr0 lo hi cells projected edges lobes ks hfixed
  · dsimp [edges]
    exact canonicalProjected_allFull_represented m e r0 hr0
      frame hfixed hk0
  · dsimp [lobes]
    exact canonical_support_replay_cover m e r0
      frame.toFiniteEpochFrame hfixed hk0
  · dsimp [lobes, projected]
    exact canonicalProjectedCells_length m e r0
      frame.toFiniteEpochFrame
  · exact frame.cells_nodup
  · dsimp [projected]
    exact canonicalProjectedCells_nodup m e r0 frame.cells_nodup
  · dsimp [edges]
    exact canonicalProjectedEdgeEnds_nodup m e r0
      frame.slots_nodup
  · dsimp [projected, edges]
    exact canonicalProjected_selected m e r0 hr0 frame hfixed hk0
  · dsimp [projected, edges]
    exact canonicalProjected_confirmed_cell m e r0 frame hfixed hk0
  · dsimp [edges]
    exact canonicalProjectedEdges_occupied m e r0 hfixed hk0
  · dsimp [lobes]
    exact canonicalActiveLobeCells_nodup m e r0
      frame.slots_nodup
  · dsimp [lobes]
    exact canonicalActiveLobeCells_closed m e r0
      frame.toFiniteEpochFrame
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
