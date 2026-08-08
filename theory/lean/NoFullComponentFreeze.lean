import EndpointAccountingStandalone
import NoFullFreezeCore

/-!
# A no-full support component is frozen

Endpoint accounting makes the number of full edges in a finite represented
component equal to `V-E`, hence constant while its support is fixed.  If the
component has no full edge at one time, it has none throughout the epoch.
The one-step no-full/non-lobe lemma then freezes every register in the
component.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Fullness is independent of which endpoint represents an edge. -/
theorem full_bar_iff (k s : Nat) :
    Full m e r0 k (m.bar s) ↔ Full m e r0 k s := by
  unfold Full
  rw [m.bar_invol]
  exact and_comm

/-- Endpoint-list membership identifies a represented edge. -/
theorem mem_standaloneEdgeEnds_cases {edges : List Nat} {x : Nat} :
    x ∈ standaloneEdgeEnds m edges →
      ∃ s, s ∈ edges ∧ (x = s ∨ x = m.bar s) := by
  induction edges with
  | nil => simp [standaloneEdgeEnds]
  | cons s rest ih =>
      intro hx
      simp only [standaloneEdgeEnds, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨s, List.mem_cons_self, Or.inl rfl⟩
      · rcases hx with rfl | hx
        · exact ⟨s, List.mem_cons_self, Or.inr rfl⟩
        · rcases ih hx with ⟨t, ht, hxt⟩
          exact ⟨t, List.mem_cons_of_mem _ ht, hxt⟩

/-- Zero full-bit count means no represented edge is full. -/
theorem noFull_of_endpointTrueCount_zero
    (edges : List Nat) (k : Nat)
    (hzero : endpointTrueCount
      (endpointFullBits m e r0 edges k) = 0) :
    ∀ s ∈ edges, ¬ Full m e r0 k s := by
  classical
  induction edges with
  | nil => simp
  | cons s rest ih =>
      simp only [endpointFullBits, List.map_cons,
        endpointTrueCount] at hzero
      by_cases hs : Full m e r0 k s
      · simp [hs] at hzero
      · have hrest : endpointTrueCount
            (endpointFullBits m e r0 rest k) = 0 := by
          simp [hs] at hzero
          exact hzero
        intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hs
        · exact ih hrest t ht

/-- Conversely, if no represented edge is full, the count is zero. -/
theorem endpointTrueCount_zero_of_noFull
    (edges : List Nat) (k : Nat)
    (hnone : ∀ s ∈ edges, ¬ Full m e r0 k s) :
    endpointTrueCount (endpointFullBits m e r0 edges k) = 0 := by
  classical
  induction edges with
  | nil => rfl
  | cons s rest ih =>
      have hs := hnone s List.mem_cons_self
      have hrest : ∀ t ∈ rest, ¬ Full m e r0 k t := by
        intro t ht
        exact hnone t (List.mem_cons_of_mem _ ht)
      simp [endpointFullBits, endpointTrueCount, hs, ih hrest]

/-- Uniform finite representation of one support component over an interval. -/
structure ComponentInterval (lo hi : Nat) where
  cells : List Nat
  edges : List Nat
  cells_nodup : cells.Nodup
  ends_nodup : (standaloneEdgeEnds m edges).Nodup
  selected : ∀ k, lo ≤ k → k ≤ hi → ∀ c ∈ cells,
    reg m e r0 k c ∈ standaloneEdgeEnds m edges
  confirmed_cells : ∀ k, lo ≤ k → k ≤ hi →
    ∀ x ∈ standaloneEdgeEnds m edges,
      Confirmed m e r0 k x → m.cellOf x ∈ cells
  occupied : ∀ k, lo ≤ k → k ≤ hi → ∀ s ∈ edges,
    Occupied m e r0 k s
  support_step : ∀ k, lo ≤ k → k < hi → ∀ s,
    Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s

/-- Endpoint accounting gives the same full-edge count at all interval times. -/
theorem ComponentInterval.fullCount_eq
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat}
    (comp : ComponentInterval m e r0 lo hi)
    {i j : Nat}
    (hiLo : lo ≤ i) (hiHi : i ≤ hi)
    (hjLo : lo ≤ j) (hjHi : j ≤ hi) :
    endpointTrueCount (endpointFullBits m e r0 comp.edges i) =
      endpointTrueCount (endpointFullBits m e r0 comp.edges j) := by
  have hai := endpoint_accounting_standalone m e r0 hr0
    comp.cells comp.edges i comp.cells_nodup comp.ends_nodup
    (comp.selected i hiLo hiHi)
    (comp.confirmed_cells i hiLo hiHi)
    (comp.occupied i hiLo hiHi)
  have haj := endpoint_accounting_standalone m e r0 hr0
    comp.cells comp.edges j comp.cells_nodup comp.ends_nodup
    (comp.selected j hjLo hjHi)
    (comp.confirmed_cells j hjLo hjHi)
    (comp.occupied j hjLo hjHi)
  omega

/-- If the represented edges are not full, then no selected edge of a listed
cell is full. -/
theorem ComponentInterval.coreNoFull_of_edges
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi k : Nat}
    (comp : ComponentInterval m e r0 lo hi)
    (hkLo : lo ≤ k) (hkHi : k ≤ hi)
    (hnone : ∀ s ∈ comp.edges, ¬ Full m e r0 k s) :
    ∀ c ∈ comp.cells, CoreNoFull m e r0 k c := by
  intro c hc x hxc hfull
  have hxConfirmed : Confirmed m e r0 k x := hfull.1
  have hxreg : reg m e r0 k c = x := by
    unfold Confirmed at hxConfirmed
    rw [hxc] at hxConfirmed
    exact hxConfirmed
  have hxEnds : x ∈ standaloneEdgeEnds m comp.edges := by
    rw [← hxreg]
    exact comp.selected k hkLo hkHi c hc
  rcases mem_standaloneEdgeEnds_cases m hxEnds with
    ⟨s, hs, rfl | rfl⟩
  · exact hnone s hs hfull
  · exact hnone s hs ((full_bar_iff m e r0 k s).mp hfull)

/-- **A represented no-full non-lobe component is frozen across the interval.** -/
theorem component_snap_frozen
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat}
    (hlohi : lo ≤ hi)
    (comp : ComponentInterval m e r0 lo hi)
    (hnoneLo : ∀ s ∈ comp.edges, ¬ Full m e r0 lo s)
    (hnlobe : ∀ c ∈ comp.cells, CoreNoLobe m c) :
    snap m e r0 comp.cells hi = snap m e r0 comp.cells lo := by
  have hzeroLo := endpointTrueCount_zero_of_noFull m e r0
    comp.edges lo hnoneLo
  obtain ⟨d, rfl⟩ : ∃ d, hi = lo + d :=
    ⟨hi-lo, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
      have hkLo : lo ≤ lo+d := by omega
      have hkHi : lo+d ≤ lo+(d+1) := by omega
      have hkLt : lo+d < lo+(d+1) := by omega
      have hcount := comp.fullCount_eq hr0
        (i := lo) (j := lo+d)
        (by omega) (by omega) hkLo hkHi
      have hzeroK : endpointTrueCount
          (endpointFullBits m e r0 comp.edges (lo+d)) = 0 := by
        rw [← hcount]
        exact hzeroLo
      have hnoneK := noFull_of_endpointTrueCount_zero m e r0
        comp.edges (lo+d) hzeroK
      have hcore := comp.coreNoFull_of_edges hr0
        hkLo hkHi hnoneK
      have hstep := snap_step_eq_of_coreNoFull_coreNoLobe m e r0
        hrun hr0 (lo+d) comp.cells
        (comp.support_step (lo+d) hkLo hkLt)
        hcore hnlobe
      calc
        snap m e r0 comp.cells (lo + (d+1))
            = snap m e r0 comp.cells (lo+d+1) := by omega
        _ = snap m e r0 comp.cells (lo+d) := hstep
        _ = snap m e r0 comp.cells lo := ih

end Echo
