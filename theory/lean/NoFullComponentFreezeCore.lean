import EndpointAccountingStandalone
import NoFullFreezeCore

/-!
# No-full component freezing, corrected induction

For a finite represented component, endpoint accounting fixes its number of
full edges throughout a fixed-support interval.  If that number is zero at the
left endpoint, every non-lobe register in the component is frozen.  The proof
uses induction on prefixes `lo+d ≤ hi`, keeping the interval endpoint fixed.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Fullness is endpoint-independent. -/
theorem coreFull_bar_iff (k s : Nat) :
    Full m e r0 k (m.bar s) ↔ Full m e r0 k s := by
  unfold Full
  rw [m.bar_invol]
  exact and_comm

/-- Recover an edge representative from endpoint membership. -/
theorem mem_standaloneEdgeEnds_core {edges : List Nat} {x : Nat} :
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

/-- Zero count iff no represented edge is full: forward direction. -/
theorem coreNoFull_of_count_zero
    (edges : List Nat) (k : Nat)
    (hzero : endpointTrueCount
      (endpointFullBits m e r0 edges k) = 0) :
    ∀ s ∈ edges, ¬ Full m e r0 k s := by
  classical
  induction edges with
  | nil => simp
  | cons s rest ih =>
      by_cases hs : Full m e r0 k s
      · simp [endpointFullBits, endpointTrueCount, hs] at hzero
      · have hrest : endpointTrueCount
            (endpointFullBits m e r0 rest k) = 0 := by
          simpa [endpointFullBits, endpointTrueCount, hs] using hzero
        intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hs
        · exact ih hrest t ht

/-- Zero count iff no represented edge is full: reverse direction. -/
theorem coreCount_zero_of_noFull
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

/-- Uniform representation of one support component on `[lo,hi]`. -/
structure CoreComponentInterval (lo hi : Nat) where
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

/-- The full-edge count is constant on the interval. -/
theorem CoreComponentInterval.fullCount_eq
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat}
    (comp : CoreComponentInterval m e r0 lo hi)
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

/-- No full representative implies the pointwise `CoreNoFull` property. -/
theorem CoreComponentInterval.coreNoFull
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi k : Nat}
    (comp : CoreComponentInterval m e r0 lo hi)
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
  rcases mem_standaloneEdgeEnds_core m hxEnds with
    ⟨s, hs, hxs | hxs⟩
  · subst x
    exact hnone s hs hfull
  · subst x
    exact hnone s hs ((coreFull_bar_iff m e r0 k s).mp hfull)

/-- Every prefix of a no-full non-lobe component has the initial snapshot. -/
theorem component_snap_prefix
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat}
    (comp : CoreComponentInterval m e r0 lo hi)
    (hnoneLo : ∀ s ∈ comp.edges, ¬ Full m e r0 lo s)
    (hnlobe : ∀ c ∈ comp.cells, CoreNoLobe m c) :
    ∀ d, lo+d ≤ hi →
      snap m e r0 comp.cells (lo+d) =
        snap m e r0 comp.cells lo := by
  have hzeroLo := coreCount_zero_of_noFull m e r0
    comp.edges lo hnoneLo
  intro d
  induction d with
  | zero =>
      intro _
      rfl
  | succ d ih =>
      intro hbound
      have hprevBound : lo+d ≤ hi := by omega
      have hprev := ih hprevBound
      have hkLo : lo ≤ lo+d := by omega
      have hkLt : lo+d < hi := by omega
      have hcount := comp.fullCount_eq hr0
        (i := lo) (j := lo+d)
        (by omega) (by omega) hkLo hprevBound
      have hzeroK : endpointTrueCount
          (endpointFullBits m e r0 comp.edges (lo+d)) = 0 := by
        rw [← hcount]
        exact hzeroLo
      have hnoneK := coreNoFull_of_count_zero m e r0
        comp.edges (lo+d) hzeroK
      have hcore := comp.coreNoFull hr0 hkLo hprevBound hnoneK
      have hstep := snap_step_eq_of_coreNoFull_coreNoLobe m e r0
        hrun hr0 (lo+d) comp.cells
        (comp.support_step (lo+d) hkLo hkLt)
        hcore hnlobe
      calc
        snap m e r0 comp.cells (lo + (d+1))
            = snap m e r0 comp.cells (lo+d+1) := by omega
        _ = snap m e r0 comp.cells (lo+d) := hstep
        _ = snap m e r0 comp.cells lo := hprev

/-- **Endpoint form: the entire no-full non-lobe component is frozen.** -/
theorem component_snap_frozen_core
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat}
    (hlohi : lo ≤ hi)
    (comp : CoreComponentInterval m e r0 lo hi)
    (hnoneLo : ∀ s ∈ comp.edges, ¬ Full m e r0 lo s)
    (hnlobe : ∀ c ∈ comp.cells, CoreNoLobe m c) :
    snap m e r0 comp.cells hi = snap m e r0 comp.cells lo := by
  have h := component_snap_prefix m e r0 hrun hr0
    comp hnoneLo hnlobe (hi-lo) (by omega)
  have heq : lo + (hi-lo) = hi := by omega
  simpa [heq] using h

end Echo
