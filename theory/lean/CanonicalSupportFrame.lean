import CanonicalEdgeRepsCore
import PairedPointwiseReplayCore

/-!
# Canonical finite support frame for one fixed-support epoch

Start with a finite bar-closed slot list.  Keep one ordered representative per
jump edge, then retain only representatives occupied at one reference time.
Fixed support makes this the common support-edge list for the whole epoch.

The resulting list automatically provides:

* duplicate-free expanded endpoints;
* every projected selected register in the endpoint expansion;
* every represented edge occupied at every epoch time; and
* one representative for every full edge.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Finite slot coverage for projected cells on an interval. -/
structure FiniteSlotFrame
    (m : Machine) (e r0 : Nat → Nat)
    (lo hi : Nat) (projected slots : List Nat) where
  slots_nodup : slots.Nodup
  bar_closed : ∀ s ∈ slots, m.bar s ∈ slots
  bar_ne : ∀ s ∈ slots, m.bar s ≠ s
  selected : ∀ k, lo ≤ k → k ≤ hi → ∀ c ∈ projected,
    reg m e r0 k c ∈ slots
  confirmed_cell : ∀ k, lo ≤ k → k ≤ hi → ∀ x,
    Confirmed m e r0 k x → m.cellOf x ∈ projected

/-- Canonical occupied support representatives at a reference time. -/
noncomputable def canonicalSupportEdges
    (m : Machine) (e r0 : Nat → Nat)
    (slots : List Nat) (k0 : Nat) : List Nat := by
  classical
  exact (canonicalEdgesCore m slots).filter
    (fun s => Occupied m e r0 k0 s)

/-- Same-edge representatives have equivalent occupancy. -/
theorem occupied_sameEdge_iff
    {k s t : Nat} (h : SameEdge m s t) :
    Occupied m e r0 k s ↔ Occupied m e r0 k t := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · exact (occupied_bar m e r0 k s).symm

/-- Support-edge representatives remain ordered. -/
theorem canonicalSupportEdges_ordered
    (slots : List Nat) (k0 : Nat) :
    ∀ s ∈ canonicalSupportEdges m e r0 slots k0,
      s < m.bar s := by
  classical
  intro s hs
  have hc : s ∈ canonicalEdgesCore m slots :=
    (List.mem_filter.mp hs).1
  exact ((mem_canonicalEdgesCore_iff (m := m)).mp hc).2

/-- Support-edge representatives remain duplicate-free. -/
theorem canonicalSupportEdges_nodup
    {slots : List Nat} (hnd : slots.Nodup) (k0 : Nat) :
    (canonicalSupportEdges m e r0 slots k0).Nodup := by
  classical
  exact (canonicalEdgesCore_nodup m hnd).filter _

/-- Expanded support endpoints are duplicate-free. -/
theorem canonicalSupportEdgeEnds_nodup
    {slots : List Nat} (hnd : slots.Nodup) (k0 : Nat) :
    (standaloneEdgeEnds m
      (canonicalSupportEdges m e r0 slots k0)).Nodup := by
  apply orderedEdgeEndsCore_nodup m
    (canonicalSupportEdges m e r0 slots k0)
    (canonicalSupportEdges_nodup m e r0 hnd k0)
    (canonicalSupportEdges_ordered m e r0 slots k0)

/-- Every support representative is occupied at the reference time. -/
theorem canonicalSupportEdges_occupied_at_ref
    (slots : List Nat) (k0 : Nat) :
    ∀ s ∈ canonicalSupportEdges m e r0 slots k0,
      Occupied m e r0 k0 s := by
  classical
  intro s hs
  exact of_decide_eq_true (List.mem_filter.mp hs).2

/-- A selected projected register is represented by the common endpoint list. -/
theorem frame_selected_in_support_ends
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat} {projected slots : List Nat}
    (frame : FiniteSlotFrame m e r0 lo hi projected slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    {k0 k c : Nat}
    (hk0Lo : lo ≤ k0) (hk0Hi : k0 ≤ hi)
    (hkLo : lo ≤ k) (hkHi : k ≤ hi)
    (hc : c ∈ projected) :
    reg m e r0 k c ∈ standaloneEdgeEnds m
      (canonicalSupportEdges m e r0 slots k0) := by
  let s := reg m e r0 k c
  have hsSlots : s ∈ slots := frame.selected k hkLo hkHi c hc
  rcases slot_has_canonicalEdgeCore m frame.bar_closed frame.bar_ne
      hsSlots with ⟨g, hg, hsg⟩
  have hsConf : Confirmed m e r0 k s :=
    old_register_confirmed m e r0 hr0 k c
  have hsOcc : Occupied m e r0 k s := Or.inl hsConf
  have hgOccK : Occupied m e r0 k g :=
    (occupied_sameEdge_iff m e r0 hsg).mp hsOcc
  have hsupport := pairedSupportFixed_between m e r0 hfixed
    hk0Lo hk0Hi hkLo hkHi
  have hgOcc0 : Occupied m e r0 k0 g :=
    (hsupport g).mpr hgOccK
  have hgSupport : g ∈ canonicalSupportEdges m e r0 slots k0 := by
    classical
    exact List.mem_filter.mpr ⟨hg, decide_eq_true hgOcc0⟩
  have hends := core_rep_endpoints_mem m hgSupport
  rcases hsg with hsg | hsg
  · simpa [s, hsg] using hends.1
  · have hb := congrArg m.bar hsg
    have hbar : m.bar g = s := by
      simpa [m.bar_invol] using hb
    simpa [s, hbar] using hends.2

/-- Every full edge has a common support representative. -/
theorem frame_allFull_represented
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat} {projected slots : List Nat}
    (frame : FiniteSlotFrame m e r0 lo hi projected slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    {k0 : Nat}
    (hk0Lo : lo ≤ k0) (hk0Hi : k0 ≤ hi) :
    PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi)
      (canonicalSupportEdges m e r0 slots k0) := by
  intro k hk f hfull
  have hfCell : m.cellOf f ∈ projected :=
    frame.confirmed_cell k hk.1 hk.2 f hfull.1
  have hfSlots : f ∈ slots := by
    have hs := frame.selected k hk.1 hk.2
      (m.cellOf f) hfCell
    have hfConf : Confirmed m e r0 k f := hfull.1
    unfold Confirmed at hfConf
    rw [hfConf] at hs
    exact hs
  rcases slot_has_canonicalEdgeCore m frame.bar_closed frame.bar_ne
      hfSlots with ⟨g, hg, hfg⟩
  have hfOcc : Occupied m e r0 k f := Or.inl hfull.1
  have hgOccK : Occupied m e r0 k g :=
    (occupied_sameEdge_iff m e r0 hfg).mp hfOcc
  have hsupport := pairedSupportFixed_between m e r0 hfixed
    hk0Lo hk0Hi hk.1 hk.2
  have hgOcc0 : Occupied m e r0 k0 g :=
    (hsupport g).mpr hgOccK
  have hgSupport : g ∈ canonicalSupportEdges m e r0 slots k0 := by
    classical
    exact List.mem_filter.mpr ⟨hg, decide_eq_true hgOcc0⟩
  exact ⟨g, hgSupport, hfg⟩

/-- Every common support representative remains occupied throughout the epoch. -/
theorem frame_support_edges_occupied
    {lo hi : Nat} {projected slots : List Nat}
    (_frame : FiniteSlotFrame m e r0 lo hi projected slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    {k0 : Nat}
    (hk0Lo : lo ≤ k0) (hk0Hi : k0 ≤ hi) :
    ∀ k, lo ≤ k → k ≤ hi →
      ∀ s ∈ canonicalSupportEdges m e r0 slots k0,
        Occupied m e r0 k s := by
  intro k hkLo hkHi s hs
  have hs0 := canonicalSupportEdges_occupied_at_ref m e r0
    slots k0 s hs
  have hsupport := pairedSupportFixed_between m e r0 hfixed
    hk0Lo hk0Hi hkLo hkHi
  exact (hsupport s).mp hs0

/-- Confirmed common support endpoints belong to projected cells. -/
theorem frame_confirmed_endpoint_cell
    {lo hi : Nat} {projected slots : List Nat}
    (frame : FiniteSlotFrame m e r0 lo hi projected slots) :
    ∀ k, lo ≤ k → k ≤ hi →
      ∀ x ∈ standaloneEdgeEnds m
        (canonicalSupportEdges m e r0 slots k),
        Confirmed m e r0 k x → m.cellOf x ∈ projected := by
  intro k hkLo hkHi x hx hconf
  exact frame.confirmed_cell k hkLo hkHi x hconf

end Echo
