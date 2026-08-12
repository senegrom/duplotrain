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

theorem canonicalSupportEdges_occupied_at_ref
    (slots : List Nat) (k0 : Nat) :
    ∀ s ∈ canonicalSupportEdges m e r0 slots k0,
      Occupied m e r0 k0 s := by
  classical
  intro s hs
  exact of_decide_eq_true (List.mem_filter.mp hs).2

end Echo
