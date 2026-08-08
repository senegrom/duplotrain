import PairedBlockEpochStrictBound
import CanonicalSupportFrame
import ActiveLobeCoverCore

/-!
# Strict epoch bound from a finite slot frame

This wrapper removes all manual support-edge hypotheses from the preferred
fixed-epoch theorem.  A finite bar-closed slot frame and one reference time
canonically generate the occupied edge representatives, endpoint
no-duplication, selected-slot coverage, and full-edge representation.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Preferred strict bound from canonical finite support data.** -/
theorem paired_block_epoch_bound_from_frame
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi k0 : Nat)
    (allCells projected slots lobes ks : List Nat)
    (frame : FiniteSlotFrame m e r0 lo hi projected slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi)
    (hstructure : ∀ c ∈ allCells,
      CoreNoLobe m c ∨
        ∃ a, m.cellOf a = c ∧ m.cellOf (m.bar a) = c)
    (hactiveComplete : ActiveLobesComplete m e r0
      lo hi allCells lobes)
    (hcellCount : allCells.length = lobes.length + projected.length)
    (hallNodup : allCells.Nodup)
    (hprojectedNodup : projected.Nodup)
    (hlobeNodup : (standaloneActiveLobeCells m lobes).Nodup)
    (hlobeClosed : ∀ c ∈ standaloneActiveLobeCells m lobes,
      c ∈ allCells ∧ m.star c ∈ allCells)
    (hlobeLoop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hlobeOcc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hlobeVisit : ∀ a ∈ lobes,
      StandaloneLobeVisited m e r0 lo hi a)
    (hnoTail : StandaloneNoFourTailIn m e r0 lo hi)
    (hks : ∀ k ∈ ks, lo ≤ k ∧ k ≤ hi)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    blockCoreEighth ks.length ≤ 2^(7*allCells.length+18) := by
  let edges := canonicalSupportEdges m e r0 slots k0
  have hcover : PairedReplayCover m e r0 lo hi allCells lobes :=
    pairedReplayCover_of_active_complete m e r0
      lo hi allCells lobes hstructure hactiveComplete
  have hfullRep : PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges := by
    exact frame_allFull_represented m e r0 hr0 frame hfixed
      hk0.1 hk0.2
  have hends : (standaloneEdgeEnds m edges).Nodup := by
    exact canonicalSupportEdgeEnds_nodup m e r0
      frame.slots_nodup k0
  have hselected : ∀ k, lo ≤ k → k ≤ hi → ∀ c ∈ projected,
      reg m e r0 k c ∈ standaloneEdgeEnds m edges := by
    intro k hkLo hkHi c hc
    exact frame_selected_in_support_ends m e r0 hr0
      frame hfixed hk0.1 hk0.2 hkLo hkHi hc
  have hconfirmed : ∀ k, lo ≤ k → k ≤ hi →
      ∀ x ∈ standaloneEdgeEnds m edges,
        Confirmed m e r0 k x → m.cellOf x ∈ projected := by
    intro k hkLo hkHi x hx hconf
    exact frame.confirmed_cell k hkLo hkHi x hconf
  have hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ s ∈ edges,
      Occupied m e r0 k s := by
    exact frame_support_edges_occupied m e r0 frame hfixed
      hk0.1 hk0.2
  exact paired_block_preAbsorption_epoch_bound m e r0
    hrun hr0 lo hi allCells projected edges lobes ks
    hfixed hfullRep hcover hcellCount hallNodup
    hprojectedNodup hends hselected hconfirmed hocc
    hlobeNodup hlobeClosed hlobeLoop hlobeOcc hlobeVisit
    hnoTail hks hnd

end Echo
