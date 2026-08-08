import FullReachBooleanReplay
import FrozenComponentListCore
import PersistentLobeSeparationStandalone

/-!
# Certified strict bound for one pre-absorption support epoch

This theorem assembles the full argument for one fixed-support interval:

* endpoint accounting fixes `E+F=M`;
* full-edge reachability replays every variable projected cell;
* represented no-full non-lobe components form a frozen block;
* active lobe registers are exact Boolean coordinates;
* before a four-slot tail begins, active lobe cells are star-separated, hence
  `A≤M`; and
* sparse full-edge indicators give the strict integer bound

    (# distinct snapshots)^8 ≤ 2^(7N+8).

The only remaining global work is to manufacture the finite support/component
lists from an arbitrary finite machine and aggregate the linearly many support
epochs.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Strict bound for a certified pre-absorption fixed-support interval.** -/
theorem certified_preAbsorption_epoch_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (allCells projected edges variable lobes ks : List Nat)
    (frozenComps : List (CoreComponentInterval m e r0 lo hi))
    (hall : allCells = fullLobeFrozenCells m variable lobes
      (frozenComponentCells frozenComps))
    (hcellCount : allCells.length = lobes.length + projected.length)
    (hallNodup : allCells.Nodup)
    (hprojectedNodup : projected.Nodup)
    (hendsNodup : (standaloneEdgeEnds m edges).Nodup)
    (hselected : ∀ k, lo ≤ k → k ≤ hi → ∀ c ∈ projected,
      reg m e r0 k c ∈ standaloneEdgeEnds m edges)
    (hconfirmedCells : ∀ k, lo ≤ k → k ≤ hi →
      ∀ x ∈ standaloneEdgeEnds m edges,
        Confirmed m e r0 k x → m.cellOf x ∈ projected)
    (hedgeOcc : ∀ k, lo ≤ k → k ≤ hi → ∀ s ∈ edges,
      Occupied m e r0 k s)
    (hvariable : FullReachCovered m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges variable)
    (hfrozenNoFull : FrozenComponentsNoFull m e r0 lo frozenComps)
    (hfrozenNoLobe : FrozenComponentsNoLobe m e r0 frozenComps)
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
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    sparseCoreEighth ks.length ≤ 2^(7*allCells.length + 8) := by
  cases ks with
  | nil =>
      simp [sparseCoreEighth, fourth]
  | cons k rest =>
      have hk : k ∈ k :: rest := List.mem_cons_self
      have hkI := hks k hk
      let F := projected.length - edges.length
      have haccK := endpoint_accounting_standalone m e r0 hr0
        projected edges k hprojectedNodup hendsNodup
        (hselected k hkI.1 hkI.2)
        (hconfirmedCells k hkI.1 hkI.2)
        (hedgeOcc k hkI.1 hkI.2)
      have hEF : edges.length + F = projected.length := by
        unfold F
        omega
      have hfull : ∀ j ∈ k :: rest,
          endpointTrueCount (endpointFullBits m e r0 edges j) = F := by
        intro j hj
        have hjI := hks j hj
        have haccJ := endpoint_accounting_standalone m e r0 hr0
          projected edges j hprojectedNodup hendsNodup
          (hselected j hjI.1 hjI.2)
          (hconfirmedCells j hjI.1 hjI.2)
          (hedgeOcc j hjI.1 hjI.2)
        unfold F
        omega
      have hfreeze : SnapshotFrozen m e r0
          (fun t => lo ≤ t ∧ t ≤ hi)
          (frozenComponentCells frozenComps) := by
        intro i hiI j hjI
        exact frozenComponentList_constant m e r0 hrun hr0
          frozenComps hfrozenNoFull hfrozenNoLobe
          hiI.1 hiI.2 hjI.1 hjI.2
      have hhalfAll := standaloneActiveLobes_half m e r0 hrun
        lo hi lobes allCells hlobeNodup hallNodup hlobeClosed
        hlobeLoop hlobeOcc hlobeVisit hnoTail
      have hhalf : lobes.length ≤ projected.length := by
        rw [hcellCount] at hhalfAll
        omega
      have hnd' : ((k :: rest).map (snap m e r0
          (fullLobeFrozenCells m variable lobes
            (frozenComponentCells frozenComps)))).Nodup := by
        simpa [hall] using hnd
      exact full_reach_lobe_epoch_bound m e r0
        (fun t => lo ≤ t ∧ t ≤ hi)
        edges variable lobes (frozenComponentCells frozenComps)
        (k :: rest) allCells.length projected.length F
        hvariable hfreeze hlobeLoop
        (fun t ht a ha => hlobeOcc t ht.1 ht.2 a ha)
        hks hsupport hEF hfull hnd'
        hcellCount hhalf

end Echo
