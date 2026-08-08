import PairedPointwiseReplayCore
import PersistentLobeSeparationStandalone

/-!
# Preferred strict bound for one pre-absorption support epoch

For one fixed-support interval:

* endpoint accounting gives `E+F=M` for the non-active-lobe cells;
* separated full-edge indicators have three bits of capacity per four
  projected cells;
* one exact Boolean bit records each active lobe;
* before a four-slot absorbing tail, active lobe cells are star-separated, so
  their count `A` is at most `M`; and
* paired pointwise replay makes the combined code injective on snapshots.

Hence, for `N=A+M` represented cells and `S` distinct snapshots,

    S^8 ≤ 2^(7N+18).

This is a strict-base bound `S ≤ 2^(7N/8 + 9/4)` for one support epoch.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Strict bound for one certified pre-absorption fixed-support epoch.** -/
theorem paired_block_preAbsorption_epoch_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (allCells projected edges lobes ks : List Nat)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hfullRep : PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : PairedReplayCover m e r0 lo hi allCells lobes)
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
  cases ks with
  | nil =>
      simp [blockCoreEighth, fourth]
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
          blockCoreTrueCount (endpointFullBits m e r0 edges j) = F := by
        intro j hj
        have hjI := hks j hj
        have haccJ := endpoint_accounting_standalone m e r0 hr0
          projected edges j hprojectedNodup hendsNodup
          (hselected j hjI.1 hjI.2)
          (hconfirmedCells j hjI.1 hjI.2)
          (hedgeOcc j hjI.1 hjI.2)
        rw [blockCoreTrueCount_eq_endpoint]
        unfold F
        omega
      have hhalfAll := standaloneActiveLobes_half m e r0 hrun
        lo hi lobes allCells hlobeNodup hallNodup hlobeClosed
        hlobeLoop hlobeOcc hlobeVisit hnoTail
      have hhalf : lobes.length ≤ projected.length := by
        rw [hcellCount] at hhalfAll
        omega
      apply blockCore_abstract_epoch_eighth_bound m e r0
        allCells edges (k :: rest)
        (coreLobeBits m e r0 lobes)
        allCells.length projected.length lobes.length F
        hEF hfull
      · intro j hj
        exact coreLobeBits_length m e r0 lobes j
      · intro i hiK j hjK hc
        exact paired_block_code_replay m e r0 hrun hr0
          lo hi allCells edges lobes hfixed hfullRep hcover
          hlobeLoop hlobeOcc
          (hks i hiK) (hks j hjK) hc
      · exact hnd
      · exact hcellCount
      · exact hhalf

end Echo
