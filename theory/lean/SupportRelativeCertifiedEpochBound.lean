import SupportRelativePointwiseReplay
import CertifiedLobeAbsorption

/-!
# Strict fixed-support bound under the exact absorption dichotomy

This is the support-relative one-epoch theorem with the precise hypothesis
`NoCertifiedLobeAbsorptionIn`.  That condition is exactly what is needed for
active lobe half-density and is exhaustive on a finite interval.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Strict bound for one fixed-support epoch before any certified lobe
absorption.** -/
theorem support_relative_noCertified_epoch_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (allCells projected edges lobes ks : List Nat)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hfullRep : PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : PairedSupportReplayCover m e r0 lo hi allCells lobes)
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
    (hnoAbsorb : NoCertifiedLobeAbsorptionIn m e r0 lo hi)
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
      have hhalfAll := standaloneActiveLobes_half_noCertified m e r0
        lo hi lobes allCells hlobeNodup hallNodup hlobeClosed
        hlobeLoop hlobeOcc hlobeVisit hnoAbsorb
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
        exact paired_support_block_code_replay m e r0 hrun hr0
          lo hi allCells edges lobes hfixed hfullRep hcover
          hlobeLoop hlobeOcc
          (hks i hiK) (hks j hjK) hc
      · exact hnd
      · exact hcellCount
      · exact hhalf

end Echo
