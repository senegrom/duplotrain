import SupportWeightFibres
import CanonicalCertifiedEpochBound

/-!
# Global strict bound with no certified lobe absorption

Partition distinct snapshots by occupied-support weight.  Equal weights give
equal support, so every nonempty fibre lies inside a canonically fixed-support
interval.  The exact no-certificate condition restricts to that interval and
the canonical epoch theorem applies.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- One support-weight fibre satisfies the strict bound under the global
no-certificate condition. -/
theorem canonical_noCertified_supportWeight_fibre_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (q : Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnoAbsorb : NoCertifiedLobeAbsorptionIn m e r0
      globalLo globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    blockCoreEighth
      ((ks.filter (fun k => supportWeight m e r0 slots k = q)).length) ≤
      2^(7*cells.length+18) := by
  let fibre := ks.filter
    (fun k => supportWeight m e r0 slots k = q)
  cases hfibre : fibre with
  | nil =>
      have hlen :
          (ks.filter (fun k => supportWeight m e r0 slots k = q)).length = 0 := by
        simpa [fibre] using congrArg List.length hfibre
      rw [hlen]
      simp [blockCoreEighth, fourth]
  | cons x rest =>
      let lo := fibreMinFrom x rest
      let hi := fibreMaxFrom x rest
      have hloMemF : lo ∈ fibre := by
        rw [hfibre]
        exact fibreMinFrom_mem x rest
      have hhiMemF : hi ∈ fibre := by
        rw [hfibre]
        exact fibreMaxFrom_mem x rest
      have hloInFilter :
          lo ∈ ks.filter
            (fun k => supportWeight m e r0 slots k = q) := by
        simpa only [fibre] using hloMemF
      have hhiInFilter :
          hi ∈ ks.filter
            (fun k => supportWeight m e r0 slots k = q) := by
        simpa only [fibre] using hhiMemF
      have hloFilter := List.mem_filter.mp hloInFilter
      have hhiFilter := List.mem_filter.mp hhiInFilter
      have hloData :
          lo ∈ ks ∧ supportWeight m e r0 slots lo = q :=
        ⟨hloFilter.1, of_decide_eq_true hloFilter.2⟩
      have hhiData :
          hi ∈ ks ∧ supportWeight m e r0 slots hi = q :=
        ⟨hhiFilter.1, of_decide_eq_true hhiFilter.2⟩
      have hloGlobal := hks lo hloData.1
      have hhiGlobal := hks hi hhiData.1
      have hlohi : lo ≤ hi := by
        dsimp [lo, hi]
        exact fibreMinFrom_le_fibreMaxFrom x rest
      have hweight : supportWeight m e r0 slots lo =
          supportWeight m e r0 slots hi :=
        hloData.2.trans hhiData.2.symm
      have hsnap : supportSnap m e r0 slots lo =
          supportSnap m e r0 slots hi :=
        supportSnap_eq_of_weight_eq m e r0 hrun hr0 slots hweight
      have hend : ∀ s,
          Occupied m e r0 lo s ↔ Occupied m e r0 hi s :=
        completeFrame_global_support_eq m e r0 frame
          hloGlobal.1 hloGlobal.2 hhiGlobal.1 hhiGlobal.2 hsnap
      have hfixed : PairedSupportFixed m e r0 lo hi :=
        pairedSupportFixed_of_endpoint_eq m e r0
          hrun hr0 hlohi hend
      let subFrame := restrictCompleteFiniteEpochFrame m e r0
        frame hloGlobal.1 hhiGlobal.2
      have hnoSub : NoCertifiedLobeAbsorptionIn m e r0 lo hi :=
        noCertifiedLobeAbsorption_restrict m e r0 hnoAbsorb
          hloGlobal.1 hhiGlobal.2
      have hbetween : ∀ k ∈ x :: rest, lo ≤ k ∧ k ≤ hi := by
        intro k hk
        constructor
        · dsimp [lo]
          exact fibreMinFrom_le_mem x rest k hk
        · dsimp [hi]
          exact mem_le_fibreMaxFrom x rest k hk
      have hndFilter :
          ((ks.filter
            (fun k => supportWeight m e r0 slots k = q)).map
              (snap m e r0 cells)).Nodup :=
        map_filter_nodup (snap m e r0 cells)
          (fun k => supportWeight m e r0 slots k = q) hnd
      have hndFibre :
          ((x :: rest).map (snap m e r0 cells)).Nodup := by
        rw [← hfibre]
        simpa [fibre] using hndFilter
      have hbound := canonical_noCertified_epoch_bound m e r0
        hrun hr0 lo hi lo cells slots (x :: rest)
        subFrame hfixed ⟨Nat.le_refl lo, hlohi⟩
        hnoSub hbetween hndFibre
      have hlen :
          (ks.filter (fun k => supportWeight m e r0 slots k = q)).length =
            (x :: rest).length := by
        simpa [fibre] using congrArg List.length hfibre
      rw [hlen]
      exact hbound

/-- **Canonical global strict-base bound when no certificate occurs.** -/
theorem canonical_noCertified_global_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnoAbsorb : NoCertifiedLobeAbsorptionIn m e r0
      globalLo globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    blockCoreEighth ks.length ≤
      blockCoreEighth (slots.length + 1) *
        2^(7*cells.length+18) := by
  let weight := supportWeight m e r0 slots
  let sizes := supportFibreSizes (slots.length + 1) weight ks
  have hsum : sizes.sum = ks.length := by
    dsimp [sizes]
    apply supportFibreSizes_sum (slots.length + 1) weight ks
    intro k hk
    dsimp [weight]
    exact supportWeight_lt m e r0 slots k
  have hlen : sizes.length = slots.length + 1 := by
    simp [sizes, supportFibreSizes]
  have heach : ∀ s ∈ sizes,
      blockCoreEighth s ≤ 2^(7*cells.length+18) := by
    intro s hs
    dsimp [sizes, supportFibreSizes] at hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    dsimp [supportFibreSize, weight]
    exact canonical_noCertified_supportWeight_fibre_bound m e r0
      hrun hr0 globalLo globalHi cells slots ks q
      frame hks hnoAbsorb hnd
  have hagg := block_aggregate_eighth_bound sizes
    (2^(7*cells.length+18)) heach
  rw [hsum, hlen] at hagg
  exact hagg

end Echo
