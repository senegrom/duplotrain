import SupportWeightFibres

/-!
# Global strict bound before the four-slot tail

Partition a finite list of distinct snapshots by occupied-support weight.  A
nonempty weight fibre has canonical minimum and maximum times.  Monotonicity of
support and equality of the endpoint weights make the whole intervening
interval a fixed-support epoch, so `canonical_preAbsorption_epoch_bound`
applies automatically.

There are exactly `slots.length + 1` possible weights.  Aggregating their
one-epoch eighth-power bounds gives

    T^8 ≤ (slots.length + 1)^8 * 2^(7*N + 18)

for every finite pre-tail trajectory list on `N` represented cells.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **One support-weight fibre satisfies the canonical strict epoch bound.** -/
theorem canonical_supportWeight_fibre_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (q : Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnoTail : StandaloneNoFourTailIn m e r0 globalLo globalHi)
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
      have hloData := List.mem_filter.mp (by
        simpa [fibre] using hloMemF)
      have hhiData := List.mem_filter.mp (by
        simpa [fibre] using hhiMemF)
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
      have hnoSub : StandaloneNoFourTailIn m e r0 lo hi :=
        noFourTail_restrict m e r0 hnoTail
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
      have hbound := canonical_preAbsorption_epoch_bound m e r0
        hrun hr0 lo hi lo cells slots (x :: rest)
        subFrame hfixed ⟨Nat.le_refl lo, hlohi⟩
        hnoSub hbetween hndFibre
      have hlen :
          (ks.filter (fun k => supportWeight m e r0 slots k = q)).length =
            (x :: rest).length := by
        simpa [fibre] using congrArg List.length hfibre
      rw [hlen]
      exact hbound

/-- **Canonical global pre-tail strict-base bound.** -/
theorem canonical_preTail_global_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnoTail : StandaloneNoFourTailIn m e r0 globalLo globalHi)
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
    exact canonical_supportWeight_fibre_bound m e r0
      hrun hr0 globalLo globalHi cells slots ks q
      frame hks hnoTail hnd
  have hagg := block_aggregate_eighth_bound sizes
    (2^(7*cells.length+18)) heach
  rw [hsum, hlen] at hagg
  exact hagg

end Echo
