import CanonicalNoCertifiedGlobalBound

/-!
# Unconditional finite-frame strict-base bound

On a finite interval, either no certified lobe absorption occurs or the finite
list of certified times has a least element.  Before that least time the
support-weight bound applies; from that time onward the complete register
snapshot has at most four possibilities.

No tail certificate is supplied by the caller.  The resulting bound is

    T^8 ≤ (2 * (slots.length + 1))^8 * 2^(7*N + 18).
-/

namespace Echo

private theorem canonical_filter_lt_ge_length (cut : Nat) :
    ∀ xs : List Nat,
      (xs.filter (fun k => k < cut)).length +
        (xs.filter (fun k => cut ≤ k)).length = xs.length := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      by_cases h : x < cut
      · have hn : ¬ cut ≤ x := by omega
        simp [h, hn, ih]
      · have hge : cut ≤ x := by omega
        simp [h, hge, ih]

/-- Four snapshots fit inside the universal strict exponential factor. -/
theorem canonical_four_snapshots_eighth_le (N : Nat) :
    blockCoreEighth 4 ≤ 2^(7*N+18) := by
  have hbase : blockCoreEighth 4 ≤ 2^18 := by decide
  exact Nat.le_trans hbase
    (Nat.pow_le_pow_right (by omega) (by omega))

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Unconditional strict-base bound for a complete finite echo frame.** -/
theorem canonical_unconditional_global_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    blockCoreEighth ks.length ≤
      blockCoreEighth (2 * (slots.length + 1)) *
        2^(7*cells.length+18) := by
  classical
  let X := 2^(7*cells.length+18)
  by_cases hex : ∃ k,
      globalLo ≤ k ∧ k ≤ globalHi ∧
        CertifiedLobeAbsorptionAt m e r0 k
  · let candidates := (List.range (globalHi + 1)).filter fun k =>
        globalLo ≤ k ∧ CertifiedLobeAbsorptionAt m e r0 k
    rcases hex with ⟨w, hwLo, hwHi, hwCert⟩
    have hwCand : w ∈ candidates := by
      dsimp [candidates]
      exact List.mem_filter.mpr
        ⟨List.mem_range.mpr (by omega), hwLo, hwCert⟩
    cases hcandidates : candidates with
    | nil =>
        rw [hcandidates] at hwCand
        cases hwCand
    | cons x rest =>
        let k0 := fibreMinFrom x rest
        have hk0Cand : k0 ∈ candidates := by
          rw [hcandidates]
          exact fibreMinFrom_mem x rest
        have hk0Data := List.mem_filter.mp (by
          simpa [candidates] using hk0Cand)
        have hk0Lo : globalLo ≤ k0 := hk0Data.2.1
        have hk0Hi : k0 ≤ globalHi := by
          have hrange : k0 < globalHi + 1 :=
            List.mem_range.mp hk0Data.1
          omega
        have hk0Cert : CertifiedLobeAbsorptionAt m e r0 k0 :=
          hk0Data.2.2
        let pre := ks.filter (fun k => k < k0)
        let tail := ks.filter (fun k => k0 ≤ k)
        have hsplit : pre.length + tail.length = ks.length := by
          dsimp [pre, tail]
          exact canonical_filter_lt_ge_length k0 ks
        have hndPre : (pre.map (snap m e r0 cells)).Nodup := by
          dsimp [pre]
          exact map_filter_nodup (snap m e r0 cells)
            (fun k => k < k0) hnd
        have hndTail : (tail.map (snap m e r0 cells)).Nodup := by
          dsimp [tail]
          exact map_filter_nodup (snap m e r0 cells)
            (fun k => k0 ≤ k) hnd
        have htailTimes : ∀ k ∈ tail, k0 ≤ k := by
          intro k hk
          exact (List.mem_filter.mp (by
            simpa [tail] using hk)).2
        have htailCount : tail.length ≤ 4 :=
          certifiedLobeAbsorption_snapshot_count m e r0
            hrun hk0Cert cells tail htailTimes hndTail
        have htailEight : blockCoreEighth tail.length ≤ X := by
          have hm := blockCoreEighth_mono htailCount
          exact Nat.le_trans hm (by
            dsimp [X]
            exact canonical_four_snapshots_eighth_le cells.length)
        by_cases hpre : globalLo < k0
        · let preHi := k0 - 1
          have hglobalPreHi : globalLo ≤ preHi := by
            dsimp [preHi]
            omega
          have hpreHiGlobal : preHi ≤ globalHi := by
            dsimp [preHi]
            omega
          let preFrame := restrictCompleteFiniteEpochFrame m e r0
            frame (Nat.le_refl globalLo) hpreHiGlobal
          have hpreTimes : ∀ k ∈ pre,
              globalLo ≤ k ∧ k ≤ preHi := by
            intro k hk
            have hkData := List.mem_filter.mp (by
              simpa [pre] using hk)
            have hkGlobal := hks k hkData.1
            constructor
            · exact hkGlobal.1
            · dsimp [preHi]
              omega
          have hnoPre : NoCertifiedLobeAbsorptionIn m e r0
              globalLo preHi := by
            intro k hkLo hkHi hcert
            have hkRange : k ∈ List.range (globalHi + 1) :=
              List.mem_range.mpr (by
                dsimp [preHi] at hkHi
                omega)
            have hkCandidates : k ∈ candidates := by
              dsimp [candidates]
              exact List.mem_filter.mpr ⟨hkRange, hkLo, hcert⟩
            have hkList : k ∈ x :: rest := by
              rw [← hcandidates]
              exact hkCandidates
            have hk0le : k0 ≤ k := by
              dsimp [k0]
              exact fibreMinFrom_le_mem x rest k hkList
            dsimp [preHi] at hkHi
            omega
          have hpreEight : blockCoreEighth pre.length ≤
              blockCoreEighth (slots.length + 1) * X := by
            dsimp [X]
            exact canonical_noCertified_global_bound m e r0
              hrun hr0 globalLo preHi cells slots pre
              preFrame hpreTimes hnoPre hndPre
          have hone : 1 ≤ blockCoreEighth (slots.length + 1) := by
            have hm := blockCoreEighth_mono
              (show 1 ≤ slots.length + 1 by omega)
            simpa [blockCoreEighth, fourth] using hm
          have htailLarge : blockCoreEighth tail.length ≤
              blockCoreEighth (slots.length + 1) * X := by
            apply Nat.le_trans htailEight
            have hm := Nat.mul_le_mul_right X hone
            simpa [Nat.mul_comm] using hm
          have hagg := block_aggregate_eighth_bound
            [pre.length, tail.length]
            (blockCoreEighth (slots.length + 1) * X) (by
              intro s hs
              simp only [List.mem_cons, List.mem_singleton] at hs
              rcases hs with rfl | rfl
              · exact hpreEight
              · exact htailLarge)
          have hsum : [pre.length, tail.length].sum = ks.length := by
            simpa using hsplit
          rw [hsum] at hagg
          rw [show blockCoreEighth (2 * (slots.length + 1)) =
              blockCoreEighth 2 * blockCoreEighth (slots.length + 1) by
                exact blockCoreEighth_mul 2 (slots.length + 1)]
          simpa [Nat.mul_assoc] using hagg
        · have hk0eq : k0 = globalLo := by omega
          have hallTail : ∀ k ∈ ks, k0 ≤ k := by
            intro k hk
            rw [hk0eq]
            exact (hks k hk).1
          have hallCount : ks.length ≤ 4 :=
            certifiedLobeAbsorption_snapshot_count m e r0
              hrun hk0Cert cells ks hallTail hnd
          have hallEight : blockCoreEighth ks.length ≤ X := by
            have hm := blockCoreEighth_mono hallCount
            exact Nat.le_trans hm (by
              dsimp [X]
              exact canonical_four_snapshots_eighth_le cells.length)
          apply Nat.le_trans hallEight
          have hone : 1 ≤ blockCoreEighth
              (2 * (slots.length + 1)) := by
            have hm := blockCoreEighth_mono
              (show 1 ≤ 2 * (slots.length + 1) by omega)
            simpa [blockCoreEighth, fourth] using hm
          have hmul := Nat.mul_le_mul_right X hone
          simpa [Nat.mul_comm, X] using hmul
  · have hno : NoCertifiedLobeAbsorptionIn m e r0
        globalLo globalHi := by
      intro k hkLo hkHi hcert
      exact hex ⟨k, hkLo, hkHi, hcert⟩
    have hbase := canonical_noCertified_global_bound m e r0
      hrun hr0 globalLo globalHi cells slots ks
      frame hks hno hnd
    have hfactor : blockCoreEighth (slots.length + 1) ≤
        blockCoreEighth (2 * (slots.length + 1)) :=
      blockCoreEighth_mono (by omega)
    exact Nat.le_trans hbase
      (Nat.mul_le_mul_right (2^(7*cells.length+18)) hfactor)

end Echo
