import RelevantCertifiedFibonacciEpochBound
import SupportWeightFibres

/-!
# Constructible global Fibonacci upper bound

The relevant-frame support vector is monotone, so equal support weights have
identical finite support.  Each weight fibre is therefore one fixed-support
epoch and inherits the Fibonacci-exact bound.  There are at most
`slots.length + 1` support weights.

If certified lobe absorption occurs, split at its first occurrence.  The
prefix has no certificate and the suffix contains at most four distinct
complete snapshots.  This gives the direct global count

    T ≤ (slots.length + 1) * fibBalancedCapacity cells.length + 4.

Unlike the earlier eighth-power aggregation, no extra factor two is paid for
joining the prefix and the absorbed tail.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

private theorem relevant_sum_le_length_mul
    (xs : List Nat) (B : Nat)
    (h : ∀ x ∈ xs, x ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hx := h x List.mem_cons_self
      have hr : ∀ y ∈ rest, y ≤ B := by
        intro y hy
        exact h y (List.mem_cons_of_mem _ hy)
      have hi := ih hr
      simp only [List.sum_cons, List.length_cons]
      calc
        x + rest.sum ≤ B + rest.length * B :=
          Nat.add_le_add hx hi
        _ = (rest.length + 1) * B := by
          simp [Nat.add_mul, Nat.add_comm]

private theorem relevant_filter_lt_ge_length (cut : Nat) :
    ∀ xs : List Nat,
      (xs.filter (fun k => k < cut)).length +
        (xs.filter (fun k => cut ≤ k)).length = xs.length := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      by_cases h : x < cut
      · have hn : ¬ cut ≤ x := by omega
        simp [h, hn]
        omega
      · have hge : cut ≤ x := by omega
        simp [h, hge]
        omega

/-- One support-weight fibre in a constructible relevant frame. -/
theorem relevant_noCertified_supportWeight_fibre_fibonacci_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (q : Nat)
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0
      globalLo globalHi cells)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnoAbsorb : NoCertifiedLobeAbsorptionIn m e r0
      globalLo globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    (ks.filter (fun k => supportWeight m e r0 slots k = q)).length ≤
      fibBalancedCapacity cells.length := by
  let fibre := ks.filter
    (fun k => supportWeight m e r0 slots k = q)
  cases hfibre : fibre with
  | nil =>
      have hlen :
          (ks.filter (fun k => supportWeight m e r0 slots k = q)).length = 0 := by
        simpa [fibre] using congrArg List.length hfibre
      rw [hlen]
      exact Nat.zero_le _
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
      have hfixed : PairedSupportFixed m e r0 lo hi :=
        pairedSupportFixed_of_endpoint_supportSnap m e r0
          frame.toRelevantFiniteFrame hrun hr0 hsnap
      have hfullSub : FullEdgesRelevant m e r0 lo hi cells := by
        intro k hkLo hkHi f hf
        exact hfullRelevant k
          (Nat.le_trans hloGlobal.1 hkLo)
          (Nat.le_trans hkHi hhiGlobal.2) f hf
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
      have hbound :=
        relevant_canonical_noCertified_fibonacci_epoch_bound m e r0
          hrun hr0 lo hi lo cells slots (x :: rest)
          frame hfullSub hfixed ⟨Nat.le_refl lo, hlohi⟩
          hnoSub hbetween hndFibre
      have hlen :
          (ks.filter (fun k => supportWeight m e r0 slots k = q)).length =
            (x :: rest).length := by
        simpa [fibre] using congrArg List.length hfibre
      rw [hlen]
      exact hbound

/-- Global direct count when no absorption certificate occurs. -/
theorem relevant_noCertified_global_fibonacci_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0
      globalLo globalHi cells)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnoAbsorb : NoCertifiedLobeAbsorptionIn m e r0
      globalLo globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤
      (slots.length + 1) * fibBalancedCapacity cells.length := by
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
      s ≤ fibBalancedCapacity cells.length := by
    intro s hs
    dsimp [sizes, supportFibreSizes] at hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    dsimp [supportFibreSize, weight]
    exact relevant_noCertified_supportWeight_fibre_fibonacci_bound
      m e r0 hrun hr0 globalLo globalHi cells slots ks q
      frame hfullRelevant hks hnoAbsorb hnd
  have hagg := relevant_sum_le_length_mul sizes
    (fibBalancedCapacity cells.length) heach
  rw [hsum, hlen] at hagg
  exact hagg

/-- **Constructible unconditional Fibonacci upper bound.** -/
theorem relevant_unconditional_global_fibonacci_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0
      globalLo globalHi cells)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤
      (slots.length + 1) * fibBalancedCapacity cells.length + 4 := by
  classical
  by_cases hex : ∃ k,
      globalLo ≤ k ∧ k ≤ globalHi ∧
        CertifiedLobeAbsorptionAt m e r0 k
  · let candidates := (List.range (globalHi + 1)).filter fun k =>
        globalLo ≤ k ∧ CertifiedLobeAbsorptionAt m e r0 k
    rcases hex with ⟨w, hwLo, hwHi, hwCert⟩
    have hwCand : w ∈ candidates := by
      dsimp [candidates]
      exact List.mem_filter.mpr
        ⟨List.mem_range.mpr (by omega),
          decide_eq_true ⟨hwLo, hwCert⟩⟩
    cases hcandidates : candidates with
    | nil =>
        rw [hcandidates] at hwCand
        cases hwCand
    | cons x rest =>
        let k0 := fibreMinFrom x rest
        have hk0Cand : k0 ∈ candidates := by
          rw [hcandidates]
          exact fibreMinFrom_mem x rest
        have hk0InFilter :
            k0 ∈ (List.range (globalHi + 1)).filter
              (fun k => globalLo ≤ k ∧
                CertifiedLobeAbsorptionAt m e r0 k) := by
          simpa only [candidates] using hk0Cand
        have hk0Filter := List.mem_filter.mp hk0InFilter
        have hk0Cond :
            globalLo ≤ k0 ∧ CertifiedLobeAbsorptionAt m e r0 k0 :=
          of_decide_eq_true hk0Filter.2
        have hk0Lo : globalLo ≤ k0 := hk0Cond.1
        have hk0Hi : k0 ≤ globalHi := by
          have hrange : k0 < globalHi + 1 :=
            List.mem_range.mp hk0Filter.1
          omega
        have hk0Cert : CertifiedLobeAbsorptionAt m e r0 k0 :=
          hk0Cond.2
        let pre := ks.filter (fun k => k < k0)
        let tail := ks.filter (fun k => k0 ≤ k)
        have hsplit : pre.length + tail.length = ks.length := by
          dsimp [pre, tail]
          exact relevant_filter_lt_ge_length k0 ks
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
          have hkInFilter :
              k ∈ ks.filter (fun k => k0 ≤ k) := by
            simpa only [tail] using hk
          exact of_decide_eq_true
            (List.mem_filter.mp hkInFilter).2
        have htailCount : tail.length ≤ 4 :=
          certifiedLobeAbsorption_snapshot_count m e r0
            hrun hk0Cert cells tail htailTimes hndTail
        by_cases hpre : globalLo < k0
        · let preHi := k0 - 1
          have hpreHiGlobal : preHi ≤ globalHi := by
            dsimp [preHi]
            omega
          have hpreTimes : ∀ k ∈ pre,
              globalLo ≤ k ∧ k ≤ preHi := by
            intro k hk
            have hkInFilter :
                k ∈ ks.filter (fun k => k < k0) := by
              simpa only [pre] using hk
            have hkFilter := List.mem_filter.mp hkInFilter
            have hkLt : k < k0 :=
              of_decide_eq_true hkFilter.2
            have hkGlobal := hks k hkFilter.1
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
              exact List.mem_filter.mpr
                ⟨hkRange, decide_eq_true ⟨hkLo, hcert⟩⟩
            have hkList : k ∈ x :: rest := by
              rw [← hcandidates]
              exact hkCandidates
            have hk0le : k0 ≤ k := by
              dsimp [k0]
              exact fibreMinFrom_le_mem x rest k hkList
            dsimp [preHi] at hkHi
            omega
          have hfullPre : FullEdgesRelevant m e r0
              globalLo preHi cells := by
            intro k hkLo hkHi f hf
            exact hfullRelevant k hkLo
              (Nat.le_trans hkHi hpreHiGlobal) f hf
          have hpreCount : pre.length ≤
              (slots.length + 1) *
                fibBalancedCapacity cells.length :=
            relevant_noCertified_global_fibonacci_bound m e r0
              hrun hr0 globalLo preHi cells slots pre frame
              hfullPre hpreTimes hnoPre hndPre
          omega
        · have hk0eq : k0 = globalLo := by omega
          have hallTail : ∀ k ∈ ks, k0 ≤ k := by
            intro k hk
            rw [hk0eq]
            exact (hks k hk).1
          have hallCount : ks.length ≤ 4 :=
            certifiedLobeAbsorption_snapshot_count m e r0
              hrun hk0Cert cells ks hallTail hnd
          omega
  · have hno : NoCertifiedLobeAbsorptionIn m e r0
        globalLo globalHi := by
      intro k hkLo hkHi hcert
      exact hex ⟨k, hkLo, hkHi, hcert⟩
    have hbase := relevant_noCertified_global_fibonacci_bound m e r0
      hrun hr0 globalLo globalHi cells slots ks frame
      hfullRelevant hks hno hnd
    omega

end Echo
