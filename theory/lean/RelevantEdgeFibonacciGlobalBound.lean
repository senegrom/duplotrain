import RelevantEdgeRepresentativeSupport
import RelevantFibonacciGlobalBound

/-!
# Global Fibonacci bound using one support coordinate per physical edge
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

private theorem edgeFib_sum_le_length_mul
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
        x + rest.sum ≤ B + rest.length * B := Nat.add_le_add hx hi
        _ = (rest.length + 1) * B := by
          simp [Nat.add_mul, Nat.add_comm]

private theorem edgeFib_filter_lt_ge_length (cut : Nat) :
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

/-- No-certificate global count with one weight coordinate per physical edge. -/
theorem relevant_noCertified_edge_global_fibonacci_bound
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
      ((canonicalEdgesCore m slots).length + 1) *
        fibBalancedCapacity cells.length := by
  let edges := canonicalEdgesCore m slots
  let weight := supportWeight m e r0 edges
  let sizes := supportFibreSizes (edges.length + 1) weight ks
  have hsum : sizes.sum = ks.length := by
    dsimp [sizes]
    apply supportFibreSizes_sum (edges.length + 1) weight ks
    intro k hk
    dsimp [weight]
    exact supportWeight_lt m e r0 edges k
  have hlen : sizes.length = edges.length + 1 := by
    simp [sizes, supportFibreSizes]
  have heach : ∀ s ∈ sizes,
      s ≤ fibBalancedCapacity cells.length := by
    intro s hs
    dsimp [sizes, supportFibreSizes] at hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    dsimp [supportFibreSize, weight]
    exact relevant_noCertified_edgeWeight_fibre_fibonacci_bound
      m e r0 hrun hr0 globalLo globalHi cells slots ks q
      frame hfullRelevant hks hnoAbsorb hnd
  have hagg := edgeFib_sum_le_length_mul sizes
    (fibBalancedCapacity cells.length) heach
  rw [hsum, hlen] at hagg
  exact hagg

/-- **Unconditional global Fibonacci bound with the optimal physical-edge
support factor.** -/
theorem relevant_unconditional_edge_global_fibonacci_bound
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
      ((canonicalEdgesCore m slots).length + 1) *
        fibBalancedCapacity cells.length + 4 := by
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
        have hk0Cert : CertifiedLobeAbsorptionAt m e r0 k0 := hk0Cond.2
        let pre := ks.filter (fun k => k < k0)
        let tail := ks.filter (fun k => k0 ≤ k)
        have hsplit : pre.length + tail.length = ks.length := by
          dsimp [pre, tail]
          exact edgeFib_filter_lt_ge_length k0 ks
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
          have hkInFilter : k ∈ ks.filter (fun k => k0 ≤ k) := by
            simpa only [tail] using hk
          exact of_decide_eq_true (List.mem_filter.mp hkInFilter).2
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
            have hkInFilter : k ∈ ks.filter (fun k => k < k0) := by
              simpa only [pre] using hk
            have hkFilter := List.mem_filter.mp hkInFilter
            have hkLt : k < k0 := of_decide_eq_true hkFilter.2
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
              ((canonicalEdgesCore m slots).length + 1) *
                fibBalancedCapacity cells.length :=
            relevant_noCertified_edge_global_fibonacci_bound m e r0
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
    have hbase := relevant_noCertified_edge_global_fibonacci_bound m e r0
      hrun hr0 globalLo globalHi cells slots ks frame
      hfullRelevant hks hno hnd
    omega

/-- **Explicit `N`-cell complete-snapshot bound with one support coordinate per
physical edge.** -/
theorem relevant_finiteFrame_N_edge_fibonacci_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0
      globalLo globalHi cells)
    (hcells : cells.length ≤ N)
    (hslots : slots.length ≤ 2*N)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ (N + 1) * fibBalancedCapacity N + 4 := by
  have hbase := relevant_unconditional_edge_global_fibonacci_bound m e r0
    hrun hr0 globalLo globalHi cells slots ks frame
    hfullRelevant hks hnd
  have htwice := canonicalEdgesCore_twice_length m e r0 frame
  have hedges : (canonicalEdgesCore m slots).length ≤ N := by
    omega
  have hfactor : (canonicalEdgesCore m slots).length + 1 ≤ N + 1 := by
    omega
  have hcap : fibBalancedCapacity cells.length ≤ fibBalancedCapacity N :=
    fibBalancedCapacity_mono hcells
  have hmul :
      ((canonicalEdgesCore m slots).length + 1) *
          fibBalancedCapacity cells.length ≤
        (N + 1) * fibBalancedCapacity N :=
    Nat.mul_le_mul hfactor hcap
  omega

end Echo
