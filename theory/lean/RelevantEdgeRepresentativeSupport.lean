import RelevantCertifiedFibonacciEpochBound
import CanonicalEdgeRepsCore
import SupportWeightFibres

/-!
# Support epochs need one coordinate per physical jump edge

A relevant slot list is duplicate-free, closed under `bar`, and has no fixed
points in the proper frame.  The canonical representatives `s < bar s`
therefore contain exactly one element per physical edge.  Occupancy is
representative-independent, so equal support on those representatives already
fixes the whole relevant support.

This halves the support-weight coordinate count used by the global bound.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

private theorem edgeRep_nodup_subset_length
    {xs ys : List Nat}
    (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hsub' : ∀ z ∈ rest, z ∈ ys.erase x := by
        intro z hz
        have hzy := hsub z (List.mem_cons_of_mem _ hz)
        have hzx : z ≠ x := fun h => hnd.1 (h ▸ hz)
        exact (List.mem_erase_of_ne hzx).mpr hzy
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      simp only [List.length_cons]
      omega

/-- The endpoint expansion has exactly two entries per representative. -/
theorem standaloneEdgeEnds_length (edges : List Nat) :
    (standaloneEdgeEnds m edges).length = 2 * edges.length := by
  induction edges with
  | nil => rfl
  | cons s rest ih =>
      simp only [standaloneEdgeEnds, List.length_cons]
      rw [ih]
      omega

/-- In a bar-closed proper slot list, canonical edge endpoints are exactly the
original slots, hence there are half as many representatives as slots. -/
theorem canonicalEdgesCore_twice_length
    {cells slots : List Nat}
    (frame : ProperRelevantFiniteFrame m e r0 cells slots) :
    2 * (canonicalEdgesCore m slots).length = slots.length := by
  let ends := standaloneEdgeEnds m (canonicalEdgesCore m slots)
  have hendsNodup : ends.Nodup := by
    dsimp [ends]
    exact canonicalEdgeEndsCore_nodup m frame.slots_nodup
  have hto : ∀ x ∈ ends, x ∈ slots := by
    intro x hx
    dsimp [ends] at hx
    exact canonicalEdgeEndsCore_mem_slots m frame.bar_closed hx
  have hfrom : ∀ x ∈ slots, x ∈ ends := by
    intro x hx
    dsimp [ends]
    exact slot_mem_canonicalEdgeEndsCore m
      frame.bar_closed frame.bar_ne hx
  have hle1 := edgeRep_nodup_subset_length hendsNodup hto
  have hle2 := edgeRep_nodup_subset_length frame.slots_nodup hfrom
  have hlen : ends.length = slots.length := by omega
  dsimp [ends] at hlen
  rw [standaloneEdgeEnds_length] at hlen
  exact hlen

/-- Representative support equality determines support equality on every
listed slot. -/
theorem occupied_iff_of_edgeRep_supportSnap_eq
    {cells slots : List Nat}
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    {i j : Nat}
    (hsnap : supportSnap m e r0 (canonicalEdgesCore m slots) i =
      supportSnap m e r0 (canonicalEdgesCore m slots) j) :
    ∀ s ∈ slots, Occupied m e r0 i s ↔ Occupied m e r0 j s := by
  intro s hs
  rcases slot_has_canonicalEdgeCore m frame.bar_closed frame.bar_ne hs with
    ⟨g, hg, hsg⟩
  have hgEq := relevant_occupied_iff_of_supportSnap_eq
    m e r0 (canonicalEdgesCore m slots) hsnap g hg
  have hsi : Occupied m e r0 i s ↔ Occupied m e r0 i g :=
    occupied_sameEdge_iff m e r0 hsg
  have hsj : Occupied m e r0 j s ↔ Occupied m e r0 j g :=
    occupied_sameEdge_iff m e r0 hsg
  exact hsi.trans (hgEq.trans hsj.symm)

/-- Equal endpoint support on one representative per physical edge yields the
original global fixed-support interval. -/
theorem pairedSupportFixed_of_endpoint_edgeReps
    {cells slots : List Nat}
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat} (hlohi : lo ≤ hi)
    (hend : supportSnap m e r0 (canonicalEdgesCore m slots) lo =
      supportSnap m e r0 (canonicalEdgesCore m slots) hi) :
    PairedSupportFixed m e r0 lo hi := by
  have hon := occupied_iff_of_edgeRep_supportSnap_eq
    m e r0 frame hend
  have hall : ∀ s, Occupied m e r0 lo s ↔ Occupied m e r0 hi s := by
    intro s
    by_cases hs : s ∈ slots
    · exact hon s hs
    · exact unlisted_occupied_iff m e r0
        frame.toRelevantFiniteFrame hs
  exact pairedSupportFixed_of_endpoint_eq m e r0 hrun hr0 hlohi hall

/-- One representative-support-weight fibre has the Fibonacci epoch bound. -/
theorem relevant_noCertified_edgeWeight_fibre_fibonacci_bound
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
    (ks.filter (fun k => supportWeight m e r0
      (canonicalEdgesCore m slots) k = q)).length ≤
      fibBalancedCapacity cells.length := by
  let edges := canonicalEdgesCore m slots
  let fibre := ks.filter
    (fun k => supportWeight m e r0 edges k = q)
  cases hfibre : fibre with
  | nil =>
      have hlen :
          (ks.filter (fun k => supportWeight m e r0 edges k = q)).length = 0 := by
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
      have hloInFilter : lo ∈ ks.filter
          (fun k => supportWeight m e r0 edges k = q) := by
        simpa only [fibre] using hloMemF
      have hhiInFilter : hi ∈ ks.filter
          (fun k => supportWeight m e r0 edges k = q) := by
        simpa only [fibre] using hhiMemF
      have hloFilter := List.mem_filter.mp hloInFilter
      have hhiFilter := List.mem_filter.mp hhiInFilter
      have hloData : lo ∈ ks ∧
          supportWeight m e r0 edges lo = q :=
        ⟨hloFilter.1, of_decide_eq_true hloFilter.2⟩
      have hhiData : hi ∈ ks ∧
          supportWeight m e r0 edges hi = q :=
        ⟨hhiFilter.1, of_decide_eq_true hhiFilter.2⟩
      have hloGlobal := hks lo hloData.1
      have hhiGlobal := hks hi hhiData.1
      have hlohi : lo ≤ hi := by
        dsimp [lo, hi]
        exact fibreMinFrom_le_fibreMaxFrom x rest
      have hweight : supportWeight m e r0 edges lo =
          supportWeight m e r0 edges hi :=
        hloData.2.trans hhiData.2.symm
      have hsnap : supportSnap m e r0 edges lo =
          supportSnap m e r0 edges hi :=
        supportSnap_eq_of_weight_eq m e r0 hrun hr0 edges hweight
      have hfixed : PairedSupportFixed m e r0 lo hi := by
        dsimp [edges] at hsnap
        exact pairedSupportFixed_of_endpoint_edgeReps m e r0
          frame hrun hr0 hlohi hsnap
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
          ((ks.filter (fun k => supportWeight m e r0 edges k = q)).map
            (snap m e r0 cells)).Nodup :=
        map_filter_nodup (snap m e r0 cells)
          (fun k => supportWeight m e r0 edges k = q) hnd
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
          (ks.filter (fun k => supportWeight m e r0 edges k = q)).length =
            (x :: rest).length := by
        simpa [fibre] using congrArg List.length hfibre
      rw [hlen]
      exact hbound

end Echo
