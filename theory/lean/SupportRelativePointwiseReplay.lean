import PairedPointwiseReplayCore
import SupportRelativeNoLobe

/-!
# Pointwise replay relative to the occupied support

A represented coordinate is now classified as

1. an occupied active lobe, encoded by one endpoint bit;
2. a cell with no occupied lobe anywhere in the fixed-support interval; or
3. a coordinate already frozen throughout the interval.

This strictly weakens the old structural `CoreNoLobe` cover and permits dormant
internal jump edges.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Exhaustive support-relative replay classification. -/
def PairedSupportReplayCover
    (lo hi : Nat) (cells lobes : List Nat) : Prop :=
  ∀ c ∈ cells,
    (∃ a, a ∈ lobes ∧ m.cellOf a = c) ∨
    PairedNoOccupiedLobe m e r0 lo hi c ∨
    PairedPointFrozen m e r0 lo hi c

/-- Ordered pointwise replay with support-relative non-lobe cells. -/
theorem paired_support_pointwise_replay_of_le
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hfullRep : PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : PairedSupportReplayCover m e r0 lo hi cells lobes)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    {i j : Nat}
    (hiLo : lo ≤ i) (hij : i ≤ j) (hjHi : j ≤ hi)
    (hfullBits : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j)
    (hlobeBits : coreLobeBits m e r0 lobes i =
      coreLobeBits m e r0 lobes j) :
    snap m e r0 cells i = snap m e r0 cells j := by
  have hiHi : i ≤ hi := by omega
  have hjLo : lo ≤ j := by omega
  have hsupport := pairedSupportFixed_between_of_le m e r0
    hfixed hiLo hij hjHi
  have hlobeRegs := coreLobeBits_eq_regs m e r0 lobes
    hloop (hocc i hiLo hiHi) (hocc j hjLo hjHi) hlobeBits
  unfold snap
  apply List.map_congr_left
  intro c hc
  rcases hcover c hc with hlobe | hother
  · rcases hlobe with ⟨a, ha, hac⟩
    rw [← hac]
    exact hlobeRegs a ha
  · rcases hother with hnon | hfrozen
    · by_cases hreach : ∃ f,
          Full m e r0 i f ∧ GraphReach m e r0 i f c
      · rcases hreach with ⟨f, hfi, hri⟩
        rcases hfullRep i ⟨hiLo, hiHi⟩ f hfi with
          ⟨g, hg, hfg⟩
        have hgi := pairedFull_of_sameEdge m e r0 hfg hfi
        have hrgi := graphReach_of_sameEdge m e r0 hfg hri
        have hgj := paired_full_of_bits_eq m e r0
          edges hg hfullBits hgi
        exact reg_eq_of_paired_full_reach m e r0
          hsupport hgi hgj hrgi
      · have hno : PairedNoFullReach m e r0 i c := by
          intro f hf hr
          exact hreach ⟨f, hf, hr⟩
        have hsubfixed := pairedSupportFixed_restrict m e r0
          hfixed hiLo hij hjHi
        have hsubNoLobe :
            PairedNoOccupiedLobe m e r0 i j c := by
          intro k hkLo hkHi
          exact hnon k (Nat.le_trans hiLo hkLo)
            (Nat.le_trans hkHi hjHi)
        exact (reg_frozen_of_pairedNoFullReach_supportRelative
          m e r0 hrun hr0 hij hsubfixed hsubNoLobe hno).symm
    · exact hfrozen i hiLo hiHi j hjLo hjHi

/-- Symmetric arbitrary-time support-relative replay. -/
theorem paired_support_pointwise_replay
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hfullRep : PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : PairedSupportReplayCover m e r0 lo hi cells lobes)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    {i j : Nat}
    (hiI : lo ≤ i ∧ i ≤ hi) (hjI : lo ≤ j ∧ j ≤ hi)
    (hfullBits : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j)
    (hlobeBits : coreLobeBits m e r0 lobes i =
      coreLobeBits m e r0 lobes j) :
    snap m e r0 cells i = snap m e r0 cells j := by
  by_cases hij : i ≤ j
  · exact paired_support_pointwise_replay_of_le m e r0 hrun hr0
      lo hi cells edges lobes hfixed hfullRep hcover hloop hocc
      hiI.1 hij hjI.2 hfullBits hlobeBits
  · have hji : j ≤ i := by omega
    exact (paired_support_pointwise_replay_of_le m e r0 hrun hr0
      lo hi cells edges lobes hfixed hfullRep hcover hloop hocc
      hjI.1 hji hiI.2 hfullBits.symm hlobeBits.symm).symm

/-- Equal corrected block codes replay the complete support-relative snapshot. -/
theorem paired_support_block_code_replay
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hfullRep : PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : PairedSupportReplayCover m e r0 lo hi cells lobes)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    {i j : Nat}
    (hiI : lo ≤ i ∧ i ≤ hi) (hjI : lo ≤ j ∧ j ≤ hi)
    (hcode : blockCoreAbstractCode m e r0 edges
        (coreLobeBits m e r0 lobes) i =
      blockCoreAbstractCode m e r0 edges
        (coreLobeBits m e r0 lobes) j) :
    snap m e r0 cells i = snap m e r0 cells j := by
  have hfullSep := congrArg Prod.fst hcode
  have hlobe := congrArg Prod.snd hcode
  have hfull : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j :=
    blockCoreSeparate_injective hfullSep
  exact paired_support_pointwise_replay m e r0 hrun hr0
    lo hi cells edges lobes hfixed hfullRep hcover hloop hocc
    hiI hjI hfull hlobe

end Echo
