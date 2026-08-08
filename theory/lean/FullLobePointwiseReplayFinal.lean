import FullLobePointwiseReplay

/-!
# Complete pointwise replay with inactive lobes

Every represented cell belongs to one of three replay classes:

1. an active lobe, encoded by one Boolean endpoint bit;
2. a structurally non-lobe cell, handled by full reachability or no-full
   freezing; or
3. a cell whose register is already constant throughout the epoch.

The third class lets inactive lobe cells cost no Boolean coordinate.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- One register is constant over the selected interval. -/
def PointwiseFrozen (lo hi c : Nat) : Prop :=
  ∀ i, lo ≤ i → i ≤ hi → ∀ j, lo ≤ j → j ≤ hi,
    reg m e r0 i c = reg m e r0 j c

/-- Exhaustive replay classification for a represented cell. -/
def ActiveLobeOrNonLobeOrFrozen
    (lo hi : Nat) (cells lobes : List Nat) : Prop :=
  ∀ c ∈ cells,
    (∃ a, a ∈ lobes ∧ m.cellOf a = c) ∨
    CoreNoLobe m c ∨ PointwiseFrozen m e r0 lo hi c

/-- Ordered complete replay with the frozen third class. -/
theorem full_lobe_pointwise_replay_final_of_le
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hfullRep : AllFullEdgesRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : ActiveLobeOrNonLobeOrFrozen m e r0
      lo hi cells lobes)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    {i j : Nat}
    (hiLo : lo ≤ i) (hij : i ≤ j) (hjHi : j ≤ hi)
    (hfullBits : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j)
    (hlobeBits : booleanLobeCode m e r0 lobes i =
      booleanLobeCode m e r0 lobes j) :
    snap m e r0 cells i = snap m e r0 cells j := by
  have hiHi : i ≤ hi := by omega
  have hjLo : lo ≤ j := by omega
  have hsupport := coreSupportFixed_between_of_le m e r0
    hfixed hiLo hij hjHi
  have hlobeRegs := booleanLobeCode_eq_regs m e r0 lobes
    hloop (hocc i hiLo hiHi) (hocc j hjLo hjHi) hlobeBits
  unfold snap
  apply List.map_congr_left
  intro c hc
  rcases hcover c hc with hlobe | hstruct
  · rcases hlobe with ⟨a, ha, hac⟩
    rw [← hac]
    exact hlobeRegs a ha
  · rcases hstruct with hnon | hfrozen
    · by_cases hreach : ∃ f,
          Full m e r0 i f ∧ ReachFromFull m e r0 i f c
      · rcases hreach with ⟨f, hfi, hri⟩
        rcases hfullRep i ⟨hiLo, hiHi⟩ f hfi with
          ⟨g, hg, hfg⟩
        have hgi := frp_full_of_sameEdge m e r0 hfg hfi
        have hrgi := frp_reach_of_sameEdge m e r0 hfg hri
        have hgj := pointwise_full_of_bits_eq m e r0
          edges hg hfullBits hgi
        have hrgj := frp_reach_support_congr m e r0
          hsupport hrgi
        exact pointwise_reg_replay_from_full m e r0
          hgi hgj hrgi hrgj
      · have hno : CoreNoFullReach m e r0 i c := by
          intro f hf hr
          exact hreach ⟨f, hf, hr⟩
        have hsubfixed := coreSupportFixed_restrict m e r0
          hfixed hiLo hij hjHi
        exact (reg_frozen_of_noFullReach m e r0 hrun hr0
          hij hsubfixed hnon hno).symm
    · exact hfrozen i hiLo hiHi j hjLo hjHi

/-- Symmetric arbitrary-time replay. -/
theorem full_lobe_pointwise_replay_final
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hfullRep : AllFullEdgesRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : ActiveLobeOrNonLobeOrFrozen m e r0
      lo hi cells lobes)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    {i j : Nat}
    (hiI : lo ≤ i ∧ i ≤ hi) (hjI : lo ≤ j ∧ j ≤ hi)
    (hfullBits : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j)
    (hlobeBits : booleanLobeCode m e r0 lobes i =
      booleanLobeCode m e r0 lobes j) :
    snap m e r0 cells i = snap m e r0 cells j := by
  by_cases hij : i ≤ j
  · exact full_lobe_pointwise_replay_final_of_le m e r0
      hrun hr0 lo hi cells edges lobes hfixed hfullRep hcover
      hloop hocc hiI.1 hij hjI.2 hfullBits hlobeBits
  · have hji : j ≤ i := by omega
    exact (full_lobe_pointwise_replay_final_of_le m e r0
      hrun hr0 lo hi cells edges lobes hfixed hfullRep hcover
      hloop hocc hjI.1 hji hiI.2 hfullBits.symm hlobeBits.symm).symm

/-- Equal combined abstract codes replay the complete snapshot. -/
theorem full_lobe_abstract_code_replay_final
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hfullRep : AllFullEdgesRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : ActiveLobeOrNonLobeOrFrozen m e r0
      lo hi cells lobes)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    {i j : Nat}
    (hiI : lo ≤ i ∧ i ≤ hi) (hjI : lo ≤ j ∧ j ≤ hi)
    (hcode : abstractSparseCode m e r0 edges
        (booleanLobeCode m e r0 lobes) i =
      abstractSparseCode m e r0 edges
        (booleanLobeCode m e r0 lobes) j) :
    snap m e r0 cells i = snap m e r0 cells j := by
  have hfullSep := congrArg Prod.fst hcode
  have hlobe := congrArg Prod.snd hcode
  have hfull : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j :=
    sparseSeparateCore_injective hfullSep
  exact full_lobe_pointwise_replay_final m e r0 hrun hr0
    lo hi cells edges lobes hfixed hfullRep hcover hloop hocc
    hiI hjI hfull hlobe

end Echo
