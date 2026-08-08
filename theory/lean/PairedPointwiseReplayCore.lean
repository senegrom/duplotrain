import PairedNoFullReachFreeze
import LobeBooleanCodeCore
import BlockAbstractEpochBoundCore

/-!
# Complete pointwise replay on the paired-walk model

Every represented cell belongs to one of three classes:

1. an active lobe, encoded by one Boolean endpoint bit;
2. a non-lobe cell, replayed from a represented full root or frozen by absence
   of full reach; or
3. a coordinate already constant throughout the epoch.

Equal separated full-edge indicators and equal lobe bits therefore replay the
entire represented snapshot, without component decomposition.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Every full edge at a selected time has a representative in `edges`. -/
def PairedAllFullRepresented
    (times : Nat → Prop) (edges : List Nat) : Prop :=
  ∀ k, times k → ∀ f, Full m e r0 k f →
    ∃ g, g ∈ edges ∧ SameEdge m f g

/-- One coordinate is constant over the interval. -/
def PairedPointFrozen (lo hi c : Nat) : Prop :=
  ∀ i, lo ≤ i → i ≤ hi → ∀ j, lo ≤ j → j ≤ hi,
    reg m e r0 i c = reg m e r0 j c

/-- Exhaustive replay classification. -/
def PairedReplayCover
    (lo hi : Nat) (cells lobes : List Nat) : Prop :=
  ∀ c ∈ cells,
    (∃ a, a ∈ lobes ∧ m.cellOf a = c) ∨
    CoreNoLobe m c ∨ PairedPointFrozen m e r0 lo hi c

private theorem paired_map_eq_at_mem
    {α β : Type} {xs : List α} {p q : α → β}
    (h : xs.map p = xs.map q) {x : α} (hx : x ∈ xs) :
    p x = q x := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hh := congrArg List.head? h
        simpa using hh
      · have ht := congrArg List.tail h
        simp only [List.map_cons, List.tail_cons] at ht
        exact ih ht hx

/-- Equal full-bit vectors preserve each represented full edge. -/
theorem paired_full_of_bits_eq
    (edges : List Nat) {i j g : Nat}
    (hg : g ∈ edges)
    (hbits : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j)
    (hfull : Full m e r0 i g) :
    Full m e r0 j g := by
  classical
  unfold endpointFullBits at hbits
  have hb : decide (Full m e r0 i g) =
      decide (Full m e r0 j g) :=
    paired_map_eq_at_mem hbits hg
  have hi : decide (Full m e r0 i g) = true :=
    decide_eq_true hfull
  have hj : decide (Full m e r0 j g) = true := by
    rw [← hb]
    exact hi
  exact of_decide_eq_true hj

/-- Ordered pointwise replay. -/
theorem paired_pointwise_replay_of_le
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hfullRep : PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : PairedReplayCover m e r0 lo hi cells lobes)
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
        exact (reg_frozen_of_pairedNoFullReach m e r0 hrun hr0
          hij hsubfixed hnon hno).symm
    · exact hfrozen i hiLo hiHi j hjLo hjHi

/-- Symmetric arbitrary-time replay. -/
theorem paired_pointwise_replay
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hfullRep : PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : PairedReplayCover m e r0 lo hi cells lobes)
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
  · exact paired_pointwise_replay_of_le m e r0 hrun hr0
      lo hi cells edges lobes hfixed hfullRep hcover hloop hocc
      hiI.1 hij hjI.2 hfullBits hlobeBits
  · have hji : j ≤ i := by omega
    exact (paired_pointwise_replay_of_le m e r0 hrun hr0
      lo hi cells edges lobes hfixed hfullRep hcover hloop hocc
      hjI.1 hji hiI.2 hfullBits.symm hlobeBits.symm).symm

/-- Equal corrected block codes replay the complete snapshot. -/
theorem paired_block_code_replay
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hfullRep : PairedAllFullRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : PairedReplayCover m e r0 lo hi cells lobes)
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
  exact paired_pointwise_replay m e r0 hrun hr0
    lo hi cells edges lobes hfixed hfullRep hcover hloop hocc
    hiI hjI hfull hlobe

end Echo
