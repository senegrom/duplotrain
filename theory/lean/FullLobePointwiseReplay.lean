import SupportFixedBetween
import LobeBooleanCode
import AbstractSparseEpochBound

/-!
# Pointwise complete replay without component decomposition

For every represented cell:

* an active lobe cell is replayed by its Boolean endpoint bit;
* a non-lobe cell reached by a full edge is replayed from the common full root;
* a non-lobe cell reached by no full edge is frozen by full-reach persistence.

Thus equal full-edge indicators and equal lobe bits determine the complete
snapshot throughout a fixed-support interval.  No explicit tree/unicyclic
component partition is required.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Every full edge has a representative in the finite edge list. -/
def AllFullEdgesRepresented
    (times : Nat → Prop) (edges : List Nat) : Prop :=
  ∀ k, times k → ∀ f, Full m e r0 k f →
    ∃ g, g ∈ edges ∧ SameEdge m f g

/-- Every listed cell is either represented by an active lobe or is non-lobed. -/
def LobeOrNonLobe (cells lobes : List Nat) : Prop :=
  ∀ c ∈ cells,
    (∃ a, a ∈ lobes ∧ m.cellOf a = c) ∨ CoreNoLobe m c

private theorem pointwise_map_eq_at_mem
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

/-- Equal full indicator vectors preserve represented full edges. -/
theorem pointwise_full_of_bits_eq
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
    pointwise_map_eq_at_mem hbits hg
  have hi : decide (Full m e r0 i g) = true :=
    decide_eq_true hfull
  have hj : decide (Full m e r0 j g) = true := by
    rw [← hb]
    exact hi
  exact of_decide_eq_true hj

/-- Common full root plus common support replay one register. -/
theorem pointwise_reg_replay_from_full
    {i j f c : Nat}
    (hfi : Full m e r0 i f)
    (hfj : Full m e r0 j f)
    (hri : ReachFromFull m e r0 i f c)
    (hrj : ReachFromFull m e r0 j f c) :
    reg m e r0 i c = reg m e r0 j c := by
  have hrootI : RootedCells m e r0 i f [c] :=
    rootedCells_of_reach m e r0 hfi
      (fun d hd => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        subst d
        exact hri)
  have hrootJ : RootedCells m e r0 j f [c] :=
    rootedCells_of_reach m e r0 hfj
      (fun d hd => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        subst d
        exact hrj)
  exact rootedCells_snapshot_eq m e r0 hrootI hrootJ
    c List.mem_cons_self

/-- Ordered complete replay. -/
theorem full_lobe_pointwise_replay_of_le
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hfullRep : AllFullEdgesRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : LobeOrNonLobe m cells lobes)
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
  rcases hcover c hc with hlobe | hnon
  · rcases hlobe with ⟨a, ha, hac⟩
    rw [← hac]
    exact hlobeRegs a ha
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

/-- Symmetric complete replay for arbitrary two interval times. -/
theorem full_lobe_pointwise_replay
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hfullRep : AllFullEdgesRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : LobeOrNonLobe m cells lobes)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    {i j : Nat}
    (hiLo : lo ≤ i) (hiHi : i ≤ hi)
    (hjLo : lo ≤ j) (hjHi : j ≤ hi)
    (hfullBits : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j)
    (hlobeBits : booleanLobeCode m e r0 lobes i =
      booleanLobeCode m e r0 lobes j) :
    snap m e r0 cells i = snap m e r0 cells j := by
  by_cases hij : i ≤ j
  · exact full_lobe_pointwise_replay_of_le m e r0 hrun hr0
      lo hi cells edges lobes hfixed hfullRep hcover hloop hocc
      hiLo hij hjHi hfullBits hlobeBits
  · have hji : j ≤ i := by omega
    exact (full_lobe_pointwise_replay_of_le m e r0 hrun hr0
      lo hi cells edges lobes hfixed hfullRep hcover hloop hocc
      hjLo hji hiHi hfullBits.symm hlobeBits.symm).symm

/-- Equality of the combined abstract code replays the complete snapshot. -/
theorem full_lobe_abstract_code_replay
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat)
    (cells edges lobes : List Nat)
    (hfixed : CoreSupportFixed m e r0 lo hi)
    (hfullRep : AllFullEdgesRepresented m e r0
      (fun k => lo ≤ k ∧ k ≤ hi) edges)
    (hcover : LobeOrNonLobe m cells lobes)
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
  exact full_lobe_pointwise_replay m e r0 hrun hr0
    lo hi cells edges lobes hfixed hfullRep hcover hloop hocc
    hiI.1 hiI.2 hjI.1 hjI.2 hfull hlobe

end Echo
