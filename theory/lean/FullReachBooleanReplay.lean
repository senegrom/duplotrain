import AbstractSparseEpochBound
import LobeBooleanCode
import ReachReplay

/-!
# Complete replay from full-edge and lobe Boolean codes

At two times with equal occupied support:

* equality of the full-edge indicator preserves every listed full root;
* support reachability transports unchanged;
* `ReachReplay` therefore replays every cell in a full-edge component;
* equality of the lobe Boolean code replays every active lobe register; and
* an explicitly frozen residual block adds no code choices.

This supplies the replay hypothesis of `AbstractSparseEpochBound` directly from
machine structure.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

private theorem map_eq_value_at_mem
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

/-- Equality of full-bit vectors preserves fullness of each represented edge. -/
theorem endpointFull_of_bits_eq
    (edges : List Nat) {i j f : Nat}
    (hf : f ∈ edges)
    (hbits : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j)
    (hfull : Full m e r0 i f) :
    Full m e r0 j f := by
  classical
  unfold endpointFullBits at hbits
  have hb : decide (Full m e r0 i f) =
      decide (Full m e r0 j f) :=
    map_eq_value_at_mem hbits hf
  have hi : decide (Full m e r0 i f) = true :=
    decide_eq_true hfull
  have hj : decide (Full m e r0 j f) = true := by
    rw [← hb]
    exact hi
  exact of_decide_eq_true hj

/-- Reachability transports across equal occupied supports. -/
theorem reachFromFull_support_congr
    {i j f c : Nat}
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hreach : ReachFromFull m e r0 i f c) :
    ReachFromFull m e r0 j f c := by
  induction hreach with
  | left => exact ReachFromFull.left
  | right => exact ReachFromFull.right
  | @step c d hprev hstep ih =>
      apply ReachFromFull.step ih
      rcases hstep with ⟨s, hocc, hsrc, hdst⟩
      exact ⟨s, (hsupport s).mp hocc, hsrc, hdst⟩

/-- A common full root and common support replay one register. -/
theorem reg_eq_of_full_reach
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

/-- Every variable cell is support-reachable from a represented full edge at
every epoch time. -/
def FullReachCovered
    (times : Nat → Prop)
    (edges variable : List Nat) : Prop :=
  ∀ k, times k → ∀ c ∈ variable,
    ∃ f, f ∈ edges ∧ Full m e r0 k f ∧
      ReachFromFull m e r0 k f c

/-- Equal full indicators replay the entire full-reachable block. -/
theorem fullReach_snap_replay
    (times : Nat → Prop)
    (edges variable : List Nat)
    (hcover : FullReachCovered m e r0 times edges variable)
    {i j : Nat} (hi : times i) (hj : times j)
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hbits : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j) :
    snap m e r0 variable i = snap m e r0 variable j := by
  unfold snap
  apply List.map_congr_left
  intro c hc
  rcases hcover i hi c hc with ⟨f, hf, hfi, hri⟩
  have hfj := endpointFull_of_bits_eq m e r0 edges
    hf hbits hfi
  have hrj := reachFromFull_support_congr m e r0
    hsupport hri
  exact reg_eq_of_full_reach m e r0 hfi hfj hri hrj

/-- A residual block has constant snapshot over the selected times. -/
def SnapshotFrozen (times : Nat → Prop) (frozen : List Nat) : Prop :=
  ∀ i, times i → ∀ j, times j,
    snap m e r0 frozen i = snap m e r0 frozen j

/-- Complete represented cell list. -/
def fullLobeFrozenCells
    (variable lobes frozen : List Nat) : List Nat :=
  variable ++ booleanLobeCells m lobes ++ frozen

/-- Equal abstract codes replay the complete represented snapshot. -/
theorem full_lobe_boolean_code_replay
    (times : Nat → Prop)
    (edges variable lobes frozen : List Nat)
    (hcover : FullReachCovered m e r0 times edges variable)
    (hfreeze : SnapshotFrozen m e r0 times frozen)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, times k → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    {i j : Nat} (hi : times i) (hj : times j)
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hcode : abstractSparseCode m e r0 edges
        (booleanLobeCode m e r0 lobes) i =
      abstractSparseCode m e r0 edges
        (booleanLobeCode m e r0 lobes) j) :
    snap m e r0 (fullLobeFrozenCells m variable lobes frozen) i =
      snap m e r0 (fullLobeFrozenCells m variable lobes frozen) j := by
  have hfullSep := congrArg Prod.fst hcode
  have hlobe := congrArg Prod.snd hcode
  have hfull : endpointFullBits m e r0 edges i =
      endpointFullBits m e r0 edges j :=
    sparseSeparateCore_injective hfullSep
  have hv := fullReach_snap_replay m e r0 times
    edges variable hcover hi hj hsupport hfull
  have hl := booleanLobeCode_eq_snap m e r0 lobes
    hloop (hocc i hi) (hocc j hj) hlobe
  have hf := hfreeze i hi j hj
  unfold fullLobeFrozenCells snap at hv hl hf ⊢
  simp only [List.map_append]
  rw [hv, hl, hf]

/-- **Concrete strict epoch bound from full reachability, lobe occupancy, and a
frozen residual block.** -/
theorem full_reach_lobe_epoch_bound
    (times : Nat → Prop)
    (edges variable lobes frozen ks : List Nat)
    (C M F : Nat)
    (hcover : FullReachCovered m e r0 times edges variable)
    (hfreeze : SnapshotFrozen m e r0 times frozen)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, times k → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      endpointTrueCount (endpointFullBits m e r0 edges k) = F)
    (hnd : (ks.map (snap m e r0
      (fullLobeFrozenCells m variable lobes frozen))).Nodup)
    (hC : C = lobes.length + M)
    (hhalf : lobes.length ≤ M) :
    sparseCoreEighth ks.length ≤ 2^(7*C + 8) := by
  apply abstract_sparse_epoch_eighth_bound m e r0
    (fullLobeFrozenCells m variable lobes frozen)
    edges ks (booleanLobeCode m e r0 lobes)
    C M lobes.length F hEF
  · intro k hk
    rw [sparseTrueCount_eq_endpointTrueCount]
    exact hfull k hk
  · intro k hk
    exact booleanLobeCode_length m e r0 lobes k
  · intro i hiK j hjK hc
    exact full_lobe_boolean_code_replay m e r0 times
      edges variable lobes frozen hcover hfreeze hloop hocc
      (hks i hiK) (hks j hjK)
      (hsupport i hiK j hjK) hc
  · exact hnd
  · exact hC
  · exact hhalf

end Echo
