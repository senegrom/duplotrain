import FullLobeSparseCode

/-!
# Full-edge markers replay the projected snapshot

Suppose two times have the same occupied support and the same full/non-full
indicator on a representative edge list.  For a non-lobe cell, choose any full
edge from which that cell is support-reachable.  Reachability transports across
the unchanged support, while equality of indicators keeps the chosen edge full.
The one-cell `TreeBlockCert` built from this common root then replays the cell's
register via `treeCode_eq_snap_eq`.

Lobe cells replay directly from equality of their exact endpoint list.  Thus a
simple coverage condition establishes the abstract `FullLobeDetermines`
property required by the component-free sparse count.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Equality of maps gives equality of the mapped value at every listed
argument. -/
private theorem map_eq_at_mem
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

/-- Support reachability transports across pointwise-equal supports. -/
theorem reachFromFull_congr_support
    {i j f c : Nat}
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (h : ReachFromFull m e r0 i f c) :
    ReachFromFull m e r0 j f c := by
  induction h with
  | left => exact ReachFromFull.left
  | right => exact ReachFromFull.right
  | @step c d hreach hstep ih =>
      apply ReachFromFull.step ih
      rcases hstep with ⟨s, hocc, hsrc, hdst⟩
      exact ⟨s, (hsupport s).mp hocc, hsrc, hdst⟩

/-- Equality of full-bit vectors preserves fullness of every listed edge. -/
theorem full_of_fullBits_eq
    (edges : List Nat) {i j f : Nat}
    (hf : f ∈ edges)
    (hbits : fullBits m e r0 edges i =
      fullBits m e r0 edges j)
    (hfull : Full m e r0 i f) :
    Full m e r0 j f := by
  have hb : decide (Full m e r0 i f) =
      decide (Full m e r0 j f) := by
    unfold fullBits at hbits
    exact map_eq_at_mem hbits hf
  have hi : decide (Full m e r0 i f) = true :=
    decide_eq_true hfull
  have hj : decide (Full m e r0 j f) = true := by
    rw [← hb]
    exact hi
  exact of_decide_eq_true hj

/-- Equality of exact lobe lists preserves the register in every represented
lobe cell. -/
theorem reg_eq_of_lobeCode_eq
    (lobes : List Nat) {i j a : Nat}
    (ha : a ∈ lobes)
    (hcode : lobeCode m e r0 lobes i =
      lobeCode m e r0 lobes j) :
    reg m e r0 i (m.cellOf a) =
      reg m e r0 j (m.cellOf a) := by
  unfold lobeCode at hcode
  exact map_eq_at_mem hcode ha

/-- Pair of selected times. -/
def PairTimes (i j k : Nat) : Prop := k = i ∨ k = j

/-- A common full marker and support reachability replay one cell. -/
theorem reg_eq_of_common_full_reach
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j f c : Nat}
    (hfi : Full m e r0 i f)
    (hfj : Full m e r0 j f)
    (hri : ReachFromFull m e r0 i f c)
    (hrj : ReachFromFull m e r0 j f c)
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s) :
    reg m e r0 i c = reg m e r0 j c := by
  let pair : Nat → Prop := PairTimes i j
  have hfull : ∀ k, pair k → Full m e r0 k f := by
    intro k hk
    rcases hk with rfl | rfl
    · exact hfi
    · exact hfj
  have hreach : ∀ k, pair k →
      ReachableCells m e r0 k f [c] := by
    intro k hk d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst d
    rcases hk with rfl | rfl
    · exact hri
    · exact hrj
  let block : TreeBlockCert m e r0 pair :=
    treeBlockOfReach m e r0 pair [c] [f] (fun _ => f)
      (fun k hk => List.mem_cons_self)
      hfull hreach
  have hcode : treeCode m e r0 [block] i =
      treeCode m e r0 [block] j := by
    rfl
  have hsnap := treeCode_eq_snap_eq m e r0 hr0 [block]
    (Or.inl rfl) (Or.inr rfl) hsupport hcode
  simp [snap] at hsnap
  exact hsnap.symm

/-- Every covered cell is either represented by a lobe endpoint or reachable
from a listed full edge. -/
def FullLobeCovered
    (edges lobes cells : List Nat) : Prop :=
  ∀ k, times k → ∀ c ∈ cells,
    (∃ a, a ∈ lobes ∧ m.cellOf a = c) ∨
    (∃ f, f ∈ edges ∧ Full m e r0 k f ∧
      ReachFromFull m e r0 k f c)

/-- **Coverage implies exact replay.** -/
theorem fullLobeDetermines_of_covered
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (edges lobes cells : List Nat)
    (hcover : FullLobeCovered m e r0 times edges lobes cells) :
    FullLobeDetermines m e r0 times edges lobes cells := by
  intro i hi j hj hsupport hfullBits hlobeCode
  unfold snap
  apply List.map_congr_left
  intro c hc
  rcases hcover i hi c hc with hlobe | htree
  · rcases hlobe with ⟨a, ha, hac⟩
    rw [← hac]
    exact reg_eq_of_lobeCode_eq m e r0 lobes ha hlobeCode
  · rcases htree with ⟨f, hf, hfi, hri⟩
    have hfj := full_of_fullBits_eq m e r0 edges hf
      hfullBits hfi
    have hrj := reachFromFull_congr_support m e r0
      hsupport hri
    exact reg_eq_of_common_full_reach m e r0 hr0
      hfi hfj hri hrj hsupport

end Echo
