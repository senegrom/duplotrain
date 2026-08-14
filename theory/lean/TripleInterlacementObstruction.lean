import ConcreteCertifiedEchoRun
import RestorationFrameOrdering
import TrackCurveGrowth

/-!
# The physical triple-interlacement obstruction

This file attacks the strictly nested residue left by
`RestorationFrameOrdering`.  It uses the actual lazy-switch dynamics.

At raw track level, every trailing pass through switch `C` exits through
the unique stem `3*C`; consequently its next external port is always
`w.link (3*C)`, independently of the tongue state and of which branch was
entered.  A repeated productive visit cannot choose a different successor
at the stem.  It must be delivered to the opposite branch by traffic through
other switches.

At echo level, a productive-free interval has only three possible effects
when it is used as the bottom of a restoration descent:

* it creates a strict earlier replay of the complete machine state;
* it reaches a live slot fixed by the external-edge involution; or
* it contains another productive write and therefore another, strictly
  shorter, first-restoration frame.

The second alternative is exactly a self-linked raw track port in the
canonical compiler.  It is excluded by the physical irreflexivity condition
`w.link p = some q -> p ≠ q`.  Well-founded descent on restoration span
then rules out an endpoint-empty cyclic-minimal `ABCABC` pattern unless an
earlier full-state replay or an exact lobe endpoint already exists.
-/

namespace GeneralN

/-- Physical external track edges never connect a port to itself.  The base
`Wiring` structure deliberately records only symmetry, so this real-track
condition is kept explicit. -/
def IrreflexiveLinks (w : Wiring) : Prop :=
  forall p q, w.link p = some q -> p ≠ q

namespace TripleInterlacement

/-! ## Koizumi's curve matching, locally and directly over `Wiring`

For a fixed tongue vector, the plain-track matching is augmented by exactly
one internal edge at every switch: stem to selected branch.  The unselected
branch is the endpoint.  The definitions below deliberately retain the two
edge colours.  A physical external edge can otherwise happen to have the
same pair of endpoints as an internal edge in the deliberately permissive
raw `Wiring` model.
-/

/-- The selected internal stem--branch edge of one switch, as an undirected
edge. -/
def SwitchCurveEdge (u : Tongues) (C p q : Nat) : Prop :=
  (p = 3*C ∧ q = selectedBranch u C) ∨
  (q = 3*C ∧ p = selectedBranch u C)

/-- Any selected internal edge in the current tongue state. -/
def InternalCurveEdge (u : Tongues) (p q : Nat) : Prop :=
  ∃ C, SwitchCurveEdge u C p q

/-- The state-dependent undirected curve graph: fixed external matching
edges together with the currently selected internal edges. -/
def CurveEdge (w : Wiring) (u : Tongues) (p q : Nat) : Prop :=
  w.link p = some q ∨ InternalCurveEdge u p q

/-- The internal edge removed when switch `C` pivots. -/
def RemovedPivotEdge (u : Tongues) (C p q : Nat) : Prop :=
  SwitchCurveEdge u C p q

/-- The internal edge inserted when switch `C` pivots. -/
def InsertedPivotEdge (u : Tongues) (C p q : Nat) : Prop :=
  (p = 3*C ∧ q = unmatchedBranch u C) ∨
  (q = 3*C ∧ p = unmatchedBranch u C)

theorem switchCurveEdge_symm {u : Tongues} {C p q : Nat}
    (h : SwitchCurveEdge u C p q) :
    SwitchCurveEdge u C q p := by
  rcases h with h | h
  · exact Or.inr ⟨h.1, h.2⟩
  · exact Or.inl ⟨h.1, h.2⟩

theorem internalCurveEdge_symm {u : Tongues} {p q : Nat}
    (h : InternalCurveEdge u p q) :
    InternalCurveEdge u q p := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, switchCurveEdge_symm hC⟩

theorem curveEdge_symm {w : Wiring} {u : Tongues} {p q : Nat}
    (h : CurveEdge w u p q) : CurveEdge w u q p := by
  rcases h with h | h
  · exact Or.inl (w.symm _ _ h)
  · exact Or.inr (internalCurveEdge_symm h)

/-- Both endpoints of an internal edge belong to its declared switch. -/
theorem switchCurveEdge_switches {u : Tongues} {C p q : Nat}
    (h : SwitchCurveEdge u C p q) : p / 3 = C ∧ q / 3 = C := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by omega, selectedBranch_switch u C⟩
  · exact ⟨selectedBranch_switch u C, by omega⟩

/-- The switch label of an internal edge is unique. -/
theorem switchCurveEdge_switch_unique
    {u : Tongues} {C D p q : Nat}
    (hC : SwitchCurveEdge u C p q)
    (hD : SwitchCurveEdge u D p q) : C = D := by
  have hc := (switchCurveEdge_switches hC).1
  have hd := (switchCurveEdge_switches hD).1
  omega

theorem selectedBranch_flip_other
    (u : Tongues) {C D : Nat} (hDC : D ≠ C) :
    selectedBranch (flipAt u C) D = selectedBranch u D := by
  simp [selectedBranch, flipAt, hDC]

theorem unmatched_after_flip_eq_selected (u : Tongues) (C : Nat) :
    unmatchedBranch (flipAt u C) C = selectedBranch u C := by
  cases h : u C <;>
    simp [unmatchedBranch, selectedBranch, branchPort, flipAt, h]

/-- At the pivoting switch the new selected edge is exactly the old endpoint
edge. -/
theorem switchCurveEdge_flip_same_iff
    (u : Tongues) (C p q : Nat) :
    SwitchCurveEdge (flipAt u C) C p q ↔
      InsertedPivotEdge u C p q := by
  unfold SwitchCurveEdge InsertedPivotEdge
  rw [selected_after_flip_eq_unmatched]

/-- Internal edges at all other switches are literally unchanged. -/
theorem switchCurveEdge_flip_other_iff
    (u : Tongues) {C D p q : Nat} (hDC : D ≠ C) :
    SwitchCurveEdge (flipAt u C) D p q ↔
      SwitchCurveEdge u D p q := by
  unfold SwitchCurveEdge
  rw [selectedBranch_flip_other u hDC]

/-- Exact internal matching surgery: replace precisely the old selected edge
at `C` by the old endpoint edge. -/
theorem internalCurveEdge_flip_iff
    (u : Tongues) (C p q : Nat) :
    InternalCurveEdge (flipAt u C) p q ↔
      InsertedPivotEdge u C p q ∨
      (InternalCurveEdge u p q ∧ ¬ RemovedPivotEdge u C p q) := by
  constructor
  · rintro ⟨D, hD⟩
    by_cases hDC : D = C
    · subst D
      exact Or.inl ((switchCurveEdge_flip_same_iff u C p q).mp hD)
    · right
      have hOld : SwitchCurveEdge u D p q :=
        (switchCurveEdge_flip_other_iff u hDC).mp hD
      refine ⟨⟨D, hOld⟩, ?_⟩
      intro hC
      exact hDC (switchCurveEdge_switch_unique hOld hC)
  · intro h
    rcases h with hnew | ⟨⟨D, hD⟩, hnotC⟩
    · exact ⟨C, (switchCurveEdge_flip_same_iff u C p q).mpr hnew⟩
    · have hDC : D ≠ C := by
        intro hEq
        subst D
        exact hnotC hD
      exact ⟨D, (switchCurveEdge_flip_other_iff u hDC).mpr hD⟩

/-- Exact two-colour curve-graph surgery.  External edges are untouched;
among internal edges one old edge is removed and one endpoint edge inserted. -/
theorem curveEdge_flip_iff
    (w : Wiring) (u : Tongues) (C p q : Nat) :
    CurveEdge w (flipAt u C) p q ↔
      w.link p = some q ∨
      InsertedPivotEdge u C p q ∨
      (InternalCurveEdge u p q ∧ ¬ RemovedPivotEdge u C p q) := by
  unfold CurveEdge
  rw [internalCurveEdge_flip_iff]

/-- A finite arc in the curve graph.  Repetition-freeness is kept separate:
it is the property which turns an arc into an honest subarc of a curve. -/
inductive CurveSegment (w : Wiring) (u : Tongues) : List Nat → Prop
  | nil : CurveSegment w u []
  | singleton (p : Nat) : CurveSegment w u [p]
  | cons {p q : Nat} {rest : List Nat}
      (edge : CurveEdge w u p q)
      (tail : CurveSegment w u (q :: rest)) :
      CurveSegment w u (p :: q :: rest)

/-- No consecutive edge of the segment is the selected edge about to be
removed at switch `C`. -/
def AvoidsRemovedPivot (u : Tongues) (C : Nat) : List Nat → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest =>
      ¬ RemovedPivotEdge u C p q ∧
      AvoidsRemovedPivot u C (q :: rest)

/-- If the stem of `C` is absent from an arc, that arc cannot contain the
selected internal edge of `C`. -/
theorem avoidsRemovedPivot_of_stem_not_mem
    (u : Tongues) (C : Nat) :
    ∀ xs : List Nat, 3*C ∉ xs → AvoidsRemovedPivot u C xs := by
  intro xs
  induction xs with
  | nil => intro _; trivial
  | cons p rest ih =>
      cases rest with
      | nil => intro _; trivial
      | cons q tail =>
          intro hstem
          have hp : p ≠ 3*C := by
            intro h
            apply hstem
            simp [h]
          have htail : 3*C ∉ q :: tail := by
            intro h
            exact hstem (List.mem_cons_of_mem _ h)
          constructor
          · intro hedge
            rcases hedge with ⟨h, _⟩ | ⟨h, _⟩
            · exact hp h
            · exact htail (by simp [h])
          · exact ih htail

/-- Every old curve edge other than the removed selected edge survives the
pivot. -/
theorem curveEdge_survives_flip
    {w : Wiring} {u : Tongues} {C p q : Nat}
    (hedge : CurveEdge w u p q)
    (havoid : ¬ RemovedPivotEdge u C p q) :
    CurveEdge w (flipAt u C) p q := by
  rw [curveEdge_flip_iff]
  rcases hedge with hext | hint
  · exact Or.inl hext
  · exact Or.inr (Or.inr ⟨hint, havoid⟩)

/-- An arc avoiding the removed edge remains an arc after the pivot. -/
theorem curveSegment_survives_flip
    {w : Wiring} {u : Tongues} {C : Nat} :
    ∀ {xs : List Nat}, CurveSegment w u xs →
      AvoidsRemovedPivot u C xs →
      CurveSegment w (flipAt u C) xs := by
  intro xs hsegment
  induction hsegment with
  | nil => intro _; exact CurveSegment.nil
  | singleton p => intro _; exact CurveSegment.singleton p
  | @cons p q rest hedge htail ih =>
      intro havoid
      exact CurveSegment.cons
        (curveEdge_survives_flip hedge havoid.1)
        (ih havoid.2)

/-- **Koizumi local component surgery.**

Orient a simple train-free curve so that the switch being entered contributes
the consecutive old selected edge `stem -- selected`.  A productive pivot
inserts `old-unmatched -- stem`; the old selected branch becomes the new
endpoint, and the opposite side is a strict, still-valid subarc.  This is the
raw matching-language version of the shrinking-curve move. -/
theorem pivot_releases_strict_subcurve
    {w : Wiring} {u : Tongues} {C : Nat} {rest : List Nat}
    (hcurve : CurveSegment w u
      (3*C :: selectedBranch u C :: rest))
    (hsimple : (3*C :: selectedBranch u C :: rest).Nodup) :
    CurveEdge w (flipAt u C) (unmatchedBranch u C) (3*C) ∧
    unmatchedBranch (flipAt u C) C = selectedBranch u C ∧
    CurveSegment w (flipAt u C)
      (unmatchedBranch (flipAt u C) C :: rest) ∧
    (unmatchedBranch (flipAt u C) C :: rest).length <
      (3*C :: selectedBranch u C :: rest).length := by
  have htail : CurveSegment w u (selectedBranch u C :: rest) := by
    cases hcurve with
    | cons _ tail => exact tail
  have hstem : 3*C ∉ selectedBranch u C :: rest :=
    (List.nodup_cons.mp hsimple).1
  have havoid : AvoidsRemovedPivot u C
      (selectedBranch u C :: rest) :=
    avoidsRemovedPivot_of_stem_not_mem u C _ hstem
  have hsurvives : CurveSegment w (flipAt u C)
      (selectedBranch u C :: rest) :=
    curveSegment_survives_flip htail havoid
  have hjoin : CurveEdge w (flipAt u C)
      (unmatchedBranch u C) (3*C) := by
    rw [curveEdge_flip_iff]
    exact Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))
  refine ⟨hjoin, unmatched_after_flip_eq_selected u C, ?_, ?_⟩
  · simpa [unmatched_after_flip_eq_selected u C] using hsurvives
  · simp

theorem pivot_residual_keeps_endpoint_name (u : Tongues) (C : Nat) :
    selectedBranch u C = unmatchedBranch (flipAt u C) C := by
  exact (unmatched_after_flip_eq_selected u C).symm

end TripleInterlacement


theorem canonical_live_bar_ne
    {w : Wiring} {p : Nat}
    (hirr : IrreflexiveLinks w)
    (hp : IsCanonicalEchoSlot w p) :
    (canonicalEchoMachine w).bar (encodeSlot p) ≠ encodeSlot p := by
  rw [canonicalEchoMachine_bar]
  intro hEq
  have hwire : wireBar w p = p := encodeSlot_injective hEq
  have hlink : w.link p = some p := by
    simpa [hwire] using hp.2.2.1
  exact hirr p p hlink rfl

end GeneralN

namespace Echo

variable (m : Machine) (e : Nat -> Nat) (r0 : Nat -> Nat)

/-- Equality of the actual complete echo state: current entry and every
register, not merely a projection to a chosen finite cell list. -/
def CompleteStateEq (i j : Nat) : Prop :=
  e i = e j /\
  forall c, reg m e r0 i c = reg m e r0 j c

/-- A replay strictly shorter than the declared recurrent period. -/
def EarlierCompleteStateReplay (K p : Nat) : Prop :=
  exists i q,
    K <= i /\ 0 < q /\ q < p /\
    CompleteStateEq m e r0 i (i + q)

/-- Equality of every finite state code yields equality of the actual
complete state. -/
theorem completeStateEq_of_all_stateCodes
    {i j : Nat}
    (h : forall cells : List Nat,
      stateCode m e r0 cells i = stateCode m e r0 cells j) :
    CompleteStateEq m e r0 i j := by
  constructor
  · exact stateCode_entry_eq m e r0 [] (h [])
  · intro c
    exact stateCode_reg_eq m e r0 [c] (h [c]) c (by simp)

/-- A productive-free return to the same cell is already a replay of the
entire state, not only of a finite projection. -/
theorem quiet_return_complete_state
    {i q : Nat}
    (hquiet : forall t, i <= t -> t < i + q ->
      Not (ProductiveStep m e r0 t))
    (hcell : m.cellOf (e (i + q)) = m.cellOf (e i)) :
    CompleteStateEq m e r0 i (i + q) := by
  apply completeStateEq_of_all_stateCodes m e r0
  intro cells
  exact quiet_return_same_cell_state m e r0 cells hquiet hcell

/-- If the replay corridor between consecutive same-cell deliveries avoids
both that cell and its mouth, the corridor after the second delivery closes
a complete-state loop. -/
theorem consecutive_avoid_complete_replay
    (hrun : IsRun m e r0)
    {C t1 t2 : Nat} (h12 : t1 < t2)
    (hq : forall s, t1 < s -> s < t2 ->
      Not (ProductiveStep m e r0 s))
    (hc1 : m.cellOf (e (t1 + 1)) = C)
    (hc2 : m.cellOf (e (t2 + 1)) = C)
    (havoid : forall l, 1 <= l -> l <= t2 - t1 - 1 ->
      m.cellOf (e (t1 + 1 + l)) ≠ C /\
      m.cellOf (e (t1 + 1 + l)) ≠ m.star C) :
    CompleteStateEq m e r0 (t2 + 1)
      (t2 + 1 + (t2 - t1)) := by
  apply completeStateEq_of_all_stateCodes m e r0
  intro cells
  exact (consecutive_avoid_loop m e r0 hrun cells
    h12 hq hc1 hc2 havoid).1

/-- Before invoking periodicity, the same-writer corridor has an exact
dynamical dichotomy: it either closes a complete state loop, or it physically
visits the written cell or its mouth partner. -/
theorem consecutive_same_write_replay_or_visit
    (hrun : IsRun m e r0)
    {C t1 t2 : Nat} (h12 : t1 < t2)
    (hq : forall s, t1 < s -> s < t2 ->
      Not (ProductiveStep m e r0 s))
    (hc1 : m.cellOf (e (t1 + 1)) = C)
    (hc2 : m.cellOf (e (t2 + 1)) = C) :
    CompleteStateEq m e r0 (t2 + 1)
        (t2 + 1 + (t2 - t1)) \/
    exists l, 1 <= l /\ l <= t2 - t1 - 1 /\
      (m.cellOf (e (t1 + 1 + l)) = C \/
       m.cellOf (e (t1 + 1 + l)) = m.star C) := by
  by_cases hex : exists l, 1 <= l /\ l <= t2 - t1 - 1 /\
      (m.cellOf (e (t1 + 1 + l)) = C \/
       m.cellOf (e (t1 + 1 + l)) = m.star C)
  · exact Or.inr hex
  · left
    apply consecutive_avoid_complete_replay m e r0 hrun h12 hq hc1 hc2
    intro l h1 h2
    constructor
    · intro h
      exact hex ⟨l, h1, h2, Or.inl h⟩
    · intro h
      exact hex ⟨l, h1, h2, Or.inr h⟩

/-- A quiet route from a cell to its mouth partner forces a live
`bar`-fixed entry.  This is the exact total-machine degeneracy hidden by a
global fixed-point-free premise; the canonical raw compiler identifies it
with a self-linked physical port. -/
theorem quiet_mouth_forces_fixed_entry
    (hrun : IsRun m e r0)
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {i p : Nat}
    (hquiet : forall t, i <= t -> t < i + p ->
      Not (ProductiveStep m e r0 t))
    (hmouth : m.cellOf (e (i + p)) =
      m.star (m.cellOf (e i))) :
    exists q, i < q /\ q <= i + p /\ m.bar (e q) = e q := by
  have hpair : forall j, j <= p ->
      m.cellOf (e (i + (p - j))) =
        m.star (m.cellOf (e (i + j))) := by
    intro j
    induction j with
    | zero =>
        intro _
        exact hmouth
    | succ n ih =>
        intro hn1
        have IH := ih (by omega)
        have ht : i + (p - n) = (i + (p - (n+1))) + 1 := by omega
        have hq1 : Not (ProductiveStep m e r0
            (i + (p - (n+1)))) :=
          hquiet _ (Nat.le_add_right _ _) (by omega)
        have hun : e ((i + (p - (n+1))) + 1) =
            reg m e r0 (i + (p - (n+1)))
              (m.cellOf (e ((i + (p - (n+1))) + 1))) := by
          by_cases hq2 : e ((i + (p - (n+1))) + 1) =
              reg m e r0 (i + (p - (n+1)))
                (m.cellOf (e ((i + (p - (n+1))) + 1)))
          · exact hq2
          · exact absurd hq2 hq1
        rw [← ht] at hun
        have hreg1 : forall c,
            reg m e r0 (i + (p - (n+1))) c =
              reg m e r0 i c :=
          quiet_reg m e r0 (p - (n+1))
            (fun t h1 h2 => hquiet t h1 (by omega))
        have hreg2 : forall c,
            reg m e r0 (i + n) c = reg m e r0 i c :=
          quiet_reg m e r0 n
            (fun t h1 h2 => hquiet t h1 (by omega))
        have hval : e (i + (p - n)) =
            reg m e r0 i
              (m.star (m.cellOf (e (i + n)))) := by
          rw [hun, hreg1, IH]
        have hfwd : e (i + n + 1) =
            m.bar (reg m e r0 i
              (m.star (m.cellOf (e (i + n))))) := by
          rw [hrun (i + n), hreg2]
        have hpal : m.bar (e (i + (p - n))) =
            e (i + n + 1) := by
          rw [hval, hfwd]
        have hw :=
          (witness m e r0 hrun hr0 (i + (p - (n+1)))).1
        rw [← ht] at hw
        rw [hpal] at hw
        have hst := congrArg m.star hw
        rw [m.star_invol] at hst
        exact hst.symm
  have hsplit : p = 2 * (p / 2) \/
      p = 2 * (p / 2) + 1 := by omega
  rcases hsplit with heven | hodd
  · have h := hpair (p / 2) (by omega)
    have hsub : p - p / 2 = p / 2 := by omega
    rw [hsub] at h
    exact (m.star_ne _ h.symm).elim
  · have h := hpair (p / 2) (by omega)
    have hsub : p - p / 2 = p / 2 + 1 := by omega
    rw [hsub] at h
    have hq1 : Not (ProductiveStep m e r0 (i + p / 2)) :=
      hquiet _ (Nat.le_add_right _ _) (by omega)
    have hun : e (i + p / 2 + 1) =
        reg m e r0 (i + p / 2)
          (m.cellOf (e (i + p / 2 + 1))) := by
      by_cases hq2 : e (i + p / 2 + 1) =
          reg m e r0 (i + p / 2)
            (m.cellOf (e (i + p / 2 + 1)))
      · exact hq2
      · exact absurd hq2 hq1
    have hcell : m.cellOf (e (i + p / 2 + 1)) =
        m.star (m.cellOf (e (i + p / 2))) := h
    rw [hcell] at hun
    have hstep := hrun (i + p / 2)
    rw [hun] at hstep
    refine ⟨i + p / 2 + 1, ?_⟩
    exact (by
      constructor
      · omega
      constructor
      · omega
      · rw [hun]
        exact hstep.symm)

/-- Base obstruction for two consecutive productive writes of one cell.
Within a declared period it produces either a strictly shorter complete-state
replay or a live fixed jump slot. -/
theorem consecutive_same_writer_earlier_replay_or_fixed
    (hrun : IsRun m e r0)
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p C t1 t2 : Nat}
    (hK : K <= t1)
    (h12 : t1 < t2)
    (ht2period : t2 < t1 + p)
    (hquiet : forall s, t1 < s -> s < t2 ->
      Not (ProductiveStep m e r0 s))
    (hc1 : m.cellOf (e (t1 + 1)) = C)
    (hc2 : m.cellOf (e (t2 + 1)) = C) :
    EarlierCompleteStateReplay m e r0 K p \/
    exists q, m.bar (e q) = e q := by
  rcases consecutive_same_write_replay_or_visit
      m e r0 hrun h12 hquiet hc1 hc2 with hloop | hvisit
  · left
    refine ⟨t2 + 1, t2 - t1, ?_⟩
    exact (by
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · exact hloop)
  · obtain ⟨l, hl1, hl2, hcell | hmouth⟩ := hvisit
    · left
      let start := t1 + 1
      have hsegment : forall t, start <= t -> t < start + l ->
          Not (ProductiveStep m e r0 t) := by
        intro t hlow hhigh
        exact hquiet t (by dsimp [start] at hlow; omega)
          (by dsimp [start] at hhigh; omega)
      have hreturn :
          m.cellOf (e (start + l)) = m.cellOf (e start) := by
        dsimp [start]
        rw [hc1]
        exact hcell
      refine ⟨start, l, ?_⟩
      exact (by
        constructor
        · dsimp [start]
          omega
        constructor
        · omega
        constructor
        · omega
        · exact quiet_return_complete_state
            m e r0 hsegment hreturn)
    · right
      let start := t1 + 1
      have hsegment : forall t, start <= t -> t < start + l ->
          Not (ProductiveStep m e r0 t) := by
        intro t hlow hhigh
        exact hquiet t (by dsimp [start] at hlow; omega)
          (by dsimp [start] at hhigh; omega)
      have hmouth' :
          m.cellOf (e (start + l)) =
            m.star (m.cellOf (e start)) := by
        dsimp [start]
        rw [hc1]
        exact hmouth
      obtain ⟨q, _hlo, _hhi, hfix⟩ :=
        quiet_mouth_forces_fixed_entry
          m e r0 hrun hr0 hsegment hmouth'
      exact ⟨q, hfix⟩

/-- Two distinct first-restoration frames cannot close at the same event
when the second opens strictly inside the first. -/
theorem nested_foreign_frames_shared_close_impossible
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {b d r : Nat}
    (houter : FirstRestorationFrame m e r0 b r)
    (hinner : FirstRestorationFrame m e r0 d r)
    (hbd : b < d) : False := by
  have hwriter : writerAt m e d = writerAt m e b :=
    hinner.1.2.2.2.1.symm.trans houter.1.2.2.2.1
  have hold : oldSlot m e r0 d = oldSlot m e r0 b :=
    hinner.1.2.2.2.2.symm.trans houter.1.2.2.2.2
  by_cases hnext : d = b + 1
  · have hreg : reg m e r0 d (writerAt m e b) = e (b+1) := by
      rw [hnext]
      exact reg_write m e r0 rfl
    have holdAtD :
        reg m e r0 d (writerAt m e b) = oldSlot m e r0 b := by
      calc
        reg m e r0 d (writerAt m e b) =
            reg m e r0 d (writerAt m e d) := by rw [hwriter]
        _ = oldSlot m e r0 d := rfl
        _ = oldSlot m e r0 b := hold
    apply houter.1.1
    simpa [oldSlot, writerAt] using hreg.symm.trans holdAtD
  · exact first_restoration_forbids_early_returned_register
      m e r0 hr0 houter (by omega) hinner.1.2.1 hwriter hold

/-- A strictly nested foreign frame in a cyclic-overlap-minimal crossing
forces an exact lobe, an earlier complete-state replay, or a live fixed jump
slot.  The proof descends on the physical restoration span. -/
theorem cyclic_minimal_nested_foreign_obstruction
    (hrun : IsRun m e r0)
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p t0 u0 t1 u1 b r : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hKb : K <= b)
    (ht1b : t1 < b)
    (hbr : b < r)
    (hrperiod : r < b + p)
    (hru0 : r < u0)
    (hframe : ForeignRestorationFrame m e r0 b r) :
    (exists k, ExactLobeWrite m e r0 k) \/
    EarlierCompleteStateReplay m e r0 K p \/
    (exists q, m.bar (e q) = e q) := by
  by_cases hinter : exists d, b < d /\ d < r /\
      ProductiveStep m e r0 d
  · obtain ⟨d, hbd, hdr, hprodD⟩ := hinter
    have hKd : K <= d := by omega
    obtain ⟨s, hds, hsperiod, hfirstD⟩ :=
      productive_has_first_restoration_before_period
        m e r0 hr0 hper.positive hKd hper.register hprodD
    by_cases hopen : SameEdgeWrite m e r0 d
    · exact Or.inl ⟨d, productive_sameEdgeWrite_exact_lobe
        m e r0 hr0 hprodD hopen⟩
    · by_cases hclose : SameEdgeWrite m e r0 s
      · exact Or.inl ⟨s, productive_sameEdgeWrite_exact_lobe
          m e r0 hr0 hfirstD.1.2.2.1 hclose⟩
      · have hforeignD : ForeignRestorationFrame m e r0 d s :=
          ⟨hfirstD, hopen, hclose⟩
        by_cases hsr : s < r
        · exact cyclic_minimal_nested_foreign_obstruction
            hrun hr0 hper hmin hKd (by omega)
            hds hsperiod (by omega) hforeignD
        · by_cases hEq : s = r
          · subst s
            exact (nested_foreign_frames_shared_close_impossible
              m e r0 hr0 hframe.1 hfirstD hbd).elim
          · have hrs : r < s := by omega
            have hcross : ForeignRestorationCrossing
                m e r0 b r d s :=
              ⟨hframe, hforeignD, ⟨hbd, hdr, hrs⟩⟩
            have hlift : PeriodLiftedForeignRestorationCrossing
                m e r0 p b r d s :=
              ⟨hcross, hrperiod, hsperiod⟩
            obtain ⟨a0, z0, a1, z1, hnorm, hover⟩ :=
              periodLifted_crossing_has_normalized_lift
                m e r0 hper hKb hlift
            have hstrict :
                crossingOverlap a0 z0 a1 z1 <
                  crossingOverlap t0 u0 t1 u1 := by
              rw [hover]
              unfold crossingOverlap
              omega
            exact (hmin.2 a0 z0 a1 z1 hnorm hstrict).elim
  · have hquiet : forall s, b < s -> s < r ->
        Not (ProductiveStep m e r0 s) := by
      intro s hbs hsr hprod
      exact hinter ⟨s, hbs, hsr, hprod⟩
    have hc2 : m.cellOf (e (r + 1)) =
        m.cellOf (e (b + 1)) := by
      exact hframe.1.1.2.2.2.1
    rcases consecutive_same_writer_earlier_replay_or_fixed
        m e r0 hrun hr0 hKb hbr hrperiod hquiet rfl hc2 with
      hreplay | hfixed
    · exact Or.inr (Or.inl hreplay)
    · exact Or.inr (Or.inr hfixed)
termination_by r - b
decreasing_by omega

/-- The cyclic triple-interlacement obstruction at the abstract run level.
A stable failed-retrace blocker in the overlap cannot generate an
endpoint-empty `ABCABC` descent: it yields a lobe, an earlier full-state
replay, or a live fixed jump slot. -/
theorem cyclic_minimal_stable_blocker_obstruction
    (hrun : IsRun m e r0)
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p t0 u0 t1 u1 b j : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hKb : K <= b)
    (ht1b : t1 < b)
    (hbu0 : b < u0)
    (hstable : StableBlockerUntil m e r0 b j) :
    (exists k, ExactLobeWrite m e r0 k) \/
    EarlierCompleteStateReplay m e r0 K p \/
    (exists q, m.bar (e q) = e q) := by
  obtain ⟨r, hbr, hrperiod, hfirst, _hjr, hout⟩ :=
    cyclic_minimal_stable_blocker_order
      m e r0 hr0 hper hmin hKb ht1b hbu0 hstable
  by_cases hopen : SameEdgeWrite m e r0 b
  · exact Or.inl ⟨b, productive_sameEdgeWrite_exact_lobe
      m e r0 hr0 hstable.productive hopen⟩
  · by_cases hclose : SameEdgeWrite m e r0 r
    · exact Or.inl ⟨r, productive_sameEdgeWrite_exact_lobe
        m e r0 hr0 hfirst.1.2.2.1 hclose⟩
    · have hforeign : ForeignRestorationFrame m e r0 b r :=
        ⟨hfirst, hopen, hclose⟩
      have hru0 : r <= u0 := by
        rcases hout with h | h | h
        · exact (hopen h).elim
        · exact (hclose h).elim
        · exact h
      have hrlt : r < u0 := by
        by_cases hre : r = u0
        · have houter : FirstRestorationFrame m e r0 t0 u0 :=
            hmin.1.1.1.1.1
          have ht0b : t0 < b := by
            have ht0t1 : t0 < t1 := hmin.1.1.1.2.2.1
            exact Nat.lt_trans ht0t1 ht1b
          subst r
          exact (nested_foreign_frames_shared_close_impossible
            m e r0 hr0 houter hfirst ht0b).elim
        · omega
      exact cyclic_minimal_nested_foreign_obstruction
        m e r0 hrun hr0 hper hmin hKb ht1b hbr
          hrperiod hrlt hforeign

/-- **Physical theorem.**  For a certified run of a symmetric cubic
lazy-switch wiring with no self-linked external port, the fixed-jump branch
of the abstract obstruction is impossible.  Thus a cyclic-minimal
endpoint-empty triple interlacement forces either an exact lobe endpoint or
a strict earlier replay of the complete state. -/
theorem physical_cyclic_minimal_stable_blocker_lobe_or_replay
    {w : GeneralN.Wiring}
    (hirr : GeneralN.IrreflexiveLinks w)
    (run : GeneralN.CertifiedConcreteEchoRun w)
    {K p t0 u0 t1 u1 b j : Nat}
    (hper : RestorationPeriodicTail
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister K p)
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister K p t0 u0 t1 u1)
    (hKb : K <= b)
    (ht1b : t1 < b)
    (hbu0 : b < u0)
    (hstable : StableBlockerUntil
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister b j) :
    (exists k, ExactLobeWrite
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister k) \/
    EarlierCompleteStateReplay
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister K p := by
  have hout := cyclic_minimal_stable_blocker_obstruction
    (GeneralN.canonicalEchoMachine w)
    (GeneralN.encodedEntries run.entry)
    run.initialRegister
    (GeneralN.certifiedConcreteEcho_isRun run)
    run.initialWellFormed
    hper hmin hKb ht1b hbu0 hstable
  rcases hout with hlobe | hreplay | hfixed
  · exact Or.inl hlobe
  · exact Or.inr hreplay
  · obtain ⟨q, hfix⟩ := hfixed
    have hne := GeneralN.canonical_live_bar_ne
      hirr (run.toConcreteAscentTrace.freeSlot q)
    apply (hne ?_).elim
    simpa [GeneralN.encodedEntries] using hfix

/-- Direct impossibility form matching the endpoint-empty `ABCABC`
question.  Under the physical wiring axioms, cyclic minimality plus absence
of both allowed escape hatches is contradictory. -/
theorem physical_endpoint_empty_abcabc_impossible
    {w : GeneralN.Wiring}
    (hirr : GeneralN.IrreflexiveLinks w)
    (run : GeneralN.CertifiedConcreteEchoRun w)
    {K p t0 u0 t1 u1 b j : Nat}
    (hper : RestorationPeriodicTail
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister K p)
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister K p t0 u0 t1 u1)
    (hKb : K <= b)
    (ht1b : t1 < b)
    (hbu0 : b < u0)
    (hstable : StableBlockerUntil
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister b j)
    (hnoLobe : forall k, Not (ExactLobeWrite
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister k))
    (hnoReplay : Not (EarlierCompleteStateReplay
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister K p)) :
    False := by
  rcases physical_cyclic_minimal_stable_blocker_lobe_or_replay
      hirr run hper hmin hKb ht1b hbu0 hstable with
    hlobe | hreplay
  · obtain ⟨k, hk⟩ := hlobe
    exact hnoLobe k hk
  · exact hnoReplay hreplay

end Echo
