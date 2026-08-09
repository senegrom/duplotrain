import ManufacturedPairTailNovelty
import SixEventSharpClosure

/-!
# An early serial pair must make a concrete support contact

Two oppositely oriented manufactured reflectors give the four Gray corners
as soon as both local actions avoid the other reflector's support. In a raw
six-event counterexample, reaching such a compatible pair before the second
selected close is therefore impossible.

This file removes the negated compatibility predicates from that residual.
If an early pair exists, at least one reflector is a genuine flip reflector
and its action switch occurs on a concrete passage in the opposite support.
That passage is the physical contact which the remaining serial/serial
argument must identify with one of the six canonical events.

The result is general in N and uses only raw Wiring/stepN data. It is not yet
the final four-cover theorem.
-/

namespace GeneralN

/-- Failure of local-action avoidance names both the flipped switch and a
concrete passage of the support which uses it. -/
theorem LocalAction.not_avoids_support_witness
    {action : LocalAction} {paths : List (List Passage)}
    (h : Not (action.Avoids paths)) :
    Exists fun k =>
      Exists fun path =>
        Exists fun passage =>
          And (action = .flip k)
            (And (List.Mem path paths)
              (And (List.Mem passage path)
                (passageSwitch passage = k))) := by
  cases action with
  | stay =>
      exact (h True.intro).elim
  | flip k =>
      have hex :
          Exists fun path =>
            Exists fun passage =>
              And (List.Mem path paths)
                (And (List.Mem passage path)
                  (passageSwitch passage = k)) := by
        apply Classical.byContradiction
        intro hnone
        apply h
        intro path hpath passage hpassage hswitch
        apply hnone
        exact Exists.intro path
          (Exists.intro passage
            (And.intro hpath (And.intro hpassage hswitch)))
      cases hex with
      | intro path hexPassage =>
        cases hexPassage with
        | intro passage hdata =>
          exact Exists.intro k
            (Exists.intro path
              (Exists.intro passage (And.intro rfl hdata)))

/-- A compatible opposite pair reached by the second canonical close gives
the literal forbidden four-cover of all five selected tail closes. -/
private theorem RawSixEventReduction.compatible_pair_before_second_false
    {w : Wiring} {N g e K : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    (R : RawSixEventReduction w N start)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    (hreach : stepN w K start = some (g, state))
    (hK : Nat.le K (R.z1 + 1)) : False := by
  let times :=
    [R.z1 + 1, R.z2 + 1, R.z3 + 1, R.z4 + 1, R.z5 + 1]
  let history :=
    rawFirstWriterHistory w N start (R.z5 + 1) ++
      [restrictedTonguesAt w N start (R.z0 + 1)]
  have o12 : R.z1 < R.z2 := R.order12
  have o23 : R.z2 < R.z3 := R.order23
  have o34 : R.z3 < R.z4 := R.order34
  have o45 : R.z4 < R.z5 := R.order45
  have l12 : Nat.le (R.z1 + 1) (R.z2 + 1) :=
    Nat.add_le_add_right (Nat.le_of_lt o12) 1
  have l23 : Nat.le (R.z2 + 1) (R.z3 + 1) :=
    Nat.add_le_add_right (Nat.le_of_lt o23) 1
  have l34 : Nat.le (R.z3 + 1) (R.z4 + 1) :=
    Nat.add_le_add_right (Nat.le_of_lt o34) 1
  have l45 : Nat.le (R.z4 + 1) (R.z5 + 1) :=
    Nat.add_le_add_right (Nat.le_of_lt o45) 1
  have htimes : forall j, Membership.mem times j -> Nat.le K j := by
    intro j hj
    dsimp [times] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    case inl => exact hK
    case inr.inl =>
      exact Nat.le_trans hK l12
    case inr.inr.inl =>
      exact Nat.le_trans (Nat.le_trans hK l12) l23
    case inr.inr.inr.inl =>
      exact Nat.le_trans
        (Nat.le_trans (Nat.le_trans hK l12) l23) l34
    case inr.inr.inr.inr =>
      exact Nat.le_trans
        (Nat.le_trans (Nat.le_trans (Nat.le_trans hK l12) l23) l34) l45
  have hcover : FourNoveltyCover w N start times history :=
    manufactured_pair_absolute_four_novelty_cover
      A B state hA hB hAB hBA hreach times history htimes
  exact R.no_tail_four_cover hN (by
    simpa [FourNoveltyCover, times, history] using hcover)

/-- **Concrete residual of the early two-reflector branch.**

In a raw six-event obstruction, an opposite pair reached by z1 + 1 cannot
be mutually support-compatible. Instead one of the two local actions is a
flip at a switch occurring on a named passage of the opposite reflector's
support.

Unlike a conditional compatibility certificate, the conclusion is an
unconditional physical witness extracted from the alleged counterexample.
-/
theorem RawSixEventReduction.early_pair_action_support_contact
    {w : Wiring} {N g e K : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    (R : RawSixEventReduction w N start)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hreach : stepN w K start = some (g, state))
    (hK : Nat.le K (R.z1 + 1)) :
    Or
      (Exists fun k =>
        Exists fun path =>
          Exists fun passage =>
            And (A.toSupported.action = .flip k)
              (And (List.Mem path B.toSupported.paths)
                (And (List.Mem passage path)
                  (passageSwitch passage = k))))
      (Exists fun k =>
        Exists fun path =>
          Exists fun passage =>
            And (B.toSupported.action = .flip k)
              (And (List.Mem path A.toSupported.paths)
                (And (List.Mem passage path)
                  (passageSwitch passage = k)))) := by
  classical
  by_cases hAB :
      A.toSupported.action.Avoids B.toSupported.paths
  case pos =>
    cases Classical.em
        (B.toSupported.action.Avoids A.toSupported.paths) with
    | inl hBA =>
        exact (R.compatible_pair_before_second_false
          hN A B state hA hB hAB hBA hreach hK).elim
    | inr hBA =>
        exact Or.inr
          (LocalAction.not_avoids_support_witness hBA)
  case neg =>
    exact Or.inl
      (LocalAction.not_avoids_support_witness hAB)

end GeneralN
