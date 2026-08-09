import ManufacturedPairTailNovelty
import SixEventSharpClosure

/-!
# Mellit's first-repeat / second-repeat route to the sharp tail

This file develops a closure route which is deliberately independent of the
interval/BABA descent.  A nonsimple physical run beginning on the far side of
an already manufactured reflector has a first repeated switch.  The public
`PhysicalTrace.first_revisit_activated_outcome` theorem says that this second
repeat either enters a simple cycle or manufactures the oppositely oriented
reflector.  In the latter case the two supports are installed in the exact
states needed by the protected two-reflector theorem.

The compatible-pair branch already gives the literal four-vector cover of the
five selected closes in `RawSixEventReduction`, and therefore contradicts the
raw six-event obstruction.  The remaining branch is not hidden here: one must
turn a support interaction during protected repair into the same four-vector
cover (or directly pay one selected close).
-/

namespace GeneralN

/-- A literal branch-to-branch lobe together with its external stem edge is
already a nondegenerate manufactured reflector.  This packages the endpoint
shape produced by the overlap-minimal BABA analysis into the exact object
consumed by the second-repeat theorem.  Both the runway and the candy tail
are empty; the one recorded candy-head passage is the branch edge itself. -/
def manufacturedFlipReflectorOfLobe
    {w : Wiring} (C outside : Nat) (base : Tongues)
    (hbase : base C = false)
    (hbranch : w.link (3 * C + 1) = some (3 * C + 2))
    (hstem : w.link (3 * C) = some outside) :
    ManufacturedFlipReflector w (3 * C) outside where
  base := base
  mouthState := base
  returnState := base
  afterReturn := pin base (3 * C + 2)
  runway := []
  candy := []
  mouth := 3 * C
  firstArm := 3 * C + 1
  secondArm := 3 * C + 2
  runwayTrace := PhysicalTrace.nil (3 * C, base)
  candyTrace := by
    have harrive : arrive base (3 * C) = (3 * C + 1, base) := by
      simp [arrive, branchPort, hbase]
    exact PhysicalTrace.cons harrive hbranch
      (PhysicalTrace.nil (3 * C + 2, base))
  simple := by
    simp [SwitchSimple, passageSwitch]
  crossed := by
    have hdiv : (3 * C + 2) / 3 = C := by omega
    simp [arrive, hdiv]
  arms_ne := by omega
  entryEdge := w.symm _ _ hstem

/-- Coercion of the literal lobe package to the orientation-free
manufactured-reflector interface. -/
def manufacturedReflectorOfLobe
    {w : Wiring} (C outside : Nat) (base : Tongues)
    (hbase : base C = false)
    (hbranch : w.link (3 * C + 1) = some (3 * C + 2))
    (hstem : w.link (3 * C) = some outside) :
    ManufacturedReflector w (3 * C) outside :=
  .flip (manufacturedFlipReflectorOfLobe
    C outside base hbase hbranch hstem)

/-- Result of applying the first-repeat theorem a second time, starting on the
far side of an already manufactured reflector.  In the non-cycle branch the
new reflector has the opposite orientation, both support-groove hypotheses
are available, and the train actually reaches the start configuration of the
protected pair.

This is the raw track-and-switch form of the first/second-repeat step in
Mellit's argument. -/
theorem mellit_second_repeat_cycle_or_pair
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    {state : Tongues} {finish : Nat × Tongues}
    {passages : List Passage}
    (hstate : state = A.activatedState)
    (hA : PathGrooves A.toSupported.paths state)
    (htrace : PhysicalTrace w (e, state) passages finish)
    (hnonsimple : ¬ SwitchSimple passages) :
    (∃ atRepeat visited,
        stepN w visited (e, state) = some atRepeat ∧
        SettlesOnSimpleCycle w atRepeat) ∨
      (∃ (B : ManufacturedReflector w e g)
          (atRepeat : Nat × Tongues) (visited backSteps : Nat),
        stepN w visited (e, state) = some atRepeat ∧
        stepN w (visited + backSteps) (e, state) =
          some (g, B.activatedState) ∧
        PathGrooves A.toSupported.paths B.baseState ∧
        PathGrooves B.toSupported.paths B.activatedState ∧
        EventuallyPeriodic w (g, B.activatedState)) := by
  subst state
  have hentry : w.link g = some e :=
    w.symm _ _ A.entryEdge
  obtain ⟨atRepeat, visited, hvisited, houtcome⟩ :=
    htrace.first_revisit_activated_outcome hnonsimple hentry
  rcases houtcome with hcycle | hreflector
  · exact Or.inl ⟨atRepeat, visited, hvisited, hcycle⟩
  · obtain ⟨B, activated, backSteps, hBpaths, hBbase,
        hactivated, hback, _hpreserves⟩ := hreflector
    have hreach : stepN w (visited + backSteps)
        (e, A.activatedState) =
        some (g, B.activatedState) := by
      rw [stepN_add, hvisited]
      simpa [hactivated] using hback
    have hABase : PathGrooves A.toSupported.paths B.baseState := by
      rw [hBbase]
      exact hA
    have hBActivated :
        PathGrooves B.toSupported.paths B.activatedState := by
      simpa [hactivated] using hBpaths
    have hperiodic : EventuallyPeriodic w (g, B.activatedState) :=
      manufactured_pair_protected_repair_eventuallyPeriodic
        A B hABase hBActivated
    exact Or.inr ⟨B, atRepeat, visited, backSteps,
      hvisited, hreach, hABase, hBActivated, hperiodic⟩

/-- Forget the head-window data while retaining the same canonical six raw
events.  This lets the no-gap overlapping reduction feed the literal
accounting target in `SixEventSharpClosure`. -/
def RawOverlappingFiveWindowReduction.toSixEventReduction
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start) :
    RawSixEventReduction w N start := {
  z0 := C.z0
  z1 := C.z1
  z2 := C.z2
  z3 := C.z3
  z4 := C.z4
  z5 := C.z5
  order01 := C.order01
  order12 := C.order12
  order23 := C.order23
  order34 := C.order34
  order45 := C.order45
  event0 := C.event0
  event1 := C.event1
  event2 := C.event2
  event3 := C.event3
  event4 := C.event4
  event5 := C.event5
  first0 := C.first0
  a1 := C.a1
  q1 := C.q1
  a2 := C.a2
  q2 := C.q2
  a3 := C.a3
  q3 := C.q3
  a4 := C.a4
  q4 := C.q4
  a5 := C.a5
  q5 := C.q5
  frame1 := C.frame1
  frame2 := C.frame2
  frame3 := C.frame3
  frame4 := C.frame4
  frame5 := C.frame5
  tail_shape := C.tail_shape
}

/-- Before the second canonical repeated novelty, every represented vector is
already paid by first-writer history or by event zero.  At the endpoint
`z1+1` there is only one additional candidate, namely event one's own
post-vector.  The consecutive-event facts are essential here. -/
theorem RawOverlappingFiveWindowReduction.prefix_through_z1_paid
    {w : Wiring} {N t : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (ht : t ≤ C.z1 + 1) :
    restrictedTonguesAt w N start t ∈
      (rawFirstWriterHistory w N start (C.z5 + 1) ++
        [restrictedTonguesAt w N start (C.z0 + 1)]) ++
      [restrictedTonguesAt w N start (C.z1 + 1)] := by
  by_cases htEnd : t = C.z1 + 1
  · subst t
    exact List.mem_append_right _ (by simp)
  have htLe : t ≤ C.z1 := by omega
  have hz15 : C.z1 < C.z5 :=
    Nat.lt_trans C.order12
      (Nat.lt_trans C.order23
        (Nat.lt_trans C.order34 C.order45))
  have hcovered := restrictedTonguesAt_mem_finite_writer_cover
    w N start (C.z5 + 1) t (by omega)
  rcases List.mem_append.mp hcovered with hfirst | hrepeated
  · exact List.mem_append_left _
      (List.mem_append_left _ hfirst)
  · obtain ⟨k, hk, hvector⟩ := List.mem_map.mp hrepeated
    have Hk : RawRepeatedWriterNovelAt w N start k :=
      (mem_rawRepeatedWriterNovelTimes_iff.mp hk).2
    by_cases hbefore : t < k + 1
    · exact (Hk.2.2.post_ne_earlier hbefore hvector).elim
    have hkLt : k < C.z1 := by omega
    have hkEq : k = C.z0 := by
      by_cases hkBefore0 : k < C.z0
      · exact (C.first0 k hkBefore0 Hk).elim
      by_cases hkAt0 : k = C.z0
      · exact hkAt0
      · exact (C.no_event01 k (by omega) hkLt Hk).elim
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [List.mem_singleton]
    simpa [hkEq] using hvector.symm

/-- If the second-repeat pair is already support-compatible and is reached
no later than the first selected tail close, its four Gray corners cover all
five selected closes.  This is exactly the cover forbidden by
`RawSixEventReduction.no_tail_four_cover`. -/
theorem RawSixEventReduction.early_compatible_second_repeat_false
    {w : Wiring} {N g e K : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (R : RawSixEventReduction w N start)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    (hreach : stepN w K start = some (g, state))
    (hK : K ≤ R.z1 + 1) : False := by
  let times :=
    [R.z1 + 1, R.z2 + 1, R.z3 + 1, R.z4 + 1, R.z5 + 1]
  let history := rawFirstWriterHistory w N start (R.z5 + 1) ++
    [restrictedTonguesAt w N start (R.z0 + 1)]
  have o12 : R.z1 < R.z2 := R.order12
  have o23 : R.z2 < R.z3 := R.order23
  have o34 : R.z3 < R.z4 := R.order34
  have o45 : R.z4 < R.z5 := R.order45
  have htimes : ∀ j ∈ times, K ≤ j := by
    intro j hj
    dsimp [times] at hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact hK
    · omega
    · omega
    · omega
    · omega
  have hcover : FourNoveltyCover w N start times history :=
    manufactured_pair_absolute_four_novelty_cover
      A B state hA hB hAB hBA hreach times history htimes
  exact R.no_tail_four_cover hN (by
    simpa [FourNoveltyCover, times, history] using hcover)

/-- Payment-shaped interface for the six-event closure.  In the early
compatible-pair branch the raw obstruction is impossible, so in particular
the exact disjunction consumed by `no_selected_tail_close_paid` follows.
The theorem is intentionally stated with that literal target to make later
branch assembly type-check against the final accounting interface. -/
theorem RawSixEventReduction.early_compatible_second_repeat_pays
    {w : Wiring} {N g e K : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (R : RawSixEventReduction w N start)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    (hreach : stepN w K start = some (g, state))
    (hK : K ≤ R.z1 + 1) :
    restrictedTonguesAt w N start (R.z1 + 1) ∈
        rawFirstWriterHistory w N start (R.z5 + 1) ++
          [restrictedTonguesAt w N start (R.z0 + 1)] ∨
    restrictedTonguesAt w N start (R.z2 + 1) ∈
        rawFirstWriterHistory w N start (R.z5 + 1) ++
          [restrictedTonguesAt w N start (R.z0 + 1)] ∨
    restrictedTonguesAt w N start (R.z3 + 1) ∈
        rawFirstWriterHistory w N start (R.z5 + 1) ++
          [restrictedTonguesAt w N start (R.z0 + 1)] ∨
    restrictedTonguesAt w N start (R.z4 + 1) ∈
        rawFirstWriterHistory w N start (R.z5 + 1) ++
          [restrictedTonguesAt w N start (R.z0 + 1)] ∨
    restrictedTonguesAt w N start (R.z5 + 1) ∈
        rawFirstWriterHistory w N start (R.z5 + 1) ++
          [restrictedTonguesAt w N start (R.z0 + 1)] := by
  exact (R.early_compatible_second_repeat_false
    hN A B state hA hB hAB hBA hreach hK).elim

end GeneralN
