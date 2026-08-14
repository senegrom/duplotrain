import StateLawTwoSixUltra
import BoundaryAbsentSecondWriter
import BoundaryPresentSecondWriter
import PointwiseSimpleCycleTail

/-!
# The productive arbitrary-start boundary at `N+4`

The exact raw boundary target is the `N+4` analogue of
`ProductiveInitialBoundaryCap`.  This file closes the branch in which the
initially written switch is a productive first writer of the second
manufactured reflector and the resulting return prefix closes a stable
simple cycle.

The complementary branch is retained as a literal support-contact
certificate: a passage of the old switch-simple lead and a passage of the
returned prefix name the same switch.  No counting conclusion about that
contact is assumed here.
-/

namespace GeneralN

/-- The exact productive arbitrary-start boundary target needed by the raw
`N+4` state law. -/
def ProductiveInitialBoundaryNAddFour (w : Wiring) (N : Nat) : Prop :=
  forall {g e k0 : Nat} {original base : Tongues},
    w.link e = some g ->
    e = 3 * k0 ->
    k0 < N ->
    base = flipAt original k0 ->
    forall times : List Nat,
      (forall k, k ∈ times ->
        (stepN w k (g, base)).isSome) ->
      (VectorCount.restrict N original ::
        times.map (restrictedTonguesAt w N (g, base))).Nodup ->
      times.length + 1 <= N + 4

/-- The exact remaining physical residual after the present-second-writer
case fails to close a stable simple cycle. -/
structure SecondFirstWriterLeadContact
    (w : Wiring) (N g e k0 : Nat)
    (B : ManufacturedReflector w e g)
    (lead : List Passage) : Type where
  returned : SecondFirstWriterGlobalReturn w N g e k0 B
  oldPassage : Passage
  old_mem : oldPassage ∈ lead
  newPassage : Passage
  new_mem : newPassage ∈ returned.returnPath
  same_switch :
    passageSwitch oldPassage = passageSwitch newPassage

/-- A stable simple cycle has a one-vector tail: after its transient lap,
every depth has the settled tongue vector. -/
private theorem stable_simple_cycle_tail_distinct_le_one
    {w : Wiring} {N g : Nat} {settled : Tongues}
    {cycle : List Passage}
    (hnonempty : cycle ≠ [])
    (hstable : PhysicalTrace w (g, settled) cycle (g, settled))
    (hsimple : SwitchSimple cycle)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, settled))).Nodup) :
    times.length <= 1 := by
  have hcover : NoveltyCoverOn w N (g, settled) times
      [VectorCount.restrict N settled] 0 := by
    refine ⟨[], by simp, ?_⟩
    intro d _hd
    obtain ⟨port, hrun⟩ :=
      hstable.stable_simple_cycle_all_time hnonempty hsimple d
    simp [restrictedTonguesAt, tonguesAt, hrun]
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

/-- **Closed present-writer branch.**

The first complete manufacture and the returned prefix are covered by the
ordinary compressed two-reflector history, of size at most `N+3`.  Adding
the arbitrary pre-passage vector gives a history of size at most `N+4`.
The stable cycle contributes no fresh vector beyond its already historical
settled boundary.  Hence the boundary vector and all selected run vectors
fit in the same exact `N+4` budget. -/
theorem productive_initial_boundary_N_add_four_of_present_writer_cycle
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (R : SecondFirstWriterGlobalReturn w N g e k0 B)
    (lead : List Passage)
    (hcycle :
      PhysicalTrace w (g, B.baseState) (lead ++ R.returnPath)
          (g, R.after) /\
        PhysicalTrace w (g, R.after) (lead ++ R.returnPath)
          (g, R.after) /\
        SwitchSimple (lead ++ R.returnPath))
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length + 1 <= N + 4 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let returned := R.returnPath.length
  let totalTravel := firstTravel + returned
  let history := VectorCount.restrict N original ::
    A.preservedTwoHistoryCore B N
  have hAatBase :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  have hreachA :
      stepN w firstTravel (g, A.baseState) =
        some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hreachReturn :
      stepN w returned (e, A.activatedState) =
        some (g, R.after) := by
    have hraw := R.returnPath_trace.sound
    simpa [returned, hbase] using hraw
  have hreachTotal :
      stepN w totalTravel (g, A.baseState) =
        some (g, R.after) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachReturn
  have hreturnedLeExploration :
      returned <= B.exploration.length := by
    dsimp [returned]
    rw [R.returnPath_eq, List.length_take]
    exact Nat.min_le_right _ _
  have hprefix : forall d, d <= totalTravel ->
      restrictedTonguesAt w N (g, A.baseState) d ∈ history := by
    intro d hd
    by_cases hfirst : d <= firstTravel
    · apply List.mem_cons_of_mem
      apply A.mem_preservedTwoHistoryCore B
      apply Or.inl
      exact A.manufacturing_journey_mem_sharpHistory
        hA (by simpa [firstTravel] using hfirst)
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLeReturn : q <= returned := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hqLeJourney :
          q <= B.exploration.length + B.runway.length + 1 := by
        omega
      have hliveQ := stepN_prefix_some hqLeReturn hreachReturn
      have hshift := tonguesAt_add_of_reaches hreachA hliveQ
      have hmRaw := B.manufacturing_journey_mem_sharpHistory
        (N := N) hB (j := q) hqLeJourney
      have hm : restrictedTonguesAt w N
          (e, A.activatedState) q ∈
            B.sharpConstructionHistory N := by
        simpa [hbase] using hmRaw
      have heq :
          restrictedTonguesAt w N (g, A.baseState) d =
            restrictedTonguesAt w N (e, A.activatedState) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      apply List.mem_cons_of_mem
      exact A.mem_preservedTwoHistoryCore B (Or.inr hm)
  have hboundary :
      VectorCount.restrict N R.after ∈ history := by
    have hqLeJourney :
        returned <= B.exploration.length + B.runway.length + 1 := by
      omega
    have hmRaw := B.manufacturing_journey_mem_sharpHistory
      (N := N) hB (j := returned) hqLeJourney
    have hvector : restrictedTonguesAt w N
        (e, B.baseState) returned =
          VectorCount.restrict N R.after := by
      simp [restrictedTonguesAt, tonguesAt, returned,
        R.returnPath_trace.sound]
    apply List.mem_cons_of_mem
    apply A.mem_preservedTwoHistoryCore B
    apply Or.inr
    rwa [hvector] at hmRaw
  have hreturnLength : R.returnPath.length = R.time + 1 := by
    have htimeData := mem_rawFirstWriterTimes_iff.mp R.firstWriter
    rw [R.returnPath_eq, List.length_take]
    have hle : R.time + 1 <= B.exploration.length := by omega
    rw [Nat.min_eq_left hle]
  have hcycleNonempty : lead ++ R.returnPath ≠ [] := by
    intro hempty
    have hlen : (lead ++ R.returnPath).length = 0 := by
      rw [hempty]
      rfl
    simp only [List.length_append] at hlen
    rw [hreturnLength] at hlen
    omega
  have htail : forall tailTimes : List Nat,
      (forall k, k ∈ tailTimes ->
        (stepN w k (g, R.after)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N (g, R.after))).Nodup ->
      tailTimes.length <= 1 := by
    intro tailTimes _htailLive htailNodup
    exact stable_simple_cycle_tail_distinct_le_one
      hcycleNonempty hcycle.2.1 hcycle.2.2
        tailTimes htailNodup
  have hlocalNodup :
      (times.map
        (restrictedTonguesAt w N (g, A.baseState))).Nodup :=
    (List.nodup_cons.mp hnd).2
  have hcover := boundary_history_then_direct_tail_cover
    hreachTotal history hprefix hboundary htail
      (by omega) times hlive hlocalNodup
  have hextra :
      VectorCount.restrict N original ∈ history :=
    List.mem_cons_self
  have hcount := novelty_cover_count_with_historical_extra
    (VectorCount.restrict N original) hcover hextra hnd
  have hcoreLength :
      (A.preservedTwoHistoryCore B N).length <= N + 3 :=
    A.preservedTwoHistoryCore_length_le_N_add_three
      hN B hbase hAatBase hpre
  have hhistoryLength : history.length <= N + 4 := by
    dsimp [history]
    omega
  omega

/-- **Present-second-writer frontier at exact `N+4`.**

For a protected opposite reflector pair, suppose the productive initial
switch occurs among the second construction's first writers.  Following a
switch-simple old lead, either all boundary/sample vectors fit in `N+4`, or
there is a concrete old-lead/returned-prefix support contact. -/
theorem productive_initial_boundary_N_add_four_or_support_contact
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (hentry : w.link e = some g)
    (hstem : e = 3 * k0)
    (_hk0 : k0 < N)
    (original base : Tongues)
    (_hbaseFlip : base = flipAt original k0)
    (A : ManufacturedReflector w g e)
    (hAbase : A.baseState = base)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (hpresent : k0 ∈ B.constructionFirstWriterSwitches N)
    (lead : List Passage)
    (hlead : PhysicalTrace w (g, B.baseState) lead
      (e, B.baseState))
    (hleadSimple : SwitchSimple lead)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, base)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map (restrictedTonguesAt w N (g, base))).Nodup) :
    times.length + 1 <= N + 4 \/
      Nonempty (SecondFirstWriterLeadContact
        w N g e k0 B lead) := by
  obtain ⟨R⟩ := second_first_writer_present_returns_global_start
    hN hentry hstem B hpresent
  rcases R.cycle_or_lead_contact B.baseState lead hlead hleadSimple with
    hcycle | hcontact
  · apply Or.inl
    apply productive_initial_boundary_N_add_four_of_present_writer_cycle
      hN A B original hbase hA hB hpre R lead hcycle times
    · simpa [hAbase] using hlive
    · simpa [hAbase] using hnd
  · apply Or.inr
    obtain ⟨oldPassage, hold, newPassage, hnew, hsame⟩ := hcontact
    exact ⟨{
      returned := R
      oldPassage := oldPassage
      old_mem := hold
      newPassage := newPassage
      new_mem := hnew
      same_switch := hsame
    }⟩

end GeneralN
