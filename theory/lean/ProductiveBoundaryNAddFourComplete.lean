import PartialSecondRunNAddFour
import BoundaryAbsentProtectedPair

/-!
# Exact completion frontier for the productive `N+4` boundary

Eliminations for the saving residual: a dead second probe and a preserved
second cycle are too short outright; an absent boundary with an absent
second writer charges the reserved switch coordinate; and a first stay
reflector lowers every fully protected repair tail to one novelty.  No
finite-instance argument is used.
-/

namespace GeneralN

/-- The arbitrary historical boundary vector is counted together with a
two-manufacture novelty cover.  This is the exact-extra form of
`two_journeys_then_shared_history_novelty_count`. -/
theorem ManufacturedReflector.two_journeys_then_shared_history_novelty_count_with_extra
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (history : List (List Bool))
    (hhistory : ∀ x,
      x ∈ A.sharpConstructionHistory N ∨
        x ∈ B.sharpConstructionHistory N → x ∈ history)
    (budget : Nat)
    (htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes,
        (stepN w k (g, B.activatedState)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
      NoveltyCoverOn w N (g, B.activatedState) tailTimes
        history budget)
    (extra : List Bool)
    (hextra : extra ∈ history)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (extra :: times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length + 1 ≤ history.length + budget :=
  noveltyCoverOn_distinct_count_with_extra
    (A.two_journeys_then_shared_history_novelty_cover B hbase hApaths
      hBpaths history hhistory budget htail times hlive
      (List.nodup_cons.mp hnd).2) hextra hnd

/-- The dead second probe is strictly too small to support a saturated
productive boundary.  This branch does not spend either boundary saving. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_dead_second_probe
    {w : Wiring} {N : Nat}
    (R : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hdead : stepN w (N + 1)
      (R.source.e, R.A.activatedState) = none) : False := by
  have hA : PathGrooves R.A.toSupported.paths R.A.activatedState := R.grooves
  have hlive : ∀ k ∈ R.source.times,
      (stepN w k (R.source.g, R.A.baseState)).isSome := by
    intro k hk
    simpa [R.reflector_base] using R.source.live k hk
  have hnd : (R.source.times.map
      (restrictedTonguesAt w N
        (R.source.g, R.A.baseState))).Nodup := by
    have htail := (List.nodup_cons.mp R.source.distinct).2
    simpa [R.reflector_base] using htail
  have hshort :=
    PartialSecondRunNAddFour.ManufacturedReflector.dead_second_run_distinct_le_N_add_two
      hN R.A hA hdead R.source.times hlive hnd
  have hsaturated := R.source.saturated
  omega

/-- A support-preserving stable second cycle is also too small for boundary
saturation.  The concrete history consists of the arbitrary pre-passage
vector, the coefficient-one first-journey/lead history, and the settled
cycle vector. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_preserved_second_cycle
    {w : Wiring} {N : Nat}
    (R : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (C : PartialSecondCycleOutcome w
      (R.source.e, R.A.activatedState) N)
    (hend : PathGrooves R.A.toSupported.paths C.atRepeat.2) : False := by
  let firstTravel := R.A.exploration.length + R.A.runway.length + 1
  let shift := firstTravel + C.lead.length
  let localStart : Nat × Tongues :=
    (R.source.e, R.A.activatedState)
  let core := R.A.continuationHistory N localStart C.lead.length
  let history := VectorCount.restrict N R.source.original ::
    (core ++ [VectorCount.restrict N C.settled])
  have hA : PathGrooves R.A.toSupported.paths R.A.activatedState := R.grooves
  have hreachA : stepN w firstTravel
      (R.source.g, R.A.baseState) = some localStart := by
    simpa [firstTravel, localStart] using
      R.A.manufacturing_journey_reaches_activated hA
  have hreach : stepN w shift (R.source.g, R.A.baseState) =
      some C.atRepeat := by
    dsimp [shift]
    rw [stepN_add, hreachA]
    exact C.lead_trace.sound
  have hglobal : ∀ d,
      (stepN w d (R.source.g, R.A.baseState)).isSome →
      restrictedTonguesAt w N (R.source.g, R.A.baseState) d ∈
        history := by
    intro d _hlive
    by_cases hbefore : d ≤ shift
    · apply List.mem_cons_of_mem
      apply List.mem_append_left
      dsimp [core]
      apply R.A.journey_then_continuation_mem
        hA C.lead_trace C.lead_simple
      simpa [shift, firstTravel] using hbefore
    · let q := d - shift
      have hq : 0 < q := by
        dsimp [q]
        omega
      have hd : d = shift + q := by
        dsimp [q]
        omega
      obtain ⟨port, hlocal⟩ := C.positive_settled q hq
      have hrun : stepN w d (R.source.g, R.A.baseState) =
          some (port, C.settled) := by
        rw [hd, stepN_add, hreach]
        exact hlocal
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      simp [restrictedTonguesAt, tonguesAt, hrun]
  have horiginal : VectorCount.restrict N R.source.original ∈ history :=
    List.mem_cons_self
  have hlenCore : core.length ≤ N + 2 := by
    dsimp [core, localStart]
    exact R.A.continuationHistory_length_le
      hN rfl C.lead_trace C.lead_simple hA hend
  have hlen : history.length ≤ N + 4 := by
    simp [history]
    omega
  apply R.source.false_of_global_history history hlen horiginal
  intro d hd
  have hdA : (stepN w d
      (R.source.g, R.A.baseState)).isSome := by
    simpa [R.reflector_base] using hd
  simpa [R.reflector_base] using hglobal d hdA


theorem ProductiveBoundaryNAddFourSavingResidual.false_of_absent_protected_pair_of_second_writer_absent
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (habsentA : Not (Membership.mem
      (S.A.exploration.map passageSwitch) S.source.k0))
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hbase : B.baseState = S.A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves S.A.toSupported.paths B.preReturn.2)
    (habsentB : Not (Membership.mem
      (B.constructionFirstWriterSwitches N) S.source.k0)) :
    False := by
  have hApaths : PathGrooves S.A.toSupported.paths
      S.A.activatedState := S.grooves
  have hlive : forall k, Membership.mem S.source.times k ->
      (stepN w k (S.source.g, S.A.baseState)).isSome := by
    intro k hk
    simpa [S.reflector_base] using S.source.live k hk
  have hnd : (VectorCount.restrict N S.source.original ::
      S.source.times.map
        (restrictedTonguesAt w N
          (S.source.g, S.A.baseState))).Nodup := by
    simpa [S.reflector_base] using S.source.distinct
  cases hkind : S.A with
  | stay R =>
      have habsentAConcrete : Not (List.Mem S.source.k0
          ((ManufacturedReflector.stay R).exploration.map passageSwitch)) := by
        intro hm
        apply habsentA
        rw [hkind]
        exact hm
      have hbound :=
        R.absent_initial_protected_pair_all_run_distinct_le_N_add_four
          hN B S.source.original
            (by simpa [hkind] using hbase)
            (by simpa [hkind] using hApaths)
            hBpaths (by simpa [hkind] using hpre)
            S.source.switch_lt
            habsentAConcrete
            habsentB S.source.times
            (by simpa [hkind] using hlive)
            (by simpa [hkind] using hnd)
      have hsaturated := S.source.saturated
      omega
  | flip R =>
      have habsentAConcrete : Not (List.Mem S.source.k0
          ((ManufacturedReflector.flip R).exploration.map passageSwitch)) := by
        intro hm
        apply habsentA
        rw [hkind]
        exact hm
      have hbound :=
        R.absent_initial_protected_pair_all_run_distinct_le_N_add_four
          hN B S.source.original
            (by simpa [hkind] using hbase)
            (by simpa [hkind] using hApaths)
            hBpaths (by simpa [hkind] using hpre)
            S.source.switch_lt
            habsentAConcrete
            habsentB S.source.times
            (by simpa [hkind] using hlive)
            (by simpa [hkind] using hnd)
      have hsaturated := S.source.saturated
      omega


/-- A first stay reflector lowers every fully protected repair tail to one
fresh vector over any history representing both manufacturing journeys.
The only two-vector branch in the generic repair theorem is a completed
repair; for a stay action its extra action-applied pre-return corner is
literally the already historical pre-return vector. -/
theorem ManufacturedStayReflector.protected_repair_one_novelty_over_history
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedStayReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.preReturn.2)
    (history : List (List Bool))
    (hhistory : forall x,
      List.Mem x ((ManufacturedReflector.stay R).sharpConstructionHistory N) \/
        List.Mem x (B.sharpConstructionHistory N) -> List.Mem x history)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
  have hinitialHistorical :
      List.Mem (VectorCount.restrict N B.activatedState) history := by
    apply hhistory
    right
    unfold ManufacturedReflector.sharpConstructionHistory
    exact List.mem_append_right _ List.mem_cons_self
  have hpreHistorical :
      List.Mem (VectorCount.restrict N B.preReturn.2) history := by
    apply hhistory
    right
    unfold ManufacturedReflector.sharpConstructionHistory
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine Exists.intro B.exploration.length ?_
    constructor
    case left =>
      apply List.mem_range.mpr
      omega
    case right =>
      simp [restrictedTonguesAt, tonguesAt,
        B.exploration_trace.sound]
  rcases manufactured_pair_protected_repair_novelty_outcomes
      (ManufacturedReflector.stay R) B hA hB history
        hinitialHistorical hpreHistorical with
    hone | hfacing | hchanged | hcomplete
  case inl =>
    exact hone times hlive hnd
  case inr.inl =>
    exact hfacing.one_novelty_of_preReturn
      hN hA hB history hinitialHistorical hpreHistorical times hlive
  case inr.inr.inl =>
    exact (hchanged.impossible_of_preReturn_grooved hB hpre).elim
  case inr.inr.inr =>
    obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
    have haPreHistorical : List.Mem
        (VectorCount.restrict N
          ((ManufacturedReflector.stay R).toSupported.action.apply
            B.preReturn.2)) history := by
      simpa [ManufacturedReflector.toSupported,
        ManufacturedStayReflector.toSupported, LocalAction.apply] using
          hpreHistorical
    exact (ManufacturedReflector.stay R).completed_protected_route_one_novelty_of_action_preReturn
      B hA hB hrepair hAfinal hBfinal history
        hinitialHistorical hpreHistorical haPreHistorical times hlive

/-- A fully protected opposite pair whose first reflector is a stay
reflector cannot saturate the productive boundary.  The two construction
histories cost at most `N+2`; adjoining the arbitrary boundary vector costs
one; and the specialized repair tail above costs one. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_first_stay_protected_pair
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedStayReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.stay R)
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hbase : B.baseState =
      (ManufacturedReflector.stay R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.preReturn.2) :
    False := by
  let A : ManufacturedReflector w S.source.g S.source.e :=
    ManufacturedReflector.stay R
  let history := VectorCount.restrict N S.source.original ::
    A.preservedTwoHistoryCore B N
  have hApaths : PathGrooves A.toSupported.paths A.activatedState := by
    simpa [A, hAeq] using S.grooves
  have hAbase : A.baseState = S.source.base := by
    simpa [A, hAeq] using S.reflector_base
  have hbaseA : B.baseState = A.activatedState := by
    simpa [A] using hbase
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbaseA]
    exact hApaths
  have hhistory : forall x,
      List.Mem x (A.sharpConstructionHistory N) \/
        List.Mem x (B.sharpConstructionHistory N) ->
      List.Mem x history := by
    intro x hx
    apply List.mem_cons_of_mem
    exact A.mem_preservedTwoHistoryCore B hx
  have hextra : List.Mem
      (VectorCount.restrict N S.source.original) history := by
    dsimp [history]
    exact List.mem_cons_self
  have htail : forall tailTimes : List Nat,
      (forall k, List.Mem k tailTimes ->
        (stepN w k (S.source.g, B.activatedState)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N
          (S.source.g, B.activatedState))).Nodup ->
      NoveltyCoverOn w N (S.source.g, B.activatedState)
        tailTimes history 1 := by
    intro tailTimes htailLive htailNodup
    exact R.protected_repair_one_novelty_over_history
      hN B (by simpa [A] using hAatBase) hBpaths hpre
        history (by simpa [A] using hhistory)
          tailTimes htailLive htailNodup
  have hlive : forall k, List.Mem k S.source.times ->
      (stepN w k (S.source.g, A.baseState)).isSome := by
    intro k hk
    simpa [hAbase] using S.source.live k hk
  have hnd : (VectorCount.restrict N S.source.original ::
      S.source.times.map
        (restrictedTonguesAt w N
          (S.source.g, A.baseState))).Nodup := by
    simpa [hAbase] using S.source.distinct
  have hcount :=
    A.two_journeys_then_shared_history_novelty_count_with_extra
      B hbaseA hApaths hBpaths history hhistory 1 htail
        (VectorCount.restrict N S.source.original) hextra
          S.source.times hlive hnd
  have hcore := R.protectedHistory_length_le_N_add_two
    hN B hbase (by simpa [A] using hAatBase) hpre
  have hsaturated := S.source.saturated
  dsimp [history] at hcount
  dsimp only [A] at hcount
  omega

end GeneralN
