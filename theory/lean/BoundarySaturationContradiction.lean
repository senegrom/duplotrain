import ArbitraryStartCoefficientOneBoundary
import PartialSecondRunSharp
import BoundaryAbsentSecondWriter
import KnownEdgeNAddFiveAlt

/-!
# The productive initial-boundary saturation

This file narrows the sole remaining arbitrary-start boundary obstruction.
It contains only general-`N` arguments over the raw `Wiring`/`stepN`
semantics.
-/

namespace GeneralN

/-- A saturated productive boundary after the second probe has completed an
opposite reflector and the first reflector''s reusable support is still
grooved immediately before that second reflector returns.

This is strictly narrower than
`ProductiveInitialBoundaryHistorySaturation`: death, a one-vector second
cycle, and first support damage have all been removed. -/
structure ProductiveInitialProtectedPairSaturation
    (w : Wiring) (N : Nat) : Type where
  source : ProductiveInitialBoundaryHistorySaturation w N
  B : ManufacturedReflector w source.e source.g
  baseB : B.baseState = source.A.activatedState
  groovesB : PathGrooves B.toSupported.paths B.activatedState
  preGrooves :
    PathGrooves source.A.toSupported.paths B.preReturn.2

/-- Saturation cannot end in either incomplete second-run branch. Nor can
the completed second construction have damaged the first reusable support:
all three alternatives already have the strict `N+5` all-run bound.
Therefore every remaining counterexample contains a protected opposite
reflector pair. -/
theorem productive_boundary_history_saturation_has_protected_pair
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (S : ProductiveInitialBoundaryHistorySaturation w N) :
    Nonempty (ProductiveInitialProtectedPairSaturation w N) := by
  have hA :
      PathGrooves S.A.toSupported.paths S.A.activatedState := by
    rw [S.activated.symm]
    exact S.grooves
  have hndA :
      (S.times.map
        (restrictedTonguesAt w N
          (S.g, S.A.baseState))).Nodup := by
    have htail := (List.nodup_cons.mp S.distinct).2
    simpa [S.reflector_base] using htail
  have hsaturated := S.saturated
  have hback : w.link S.g = some S.e :=
    w.symm _ _ S.entry
  cases hprobe :
      stepN w (N + 1) (S.e, S.A.activatedState) with
  | none =>
      have hsmall :=
        PartialSecondRunSharp.ManufacturedReflector.dead_second_run_distinct_le_N_add_five
          hN S.A hA hprobe S.times
            (fun k hk => by
              simpa [S.reflector_base] using S.live k hk)
            hndA
      omega
  | some finish =>
      rcases first_activated_trace_outcome_sharp_partial
          hN hprobe hback with hcycle | hreflector
      case inl =>
        let C := Classical.choice hcycle
        have hsmall :=
          PartialSecondRunSharp.PartialSecondCycleOutcome.all_run_distinct_le_N_add_five
            hN S.A hA C S.times
              (fun k hk => by
                simpa [S.reflector_base] using S.live k hk)
              hndA
        omega
      case inr =>
        let B := Exists.choose hreflector
        have hstateData := Exists.choose_spec hreflector
        let state := Exists.choose hstateData
        have hdata := Exists.choose_spec hstateData
        have hB :
            PathGrooves B.toSupported.paths state :=
          hdata.2.1
        have hbase :
            B.baseState = S.A.activatedState :=
          hdata.2.2.1
        have hactivated :
            state = B.activatedState :=
          hdata.2.2.2.1
        have hBactivated :
            PathGrooves B.toSupported.paths B.activatedState := by
          rw [hactivated.symm]
          exact hB
        have hbaseActivated :
            B.baseState = S.A.activatedState := by
          exact hbase
        rcases S.A.preReturn_grooved_or_changed_support_contact
            B hbaseActivated hA with hpre | hcontact
        case inl =>
          exact Nonempty.intro {
              source := S
              B := B
              baseB := hbaseActivated
              groovesB := hBactivated
              preGrooves := hpre
            }
        case inr =>
          let C := Exists.choose hcontact
          have hnextData := Exists.choose_spec hcontact
          let next := Exists.choose hnextData
          have hcontactData := Exists.choose_spec hnextData
          have harrive := hcontactData.1
          have hchanged := hcontactData.2
          have hsmall :=
            S.A.changed_support_contact_all_run_distinct_le_N_add_five
              hN B C hbaseActivated hA harrive hchanged
                S.times
                (fun k hk => by
                  simpa [S.reflector_base] using S.live k hk)
                hndA
          omega

/-! ## The completed protected pair -/

/-- If the ordinary coefficient-one pair history is already one slot sharper,
the pre-passage vector can be adjoined without exceeding the final N+6
capacity. The protected tail contributes only three vectors beyond its
time-zero boundary. -/
private theorem protected_pair_with_extra_of_core_le_N_add_two
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (hcore :
      (A.preservedTwoHistoryCore B N).length <= N + 2)
    (times : List Nat)
    (hlive : forall k, Membership.mem times k ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length + 1 <= N + 6 := by
  let firstTravel :=
    A.exploration.length + A.runway.length + 1
  let secondTravel :=
    B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let history :=
    VectorCount.restrict N original ::
      A.preservedTwoHistoryCore B N
  have hreachA :
      stepN w firstTravel (g, A.baseState) =
        some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hreachB :
      stepN w secondTravel (e, A.activatedState) =
        some (g, B.activatedState) := by
    have hraw := B.manufacturing_journey_reaches_activated hB
    simpa [secondTravel, hbase] using hraw
  have hreachTotal :
      stepN w totalTravel (g, A.baseState) =
        some (g, B.activatedState) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachB
  have hprefix : forall d, d <= totalTravel ->
      List.Mem
        (restrictedTonguesAt w N (g, A.baseState) d) history := by
    intro d hd
    by_cases hfirst : d <= firstTravel
    case pos =>
      apply List.mem_cons_of_mem
      apply A.mem_preservedTwoHistoryCore B
      apply Or.inl
      exact A.manufacturing_journey_mem_sharpHistory
        hA (by simpa [firstTravel] using hfirst)
    case neg =>
      let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLe : q <= secondTravel := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hliveQ := stepN_prefix_some hqLe hreachB
      have hshift :=
        tonguesAt_add_of_reaches hreachA hliveQ
      have hmRaw :=
        B.manufacturing_journey_mem_sharpHistory
          (N := N) hB (j := q)
          (by simpa [secondTravel] using hqLe)
      have hm := hmRaw
      simp only [hbase] at hm
      have heq :
          restrictedTonguesAt w N (g, A.baseState) d =
            restrictedTonguesAt w N
              (e, A.activatedState) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      apply List.mem_cons_of_mem
      exact A.mem_preservedTwoHistoryCore B (Or.inr hm)
  have hboundary :
      List.Mem
        (VectorCount.restrict N B.activatedState) history := by
    apply List.mem_cons_of_mem
    apply A.mem_preservedTwoHistoryCore B
    apply Or.inr
    simp [ManufacturedReflector.sharpConstructionHistory]
  have hAatBase :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  have htail : forall tailTimes : List Nat,
      (forall k, Membership.mem tailTimes k ->
        (stepN w k (g, B.activatedState)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N
          (g, B.activatedState))).Nodup ->
      tailTimes.length <= 4 := by
    intro tailTimes htailLive htailNodup
    exact manufactured_pair_protected_repair_distinct_le_four
      A B hAatBase hB tailTimes htailLive htailNodup
  have hcover :=
    boundary_history_then_direct_tail_cover
      hreachTotal history hprefix hboundary htail
        (by omega) times hlive (List.nodup_cons.mp hnd).2
  have hextra :
      List.Mem
        (VectorCount.restrict N original) history := by
    exact List.mem_cons_self
  have hcount :=
    novelty_cover_count_with_historical_extra
      (VectorCount.restrict N original) hcover hextra hnd
  have hhistory : history.length <= N + 3 := by
    dsimp [history]
    omega
  omega


/-! ## Equality conditions forced by saturation -/

/-- A stay reflector has no omitted facing-mouth coordinate. Consequently its
compressed two-history core is one slot sharper than the generic flip/stay
bound. -/
private theorem stay_preserved_core_length_le_N_add_two
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (R : ManufacturedStayReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase :
      B.baseState =
        (ManufacturedReflector.stay R).activatedState)
    (hA :
      PathGrooves
        (ManufacturedReflector.stay R).toSupported.paths
        (ManufacturedReflector.stay R).activatedState)
    (hpre :
      PathGrooves
        (ManufacturedReflector.stay R).toSupported.paths
        B.preReturn.2) :
    ((ManufacturedReflector.stay R).preservedTwoHistoryCore
      B N).length <= N + 2 := by
  let A : ManufacturedReflector w g e :=
    ManufacturedReflector.stay R
  have hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  have hcharge :=
    A.reusable_add_second_first_writers_le
      hN B hbaseGrooves hpre
  have hboundary :
      List.Mem
        (VectorCount.restrict N A.activatedState)
        (B.writerConstructionHistory N) := by
    dsimp [A]
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have heq :
      A.exploration.length = A.reusableSwitches.length := by
    simp [A, ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches]
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

/-- The equality case cannot start with a stay reflector. Its sharper core,
together with the historical-extra cover, would hold the original vector and
all sampled vectors in only N+6 slots. -/
theorem ProductiveInitialProtectedPairSaturation.first_is_flip
    {w : Wiring} {N : Nat}
    (P : ProductiveInitialProtectedPairSaturation w N)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N)) :
    Exists fun R : ManufacturedFlipReflector w
        P.source.g P.source.e =>
      P.source.A = ManufacturedReflector.flip R := by
  let S := P.source
  have hA :
      PathGrooves S.A.toSupported.paths S.A.activatedState := by
    rw [S.activated.symm]
    exact S.grooves
  cases hkind : S.A with
  | stay R =>
      have hcoreR :=
        stay_preserved_core_length_le_N_add_two
          hN R P.B (by simpa [S, hkind] using P.baseB)
          (by simpa [S, hkind] using hA)
          (by simpa [S, hkind] using P.preGrooves)
      have hcore :
          (S.A.preservedTwoHistoryCore P.B N).length <=
            N + 2 := by
        simpa [hkind] using hcoreR
      have hbound :=
        protected_pair_with_extra_of_core_le_N_add_two
          hN S.A P.B S.original P.baseB hA P.groovesB
            P.preGrooves hcore S.times
            (fun k hk => by
              simpa [S.reflector_base] using S.live k hk)
            (by
              simpa [S.reflector_base] using S.distinct)
      have hsaturated := S.saturated
      omega
  | flip R =>
      exact Exists.intro R rfl
/-! ## The original vector is genuinely outside the ordinary pair cover -/

/-- If the pre-passage vector is already represented by the ordinary
coefficient-one pair core, the same protected-tail count closes at N+6
without adjoining any new history entry. -/
private theorem protected_pair_with_extra_mem_core
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (hextra :
      List.Mem (VectorCount.restrict N original)
        (A.preservedTwoHistoryCore B N))
    (times : List Nat)
    (hlive : forall k, Membership.mem times k ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length + 1 <= N + 6 := by
  let firstTravel :=
    A.exploration.length + A.runway.length + 1
  let secondTravel :=
    B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let history := A.preservedTwoHistoryCore B N
  have hreachA :
      stepN w firstTravel (g, A.baseState) =
        some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hreachB :
      stepN w secondTravel (e, A.activatedState) =
        some (g, B.activatedState) := by
    have hraw := B.manufacturing_journey_reaches_activated hB
    simpa [secondTravel, hbase] using hraw
  have hreachTotal :
      stepN w totalTravel (g, A.baseState) =
        some (g, B.activatedState) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachB
  have hprefix : forall d, d <= totalTravel ->
      List.Mem
        (restrictedTonguesAt w N (g, A.baseState) d)
        history := by
    intro d hd
    by_cases hfirst : d <= firstTravel
    case pos =>
      apply A.mem_preservedTwoHistoryCore B
      apply Or.inl
      exact A.manufacturing_journey_mem_sharpHistory
        hA (by simpa [firstTravel] using hfirst)
    case neg =>
      let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLe : q <= secondTravel := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hliveQ := stepN_prefix_some hqLe hreachB
      have hshift :=
        tonguesAt_add_of_reaches hreachA hliveQ
      have hmRaw :=
        B.manufacturing_journey_mem_sharpHistory
          (N := N) hB (j := q)
          (by simpa [secondTravel] using hqLe)
      have hm := hmRaw
      simp only [hbase] at hm
      have heq :
          restrictedTonguesAt w N (g, A.baseState) d =
            restrictedTonguesAt w N
              (e, A.activatedState) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      exact A.mem_preservedTwoHistoryCore B (Or.inr hm)
  have hboundary :
      List.Mem
        (VectorCount.restrict N B.activatedState) history := by
    apply A.mem_preservedTwoHistoryCore B
    apply Or.inr
    simp [ManufacturedReflector.sharpConstructionHistory]
  have hAatBase :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  have htail : forall tailTimes : List Nat,
      (forall k, Membership.mem tailTimes k ->
        (stepN w k (g, B.activatedState)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N
          (g, B.activatedState))).Nodup ->
      tailTimes.length <= 4 := by
    intro tailTimes htailLive htailNodup
    exact manufactured_pair_protected_repair_distinct_le_four
      A B hAatBase hB tailTimes htailLive htailNodup
  have hcover :=
    boundary_history_then_direct_tail_cover
      hreachTotal history hprefix hboundary htail
        (by omega) times hlive (List.nodup_cons.mp hnd).2
  have hcount :=
    novelty_cover_count_with_historical_extra
      (VectorCount.restrict N original) hcover
        (by simpa [history] using hextra) hnd
  have hhistory : history.length <= N + 3 := by
    dsimp [history]
    exact A.preservedTwoHistoryCore_length_le_N_add_three
      hN B hbase hAatBase hpre
  omega

/-- In a saturated protected pair, the pre-passage vector is not represented
by the ordinary pair core. Thus the missing unit is a real boundary state,
not an artifact of the arbitrary list of sample times. -/
theorem ProductiveInitialProtectedPairSaturation.original_not_mem_pair_core
    {w : Wiring} {N : Nat}
    (P : ProductiveInitialProtectedPairSaturation w N)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N)) :
    Not (List.Mem
      (VectorCount.restrict N P.source.original)
      (P.source.A.preservedTwoHistoryCore P.B N)) := by
  intro hmem
  let S := P.source
  have hA :
      PathGrooves S.A.toSupported.paths S.A.activatedState := by
    rw [S.activated.symm]
    exact S.grooves
  have hbound :=
    protected_pair_with_extra_mem_core
      hN S.A P.B S.original P.baseB hA P.groovesB
        P.preGrooves (by simpa [S] using hmem) S.times
        (fun k hk => by
          simpa [S.reflector_base] using S.live k hk)
        (by
          simpa [S.reflector_base] using S.distinct)
  have hsaturated := S.saturated
  omega

/-! ## Saturation of the coordinate charge -/

/-- Exact size of the protected pair core when the first reflector flips.
The extra three are the reusable support's one omitted mouth, the second
history's initial vector, and its activated endpoint. -/
private theorem flip_preserved_core_length
    {w : Wiring} {N g e : Nat}
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase :
      B.baseState =
        (ManufacturedReflector.flip R).activatedState) :
    ((ManufacturedReflector.flip R).preservedTwoHistoryCore
      B N).length =
      (ManufacturedReflector.flip R).reusableSwitches.length +
        (rawFirstWriterTimes w N (e, B.baseState)
          B.exploration.length).length + 3 := by
  have hboundary :
      List.Mem
        (VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState)
        (B.writerConstructionHistory N) := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have heq :
      (ManufacturedReflector.flip R).exploration.length =
        (ManufacturedReflector.flip R).reusableSwitches.length + 1 := by
    simp [ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches]
    omega
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    (ManufacturedReflector.flip R).sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

/-- The disjoint reusable/second-writer coordinate charge is itself saturated.
If one coordinate were spare, the pair core would be N+2 and the historical
extra theorem would contradict the N+6-state tail. -/
theorem ProductiveInitialProtectedPairSaturation.coordinate_charge_eq
    {w : Wiring} {N : Nat}
    (P : ProductiveInitialProtectedPairSaturation w N)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (R : ManufacturedFlipReflector w
      P.source.g P.source.e)
    (hkind : P.source.A = ManufacturedReflector.flip R) :
    P.source.A.reusableSwitches.length +
      (rawFirstWriterTimes w N
        (P.source.e, P.B.baseState)
        P.B.exploration.length).length = N := by
  let S := P.source
  have hA :
      PathGrooves S.A.toSupported.paths S.A.activatedState := by
    rw [S.activated.symm]
    exact S.grooves
  have hbaseGrooves :
      PathGrooves S.A.toSupported.paths P.B.baseState := by
    rw [P.baseB]
    exact hA
  have hcharge :=
    S.A.reusable_add_second_first_writers_le
      hN P.B hbaseGrooves P.preGrooves
  by_cases heq :
      S.A.reusableSwitches.length +
        (rawFirstWriterTimes w N
          (S.e, P.B.baseState)
          P.B.exploration.length).length = N
  case pos =>
    exact heq
  case neg =>
    have hcoreEqR :=
      flip_preserved_core_length (N := N) R P.B
        (by simpa [S, hkind] using P.baseB)
    have hcoreEq :
        (P.source.A.preservedTwoHistoryCore P.B N).length =
          P.source.A.reusableSwitches.length +
            (rawFirstWriterTimes w N
              (P.source.e, P.B.baseState)
              P.B.exploration.length).length + 3 := by
      simpa only [hkind] using hcoreEqR
    have hchargeSource :
        P.source.A.reusableSwitches.length +
          (rawFirstWriterTimes w N
            (P.source.e, P.B.baseState)
            P.B.exploration.length).length <= N := by
      simpa [S] using hcharge
    have hneSource : Not (
        P.source.A.reusableSwitches.length +
          (rawFirstWriterTimes w N
            (P.source.e, P.B.baseState)
            P.B.exploration.length).length = N) := by
      simpa [S] using heq
    have hcoreSource :
        (P.source.A.preservedTwoHistoryCore P.B N).length <=
          N + 2 := by
      omega
    have hcore :
        (S.A.preservedTwoHistoryCore P.B N).length <= N + 2 := by
      simpa [S] using hcoreSource
    have hbound :=
      protected_pair_with_extra_of_core_le_N_add_two
        hN S.A P.B S.original P.baseB hA P.groovesB
          P.preGrooves hcore S.times
          (fun k hk => by
            simpa [S.reflector_base] using S.live k hk)
          (by
            simpa [S.reflector_base] using S.distinct)
    have hsaturated := S.saturated
    omega


/-! ## Every counted coordinate is physically named -/

/-
/-- Equality in the reusable/first-writer charge means that every switch
coordinate below N occurs in one of those two disjoint lists. -/
private theorem mem_reusable_or_second_writer_of_full_charge
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (hfull :
      A.reusableSwitches.length +
        (rawFirstWriterTimes w N (e, B.baseState)
          B.exploration.length).length = N)
    (k : Nat) (hk : k < N) :
    Or (List.Mem k A.reusableSwitches)
      (Exists fun t =>
        And
          (List.Mem t
            (rawFirstWriterTimes w N (e, B.baseState)
              B.exploration.length))
          (rawWriterAt w (e, B.baseState) t = k)) := by
  classical
  let times :=
    rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length
  let writers := times.map (rawWriterAt w (e, B.baseState))
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact nodup_filter_nat_two_history _ List.nodup_range
  have hwritersNodup : writers.Nodup := by
    dsimp [writers]
    apply nodup_map_nat_of_injective_on_two_history
    case left =>
      intro i hi j hj hEq
      have hiData :=
        mem_rawFirstWriterTimes_iff.mp (by
          simpa [times] using hi)
      have hjData :=
        mem_rawFirstWriterTimes_iff.mp (by
          simpa [times] using hj)
      exact rawFirstWriterAt_injective
        hiData.2 hjData.2 hEq
    case right =>
      exact htimesNodup
  have hdisjoint : forall oldSwitch,
      List.Mem oldSwitch A.reusableSwitches ->
      forall freshSwitch, List.Mem freshSwitch writers ->
        oldSwitch != freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    have hmap := List.mem_map.mp hFresh
    let t := Exists.choose hmap
    have ht := Exists.choose_spec hmap
    have htData :=
      mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using ht.1)
    have houtside :=
      A.second_exploration_productive_writer_not_reusable
        hN B hbaseGrooves hpreGrooves
          htData.1 htData.2.1
    apply houtside
    have hwriterOld :
        rawWriterAt w (e, B.baseState) t = oldSwitch :=
      ht.2.trans hEq.symm
    rw [hwriterOld]
    exact hOld
  let switches := A.reusableSwitches ++ writers
  have hnd : switches.Nodup := by
    dsimp [switches]
    exact List.nodup_append.mpr
      (And.intro A.reusableSwitches_nodup
        (And.intro hwritersNodup hdisjoint))
  have hlt : forall C, List.Mem C switches -> C < N := by
    intro C hC
    rcases List.mem_append.mp hC with hOld | hFresh
    case inl =>
      exact A.reusableSwitch_lt hN hOld
    case inr =>
      have hmap := List.mem_map.mp hFresh
      let t := Exists.choose hmap
      have ht := Exists.choose_spec hmap
      have htData :=
        mem_rawFirstWriterTimes_iff.mp (by
          simpa [times] using ht.1)
      have hwlt := rawProductiveAt_writer_lt hN htData.2.1
      rw [ht.2] at hwlt
      exact hwlt
  have hlength : switches.length = N := by
    dsimp [switches, writers]
    simp only [List.length_append, List.length_map]
    simpa [times] using hfull
  by_cases hmem : List.Mem k switches
  case pos =>
    rcases List.mem_append.mp hmem with hOld | hFresh
    case inl =>
      exact Or.inl hOld
    case inr =>
      have hmap := List.mem_map.mp hFresh
      let t := Exists.choose hmap
      have ht := Exists.choose_spec hmap
      apply Or.inr
      exact Exists.intro t
        (And.intro (by simpa [times] using ht.1) ht.2)
  case neg =>
    have hreserved : (k :: switches).Nodup := by
      rw [List.nodup_cons]
      exact And.intro hmem hnd
    have hreservedLt :
        forall C, List.Mem C (k :: switches) -> C < N := by
      intro C hC
      rcases List.mem_cons.mp hC with hEq | hrest
      case inl =>
        rw [hEq]
        exact hk
      case inr =>
        exact hlt C hrest
    have hbound :=
      nodup_nat_lt_length hreserved hreservedLt
    simp only [List.length_cons, hlength] at hbound
    omega

-/

/-- Under full coordinate charge, a coordinate omitted by the first
reflector's reusable support must be a productive first writer of the
second reflector. The existing reserved-coordinate inequality makes this
the exact contrapositive of having one coordinate left over. -/
private theorem mem_second_writer_of_full_charge_of_not_reusable
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (hfull :
      A.reusableSwitches.length +
        (rawFirstWriterTimes w N (e, B.baseState)
          B.exploration.length).length = N)
    (k : Nat) (hk : k < N)
    (habsentA : Not (List.Mem k A.reusableSwitches)) :
    List.Mem k (B.constructionFirstWriterSwitches N) := by
  by_cases hmem :
      List.Mem k (B.constructionFirstWriterSwitches N)
  case pos =>
    exact hmem
  case neg =>
    have hsave :=
      A.reusable_add_second_first_writers_add_reserved_le
        hN B hbaseGrooves hpreGrooves hk habsentA hmem
    omega

/-- The facing mouth coordinate of a flip reflector is deliberately absent
from its reusable support list. -/
private theorem flip_action_not_mem_reusable
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e) :
    Not (List.Mem R.actionSwitch
      (ManufacturedReflector.flip R).reusableSwitches) := by
  intro hmem
  change List.Mem R.actionSwitch
    ((R.runway ++ R.candy).map passageSwitch) at hmem
  have hmap := List.mem_map.mp hmem
  let passage := Exists.choose hmap
  have hp := Exists.choose_spec hmap
  rcases List.mem_append.mp hp.1 with hrunway | hcandy
  case inl =>
    exact (R.support_foreign R.runway (by simp)
      passage hrunway) hp.2
  case inr =>
    exact (R.support_foreign R.candy (by simp)
      passage hcandy) hp.2

/-- The omitted facing mouth is nevertheless one of the ambient N switches. -/
private theorem flip_action_lt
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (R : ManufacturedFlipReflector w g e) :
    R.actionSwitch < N := by
  have hlt :=
    (ManufacturedReflector.flip R).exploration_trace.switch_lt
      hN (R.mouth, R.firstArm) (by
        simp [ManufacturedReflector.exploration])
  simpa [passageSwitch,
    ManufacturedFlipReflector.actionSwitch] using hlt

/-- Therefore saturation forces the second construction to productively
first-write the omitted facing-mouth switch. -/
theorem ProductiveInitialProtectedPairSaturation.action_is_second_first_writer
    {w : Wiring} {N : Nat}
    (P : ProductiveInitialProtectedPairSaturation w N)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (R : ManufacturedFlipReflector w
      P.source.g P.source.e)
    (hkind : P.source.A = ManufacturedReflector.flip R) :
    Exists fun t =>
      And
        (List.Mem t
          (rawFirstWriterTimes w N
            (P.source.e, P.B.baseState)
            P.B.exploration.length))
        (rawWriterAt w (P.source.e, P.B.baseState) t =
          R.actionSwitch) := by
  have hA :
      PathGrooves P.source.A.toSupported.paths
        P.source.A.activatedState := by
    rw [P.source.activated.symm]
    exact P.source.grooves
  have hbaseGrooves :
      PathGrooves P.source.A.toSupported.paths P.B.baseState := by
    rw [P.baseB]
    exact hA
  have hfull := P.coordinate_charge_eq hN R hkind
  have habsentA :
      Not (List.Mem R.actionSwitch
        P.source.A.reusableSwitches) := by
    intro hmem
    exact flip_action_not_mem_reusable R
      (by simpa only [hkind] using hmem)
  have hmem :=
    mem_second_writer_of_full_charge_of_not_reusable
      hN P.source.A P.B hbaseGrooves P.preGrooves
        hfull R.actionSwitch (flip_action_lt hN R) habsentA
  unfold ManufacturedReflector.constructionFirstWriterSwitches at hmem
  have hmap := List.mem_map.mp hmem
  let t := Exists.choose hmap
  have ht := Exists.choose_spec hmap
  exact Exists.intro t (And.intro ht.1 ht.2)

/-- The initially written switch is likewise either on the first reusable
support or is productively first-written by the second construction. -/
theorem ProductiveInitialProtectedPairSaturation.initial_switch_named
    {w : Wiring} {N : Nat}
    (P : ProductiveInitialProtectedPairSaturation w N)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (R : ManufacturedFlipReflector w
      P.source.g P.source.e)
    (hkind : P.source.A = ManufacturedReflector.flip R) :
    Or (List.Mem P.source.k0 P.source.A.reusableSwitches)
      (Exists fun t =>
        And
          (List.Mem t
            (rawFirstWriterTimes w N
              (P.source.e, P.B.baseState)
              P.B.exploration.length))
          (rawWriterAt w (P.source.e, P.B.baseState) t =
            P.source.k0)) := by
  classical
  have hA :
      PathGrooves P.source.A.toSupported.paths
        P.source.A.activatedState := by
    rw [P.source.activated.symm]
    exact P.source.grooves
  have hbaseGrooves :
      PathGrooves P.source.A.toSupported.paths P.B.baseState := by
    rw [P.baseB]
    exact hA
  by_cases hOld :
      List.Mem P.source.k0 P.source.A.reusableSwitches
  case pos =>
    exact Or.inl hOld
  case neg =>
    apply Or.inr
    have hmem :=
      mem_second_writer_of_full_charge_of_not_reusable
        hN P.source.A P.B hbaseGrooves P.preGrooves
          (P.coordinate_charge_eq hN R hkind)
          P.source.k0 P.source.switch_lt hOld
    unfold ManufacturedReflector.constructionFirstWriterSwitches at hmem
    have hmap := List.mem_map.mp hmem
    let t := Exists.choose hmap
    have ht := Exists.choose_spec hmap
    exact Exists.intro t (And.intro ht.1 ht.2)

/-- The productive initial-boundary history saturation is impossible.

The residual already carries a known incoming edge, an N+6 family of
distinct states on the shifted run from its known-edge start, and liveness
of every sampled time. The coefficient-one known-edge theorem bounds that
same family by N+5. -/
theorem productiveInitialBoundaryHistorySaturation_false
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N)) :
    ProductiveInitialBoundaryHistorySaturation w N -> False := by
  intro S
  have htailNodup :
      (S.times.map
        (restrictedTonguesAt w N (S.g, S.base))).Nodup :=
    (List.nodup_cons.mp S.distinct).2
  have hbound :=
    known_edge_all_run_distinct_le_N_add_five
      hN S.entry S.times S.live htailNodup
  have hsaturated := S.saturated
  omega

end GeneralN
