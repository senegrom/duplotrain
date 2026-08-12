import BoundaryNAddFourSaturation
import BoundaryAbsentSecondWriter
import PartialJourneyDichotomy
import PartialSecondRunNAddFour
import ProtectedPairNAddFour
import ProductiveBoundarySupportContact
import BoundaryDoubleDuplicate
import BoundaryResidualNovelty
import BoundaryAbsentProtectedPair
import BoundaryCanonicalOriginalOverlap
import BoundaryResidualCharge
import KnownEdgeNAddFourComplete

/-!
# Exact completion frontier for the productive `N+4` boundary

This module preserves the provenance of the first-journey saving.  The
unchanged-entry constructor carries its concrete reduced history; the absent
constructor carries the reserved switch coordinate.  No finite-instance
argument is used.
-/

namespace GeneralN

private theorem completion_nodup_map_filter
    {α : Type} [BEq α] [LawfulBEq α]
    {f : Nat → α} (p : Nat → Bool) :
    ∀ {xs : List Nat},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
            apply hnd.1
            exact List.mem_map.mpr
              ⟨y, (List.mem_filter.mp hy).1, hfy⟩
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

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
    times.length + 1 ≤ history.length + budget := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let secondTravel := B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let localTimes :=
    (times.filter (fun k => decide (totalTravel < k))).map
      (fun k => k - totalTravel)
  have hreachA : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hApaths
  have hreachB : stepN w secondTravel (e, A.activatedState) =
      some (g, B.activatedState) := by
    have h := B.manufacturing_journey_reaches_activated hBpaths
    simpa [secondTravel, hbase] using h
  have hreachTotal : stepN w totalTravel (g, A.baseState) =
      some (g, B.activatedState) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachB
  have hprefixCover : ∀ d, d ≤ totalTravel →
      restrictedTonguesAt w N (g, A.baseState) d ∈ history := by
    intro d hd
    by_cases hfirst : d ≤ firstTravel
    · apply hhistory
      left
      exact A.manufacturing_journey_mem_sharpHistory
        hApaths (by simpa [firstTravel] using hfirst)
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLe : q ≤ secondTravel := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hliveQ := stepN_prefix_some hqLe hreachB
      have hshift := tonguesAt_add_of_reaches hreachA hliveQ
      have hmRaw := B.manufacturing_journey_mem_sharpHistory
        (N := N) hBpaths (j := q)
          (by simpa [secondTravel] using hqLe)
      have hm : restrictedTonguesAt w N
          (e, A.activatedState) q ∈
            B.sharpConstructionHistory N := by
        simpa [hbase] using hmRaw
      have heq : restrictedTonguesAt w N (g, A.baseState) d =
          restrictedTonguesAt w N (e, A.activatedState) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      exact hhistory _ (Or.inr hm)
  have hlocalLive : ∀ d ∈ localTimes,
      (stepN w d (g, B.activatedState)).isSome := by
    intro d hd
    obtain ⟨k, hkFiltered, rfl⟩ := List.mem_map.mp hd
    have hk := (List.mem_filter.mp hkFiltered).1
    have hkGt : totalTravel < k := by
      simpa using (List.mem_filter.mp hkFiltered).2
    have hkEq : k = totalTravel + (k - totalTravel) := by omega
    have hkLive := hlive k hk
    rw [hkEq, stepN_add, hreachTotal] at hkLive
    exact hkLive
  have hlocalVector : localTimes.map
      (restrictedTonguesAt w N (g, B.activatedState)) =
      (times.filter (fun k => decide (totalTravel < k))).map
        (restrictedTonguesAt w N (g, A.baseState)) := by
    dsimp [localTimes]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkGt : totalTravel < k := by
      simpa using (List.mem_filter.mp hk).2
    have hkEq : k = totalTravel + (k - totalTravel) := by omega
    have hkLive := hlive k hkTimes
    cases htailRun : stepN w (k - totalTravel)
        (g, B.activatedState) with
    | none =>
        have hglobalNone : stepN w k (g, A.baseState) = none := by
          rw [hkEq, stepN_add, hreachTotal]
          simp [htailRun]
        rw [hglobalNone] at hkLive
        simp at hkLive
    | some finish =>
        have hshift := tonguesAt_add_of_reaches
          hreachTotal ⟨finish, htailRun⟩
        unfold restrictedTonguesAt
        rw [hkEq]
        simpa using congrArg (VectorCount.restrict N) hshift.symm
  have htailNodup := (List.nodup_cons.mp hnd).2
  have hfilteredNodup :
      ((times.filter (fun k => decide (totalTravel < k))).map
        (restrictedTonguesAt w N (g, A.baseState))).Nodup :=
    completion_nodup_map_filter _ htailNodup
  have hlocalNodup : (localTimes.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup := by
    rw [hlocalVector]
    exact hfilteredNodup
  have hlocalCover := htail localTimes hlocalLive hlocalNodup
  obtain ⟨fresh, hfresh, hlocalMem⟩ := hlocalCover
  have hglobalCover : NoveltyCoverOn w N (g, A.baseState)
      times history budget := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hprefix : k ≤ totalTravel
    · exact List.mem_append_left _ (hprefixCover k hprefix)
    · have hkGt : totalTravel < k := by omega
      let d := k - totalTravel
      have hkEq : k = totalTravel + d := by
        dsimp [d]
        omega
      have hkFiltered : k ∈
          times.filter (fun t => decide (totalTravel < t)) := by
        apply List.mem_filter.mpr
        exact ⟨hk, by simp [hkGt]⟩
      have hdMem : d ∈ localTimes := by
        dsimp [localTimes]
        exact List.mem_map.mpr ⟨k, hkFiltered, rfl⟩
      obtain ⟨finish, hfinish⟩ :=
        Option.isSome_iff_exists.mp (hlocalLive d hdMem)
      have hshift := tonguesAt_add_of_reaches
        hreachTotal ⟨finish, hfinish⟩
      have hvector : restrictedTonguesAt w N (g, A.baseState) k =
          restrictedTonguesAt w N (g, B.activatedState) d := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [hvector]
      exact hlocalMem d hdMem
  exact novelty_cover_count_with_historical_extra
    extra hglobalCover hextra hnd

/-- The dead second probe is strictly too small to support a saturated
productive boundary.  This branch does not spend either boundary saving. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_dead_second_probe
    {w : Wiring} {N : Nat}
    (R : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hdead : stepN w (N + 1)
      (R.source.e, R.A.activatedState) = none) : False := by
  have hA : PathGrooves R.A.toSupported.paths R.A.activatedState := by
    rw [← R.activated]
    exact R.grooves
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
  have hA : PathGrooves R.A.toSupported.paths R.A.activatedState := by
    rw [← R.activated]
    exact R.grooves
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


/-- A noncanonical unchanged occurrence supplies two distinct duplicate
positions.  The resulting double-reduced history contains the arbitrary
boundary vector and both manufacturing histories.  If the old action is a
second first-writer, the protected tail costs one vector over an N+3
history; otherwise the omitted action coordinate gives N+2 and the generic
tail costs two.  Either accounting contradicts saturation. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_noncanonical_stay_protected_pair_complete
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hstay : O.next = O.middle)
    (hdifferent : Not (O.before.length = R.runway.length))
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2) :
    False := by
  let A : ManufacturedReflector w S.source.g S.source.e :=
    ManufacturedReflector.flip R
  let history := O.doubleReducedTwoHistory B N S.source.original
  have hApathsS : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [<- S.activated]
    exact S.grooves
  have hApaths : PathGrooves A.toSupported.paths A.activatedState := by
    simpa [A, hAeq] using hApathsS
  have hAbase : A.baseState = S.source.base := by
    simpa [A, hAeq] using S.reflector_base
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have hhistoryData :=
    O.mem_doubleReducedTwoHistory (N := N) B S.source.original
      hstay hdifferent hbase
  have hextra := hhistoryData.1
  have hhistory := hhistoryData.2
  have hlive : forall k, List.Mem k S.source.times ->
      (stepN w k (S.source.g, A.baseState)).isSome := by
    intro k hk
    simpa [hAbase] using S.source.live k hk
  have hnd : (VectorCount.restrict N S.source.original ::
      S.source.times.map
        (restrictedTonguesAt w N
          (S.source.g, A.baseState))).Nodup := by
    simpa [hAbase] using S.source.distinct
  by_cases haction :
      List.Mem R.actionSwitch (B.constructionFirstWriterSwitches N)
  case pos =>
    unfold ManufacturedReflector.constructionFirstWriterSwitches at haction
    let t := Classical.choose (List.mem_map.mp haction)
    have htData := Classical.choose_spec (List.mem_map.mp haction)
    have ht : List.Mem t
        (rawFirstWriterTimes w N (S.source.e, B.baseState)
          B.exploration.length) := htData.1
    have hwriter : rawWriterAt w (S.source.e, B.baseState) t =
        R.actionSwitch := htData.2
    have htail : forall tailTimes : List Nat,
        (forall k, List.Mem k tailTimes ->
          (stepN w k (S.source.g, B.activatedState)).isSome) ->
        (tailTimes.map
          (restrictedTonguesAt w N
            (S.source.g, B.activatedState))).Nodup ->
        NoveltyCoverOn w N (S.source.g, B.activatedState)
          tailTimes history 1 := by
      intro tailTimes htailLive htailNodup
      exact R.protected_repair_one_novelty_over_history_of_action_writer
        hN B hAatBase hBpaths hpre history hhistory
          ht hwriter tailTimes htailLive htailNodup
    have hcount :=
      A.two_journeys_then_shared_history_novelty_count_with_extra
        B hbase hApaths hBpaths history hhistory 1 htail
          (VectorCount.restrict N S.source.original) hextra
            S.source.times hlive hnd
    have hlength := O.doubleReducedTwoHistory_length_le_N_add_three
      hN B S.source.original hdifferent hbase hAatBase hpre
    have hsaturated := S.source.saturated
    dsimp [history] at hcount hlength
    omega
  case neg =>
    have htail : forall tailTimes : List Nat,
        (forall k, List.Mem k tailTimes ->
          (stepN w k (S.source.g, B.activatedState)).isSome) ->
        (tailTimes.map
          (restrictedTonguesAt w N
            (S.source.g, B.activatedState))).Nodup ->
        NoveltyCoverOn w N (S.source.g, B.activatedState)
          tailTimes history 2 := by
      intro tailTimes htailLive htailNodup
      exact A.protected_repair_two_novelty_over_history
        hN B hAatBase hBpaths hpre history hhistory
          tailTimes htailLive htailNodup
    have hcount :=
      A.two_journeys_then_shared_history_novelty_count_with_extra
        B hbase hApaths hBpaths history hhistory 2 htail
          (VectorCount.restrict N S.source.original) hextra
            S.source.times hlive hnd
    have hlength :=
      O.doubleReducedTwoHistory_length_le_N_add_two_of_action_absent
        hN B S.source.original hdifferent hbase hAatBase hpre haction
    have hsaturated := S.source.saturated
    dsimp [history] at hcount hlength
    omega
/-- If the initial boundary coordinate is absent from the first flip
exploration and from the second first-writer list, the protected pair cannot
be saturated.  When the flip action is a second first-writer, k0 is one
reserved coordinate and the tail has one novelty.  Otherwise k0 and the
distinct action mouth are two reserved coordinates and the generic tail has
two novelties. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_absent_first_flip_protected_pair_complete
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (hfirstAbsent : Not (Membership.mem
      ((ManufacturedReflector.flip R).exploration.map passageSwitch)
        S.source.k0))
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (hk0AbsentB : Not (Membership.mem
      (B.constructionFirstWriterSwitches N) S.source.k0)) :
    False := by
  let A : ManufacturedReflector w S.source.g S.source.e :=
    ManufacturedReflector.flip R
  let core := A.preservedTwoHistoryCore B N
  let history := VectorCount.restrict N S.source.original :: core
  have hApathsS : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [<- S.activated]
    exact S.grooves
  have hApaths : PathGrooves A.toSupported.paths A.activatedState := by
    simpa [A, hAeq] using hApathsS
  have hAbase : A.baseState = S.source.base := by
    simpa [A, hAeq] using S.reflector_base
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have hk0NotReusable : Not
      (Membership.mem A.reusableSwitches S.source.k0) := by
    intro hk0
    let path := Classical.choose (A.mem_reusableSwitches hk0)
    have pathData :=
      Classical.choose_spec (A.mem_reusableSwitches hk0)
    have hpath := pathData.1
    let passage := Classical.choose pathData.2
    have passageData := Classical.choose_spec pathData.2
    have hpassage := passageData.1
    have hswitch := passageData.2
    apply hfirstAbsent
    have hm := A.support_switch_mem_exploration hpath hpassage
    rw [hswitch] at hm
    simpa [A] using hm
  have hk0NeAction : Not (S.source.k0 = R.actionSwitch) := by
    intro heq
    apply hfirstAbsent
    rw [heq]
    exact R.actionSwitch_mem_exploration
  have hhistory : forall x,
      Or (Membership.mem (A.sharpConstructionHistory N) x)
        (Membership.mem (B.sharpConstructionHistory N) x) ->
      Membership.mem history x := by
    intro x hx
    apply List.mem_cons_of_mem
    exact A.mem_preservedTwoHistoryCore B hx
  have hextra : Membership.mem history
      (VectorCount.restrict N S.source.original) := by
    dsimp [history]
    exact List.mem_cons_self
  have hlive : forall k, Membership.mem S.source.times k ->
      (stepN w k (S.source.g, A.baseState)).isSome := by
    intro k hk
    simpa [hAbase] using S.source.live k hk
  have hnd : (VectorCount.restrict N S.source.original ::
      S.source.times.map
        (restrictedTonguesAt w N
          (S.source.g, A.baseState))).Nodup := by
    simpa [hAbase] using S.source.distinct
  by_cases haction : Membership.mem
      (B.constructionFirstWriterSwitches N) R.actionSwitch
  case pos =>
    unfold ManufacturedReflector.constructionFirstWriterSwitches at haction
    let t := Classical.choose (List.mem_map.mp haction)
    have htData := Classical.choose_spec (List.mem_map.mp haction)
    have ht : Membership.mem
        (rawFirstWriterTimes w N (S.source.e, B.baseState)
          B.exploration.length) t := htData.1
    have hwriter : rawWriterAt w (S.source.e, B.baseState) t =
        R.actionSwitch := htData.2
    have htail : forall tailTimes : List Nat,
        (forall k, Membership.mem tailTimes k ->
          (stepN w k (S.source.g, B.activatedState)).isSome) ->
        (tailTimes.map
          (restrictedTonguesAt w N
            (S.source.g, B.activatedState))).Nodup ->
        NoveltyCoverOn w N (S.source.g, B.activatedState)
          tailTimes history 1 := by
      intro tailTimes htailLive htailNodup
      exact R.protected_repair_one_novelty_over_history_of_action_writer
        hN B hAatBase hBpaths hpre history hhistory
          ht hwriter tailTimes htailLive htailNodup
    have hcount :=
      A.two_journeys_then_shared_history_novelty_count_with_extra
        B hbase hApaths hBpaths history hhistory 1 htail
          (VectorCount.restrict N S.source.original) hextra
            S.source.times hlive hnd
    have hcoreLength :=
      A.preservedTwoHistoryCore_length_le_N_add_two_of_reserved
        hN B hbase hAatBase hpre S.source.switch_lt
          hk0NotReusable hk0AbsentB
    have hsaturated := S.source.saturated
    dsimp [history, core] at hcount
    omega
  case neg =>
    have htail : forall tailTimes : List Nat,
        (forall k, Membership.mem tailTimes k ->
          (stepN w k (S.source.g, B.activatedState)).isSome) ->
        (tailTimes.map
          (restrictedTonguesAt w N
            (S.source.g, B.activatedState))).Nodup ->
        NoveltyCoverOn w N (S.source.g, B.activatedState)
          tailTimes history 2 := by
      intro tailTimes htailLive htailNodup
      exact A.protected_repair_two_novelty_over_history
        hN B hAatBase hBpaths hpre history hhistory
          tailTimes htailLive htailNodup
    have hcount :=
      A.two_journeys_then_shared_history_novelty_count_with_extra
        B hbase hApaths hBpaths history hhistory 2 htail
          (VectorCount.restrict N S.source.original) hextra
            S.source.times hlive hnd
    have hcoreLength :=
      A.preservedTwoHistoryCore_length_le_N_add_one_of_two_reserved
        hN B hbase hAatBase hpre
          S.source.switch_lt (R.action_lt hN) hk0NeAction
          hk0NotReusable hk0AbsentB R.action_not_mem_reusable haction
    have hsaturated := S.source.saturated
    dsimp [history, core] at hcount
    omega

/-- Canonicality has a raw geometric consequence stronger than the counting
saving: the first flip mouth is the source entry, its switch-simple runway is
empty, and the source edge is a literal self-link. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_geometry_complete
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    R.mouth = S.source.e /\
      R.runway = [] /\
      S.source.g = S.source.e /\
      w.link S.source.e = some S.source.e := by
  have hk0 : S.source.k0 = R.actionSwitch :=
    O.switch_eq_action_of_before_length_eq_runway hcanonical
  have hmouth : R.mouth = S.source.e := by
    have hstem := S.source.stem
    have hmouthStem := R.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch at hk0
    omega
  have hrunway : R.runway = [] := by
    cases hroute : R.runway with
    | nil =>
        rfl
    | cons passage rest =>
        cases passage
        rename_i p x
        have htrace := R.runwayTrace
        rw [hroute] at htrace
        have hsimple : SwitchSimple ((p, x) :: rest) := by
          have hs := (ManufacturedReflector.flip R).runway_simple
          change SwitchSimple R.runway at hs
          rwa [hroute] at hs
        have hfirst : p = S.source.g :=
          htrace.head_arrive.1.symm
        have hlast :
            w.link (lastPassageExit x rest) = some R.mouth :=
          htrace.last_link
        have hback :
            w.link R.mouth = some (lastPassageExit x rest) :=
          w.symm _ _ hlast
        have hentry : w.link R.mouth = some S.source.g := by
          simpa [hmouth] using S.source.entry
        have hfinal : lastPassageExit x rest = S.source.g := by
          rw [hentry] at hback
          exact (Option.some.inj hback).symm
        exact False.elim
          (htrace.simple_last_exit_ne_first_entry hsimple
            (hfinal.trans hfirst.symm))
  have hsound := R.runwayTrace.sound
  rw [hrunway] at hsound
  have hconfig :
      (S.source.g, R.base) = (R.mouth, R.mouthState) := by
    simpa [stepN] using hsound
  have hge : S.source.g = S.source.e :=
    (congrArg Prod.fst hconfig).trans hmouth
  have hself : w.link S.source.e = some S.source.e := by
    simpa [hge] using S.source.entry
  exact And.intro hmouth
    (And.intro hrunway (And.intro hge hself))
/-- At the canonical unchanged occurrence, the first reflector's runway is
the stable simple lead needed by the present-second-writer closure.  Indeed
canonicality identifies the initially written switch with the flip mouth,
while the raw boundary hypothesis identifies that mouth with `source.e`. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_canonical_present_writer_protected_pair
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length)
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (hpresent : Membership.mem
      (B.constructionFirstWriterSwitches N) S.source.k0) :
    False := by
  have hApathsS : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [<- S.activated]
    exact S.grooves
  have hApaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState := by
    simpa [hAeq] using hApathsS
  have hAbase : (ManufacturedReflector.flip R).baseState =
      S.source.base := by
    simpa [hAeq] using S.reflector_base
  have hAatBase : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have hk0 : S.source.k0 = R.actionSwitch :=
    O.switch_eq_action_of_before_length_eq_runway hcanonical
  have hmouth : R.mouth = S.source.e := by
    have hstem := S.source.stem
    have hm := R.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch at hk0
    omega
  have hleadRaw := R.runway_trace B.baseState
    (pathGrooves_pair.mp hAatBase).1
  have hlead : PhysicalTrace w
      (S.source.g, B.baseState) R.runway
      (S.source.e, B.baseState) := by
    simpa [hmouth] using hleadRaw
  have hleadSimple : SwitchSimple R.runway := by
    simpa [ManufacturedReflector.runway] using
      (ManufacturedReflector.flip R).runway_simple
  have hbound := productive_initial_boundary_N_add_four_of_present_writer
    hN S.source.entry S.source.stem S.source.switch_lt
      S.source.original S.source.base S.source.base_flip
      (ManufacturedReflector.flip R) hAbase B hbase
      hApaths hBpaths hpre hpresent R.runway hlead hleadSimple
      S.source.times S.source.live S.source.distinct
  have hsaturated := S.source.saturated
  omega

/-- The committed absent-boundary theorem eliminates both possible kinds of
first reflector at once whenever the reserved initial coordinate is also
absent from the second construction's productive first writers. -/
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
      S.A.activatedState := by
    rw [<- S.activated]
    exact S.grooves
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


/-! ## A zero-cost boundary replacement for a first stay reflector -/

/-- Remove the post-time of the unchanged initial-switch occurrence and
replace the stay reflector's separately appended activated endpoint by the
arbitrary pre-passage vector.  The activated endpoint is still represented
inside the retained time range. -/
def InitialEntryWriterOccurrence.stayBoundaryCore
    {w : Wiring} {g e k0 : Nat}
    {R : ManufacturedStayReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.stay R))
    (N : Nat) (original : Tongues) : List (List Bool) :=
  VectorCount.restrict N original ::
    ((List.range
      ((ManufacturedReflector.stay R).exploration.length + 1)).erase
        (O.before.length + 1)).map
      (restrictedTonguesAt w N
        (g, (ManufacturedReflector.stay R).baseState))

theorem InitialEntryWriterOccurrence.activated_mem_stayBoundaryCore
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedStayReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.stay R))
    (original : Tongues)
    (hstay : O.next = O.middle) :
    List.Mem
      (VectorCount.restrict N
        (ManufacturedReflector.stay R).activatedState)
      (O.stayBoundaryCore N original) := by
  let A : ManufacturedReflector w g e := ManufacturedReflector.stay R
  let f := restrictedTonguesAt w N (g, A.baseState)
  have hendVector :
      f A.exploration.length =
        VectorCount.restrict N A.activatedState := by
    simp [f, restrictedTonguesAt, tonguesAt,
      A.exploration_trace.sound, A,
      ManufacturedReflector.preReturn,
      ManufacturedReflector.activatedState]
  have hpostRange : O.before.length + 1 <
      A.exploration.length + 1 := by
    rw [O.split]
    simp
  have hbeforeRange : O.before.length <
      A.exploration.length + 1 := by omega
  have hduplicate :
      f O.before.length = f (O.before.length + 1) := by
    exact entry_writer_unchanged_gives_consecutive_duplicate
      (N := N) A O hstay
  unfold InitialEntryWriterOccurrence.stayBoundaryCore
  change List.Mem (VectorCount.restrict N A.activatedState)
    (VectorCount.restrict N original ::
      ((List.range (A.exploration.length + 1)).erase
        (O.before.length + 1)).map f)
  apply List.mem_cons_of_mem
  apply List.mem_map.mpr
  by_cases hend : A.exploration.length = O.before.length + 1
  case pos =>
    refine Exists.intro O.before.length ?_
    constructor
    case left =>
      apply (List.mem_erase_of_ne (by omega)).mpr
      exact List.mem_range.mpr hbeforeRange
    case right =>
      calc
        f O.before.length = f (O.before.length + 1) := hduplicate
        _ = f A.exploration.length := by rw [hend]
        _ = VectorCount.restrict N A.activatedState := hendVector
  case neg =>
    refine Exists.intro A.exploration.length ?_
    constructor
    case left =>
      apply (List.mem_erase_of_ne hend).mpr
      exact List.mem_range.mpr (by omega)
    case right => exact hendVector

theorem InitialEntryWriterOccurrence.stayBoundaryCore_length
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedStayReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.stay R))
    (original : Tongues) :
    (O.stayBoundaryCore N original).length =
      (ManufacturedReflector.stay R).exploration.length + 1 := by
  have hpost : List.Mem (O.before.length + 1)
      (List.range
        ((ManufacturedReflector.stay R).exploration.length + 1)) := by
    apply List.mem_range.mpr
    rw [O.split]
    simp
  unfold InitialEntryWriterOccurrence.stayBoundaryCore
  rw [List.length_cons, List.length_map,
    List.length_erase_of_mem hpost, List.length_range]
  omega

theorem InitialEntryWriterOccurrence.sharp_mem_stayBoundaryCore
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedStayReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.stay R))
    (original : Tongues)
    (hstay : O.next = O.middle) :
    forall v,
      List.Mem v
        ((ManufacturedReflector.stay R).sharpConstructionHistory N) ->
      List.Mem v (O.stayBoundaryCore N original) := by
  intro v hv
  have hm := O.sharp_mem_reduced_of_stay original hstay v hv
  unfold InitialEntryWriterOccurrence.reducedBoundaryHistory at hm
  rcases List.mem_cons.mp hm with horiginal | htail
  case inl =>
    unfold InitialEntryWriterOccurrence.stayBoundaryCore
    exact List.mem_cons.mpr (Or.inl horiginal)
  case inr =>
    rcases List.mem_append.mp htail with htimes | hactivated
    case inl =>
      unfold InitialEntryWriterOccurrence.stayBoundaryCore
      exact List.mem_cons.mpr (Or.inr htimes)
    case inr =>
      have hvActivated := List.mem_singleton.mp hactivated
      subst v
      exact O.activated_mem_stayBoundaryCore original hstay

noncomputable def InitialEntryWriterOccurrence.stayBoundaryTwoHistory
    {w : Wiring} {g e k0 : Nat}
    {R : ManufacturedStayReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.stay R))
    (B : ManufacturedReflector w e g)
    (N : Nat) (original : Tongues) : List (List Bool) :=
  O.stayBoundaryCore N original ++
    (B.writerConstructionHistory N).erase
      (VectorCount.restrict N
        (ManufacturedReflector.stay R).activatedState)

theorem InitialEntryWriterOccurrence.mem_stayBoundaryTwoHistory
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedStayReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.stay R))
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hstay : O.next = O.middle) :
    List.Mem (VectorCount.restrict N original)
        (O.stayBoundaryTwoHistory B N original) /\
      (forall x,
        List.Mem x
            ((ManufacturedReflector.stay R).sharpConstructionHistory N) \/
          List.Mem x (B.sharpConstructionHistory N) ->
        List.Mem x (O.stayBoundaryTwoHistory B N original)) := by
  constructor
  case left =>
    apply List.mem_append_left
    unfold InitialEntryWriterOccurrence.stayBoundaryCore
    exact List.mem_cons_self
  case right =>
    intro x hx
    rcases hx with hA | hB
    case inl =>
      apply List.mem_append_left
      exact O.sharp_mem_stayBoundaryCore original hstay x hA
    case inr =>
      have hwriter := B.mem_writerConstructionHistory_of_mem_sharp hB
      by_cases hboundary :
          x = VectorCount.restrict N
            (ManufacturedReflector.stay R).activatedState
      case pos =>
        subst x
        apply List.mem_append_left
        exact O.activated_mem_stayBoundaryCore original hstay
      case neg =>
        apply List.mem_append_right
        exact (List.mem_erase_of_ne hboundary).mpr hwriter

theorem InitialEntryWriterOccurrence.stayBoundaryTwoHistory_length_le_N_add_two
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {R : ManufacturedStayReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.stay R))
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hbase : B.baseState =
      (ManufacturedReflector.stay R).activatedState)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.preReturn.2) :
    (O.stayBoundaryTwoHistory B N original).length <= N + 2 := by
  have hboundary :
      List.Mem
        (VectorCount.restrict N
          (ManufacturedReflector.stay R).activatedState)
        (B.writerConstructionHistory N) := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge :=
    (ManufacturedReflector.stay R).reusable_add_second_first_writers_le
      hN B hbaseGrooves hpreGrooves
  have hexploration :
      (ManufacturedReflector.stay R).exploration.length =
        (ManufacturedReflector.stay R).reusableSwitches.length := by
    simp [ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches]
  unfold InitialEntryWriterOccurrence.stayBoundaryTwoHistory
  rw [List.length_append, List.length_erase_of_mem hboundary,
    O.stayBoundaryCore_length original,
    B.writerConstructionHistory_length]
  omega

theorem ProductiveBoundaryNAddFourSavingResidual.false_of_unchanged_stay_protected_pair
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedStayReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.stay R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.stay R))
    (hstay : O.next = O.middle)
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hbase : B.baseState =
      (ManufacturedReflector.stay R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.preReturn.2) :
    False := by
  let A : ManufacturedReflector w S.source.g S.source.e :=
    ManufacturedReflector.stay R
  let history := O.stayBoundaryTwoHistory B N S.source.original
  have hApathsS :
      PathGrooves S.A.toSupported.paths S.A.activatedState := by
    rw [<- S.activated]
    exact S.grooves
  have hApaths :
      PathGrooves A.toSupported.paths A.activatedState := by
    simpa [A, hAeq] using hApathsS
  have hAbase : A.baseState = S.source.base := by
    simpa [A, hAeq] using S.reflector_base
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have hhistoryData :=
    O.mem_stayBoundaryTwoHistory (N := N) B S.source.original hstay
  have hextra := hhistoryData.1
  have hhistory := hhistoryData.2
  have htail : forall tailTimes : List Nat,
      (forall k, List.Mem k tailTimes ->
        (stepN w k (S.source.g, B.activatedState)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N
          (S.source.g, B.activatedState))).Nodup ->
      NoveltyCoverOn w N (S.source.g, B.activatedState)
        tailTimes history 2 := by
    intro tailTimes htailLive htailNodup
    exact A.protected_repair_two_novelty_over_history
      hN B hAatBase hBpaths hpre history hhistory
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
      B hbase hApaths hBpaths history hhistory 2 htail
        (VectorCount.restrict N S.source.original) hextra
          S.source.times hlive hnd
  have hlength :=
    O.stayBoundaryTwoHistory_length_le_N_add_two
      hN B S.source.original hbase hAatBase hpre
  have hsaturated := S.source.saturated
  dsimp [history] at hcount hlength
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
      List.Mem x (ManufacturedReflector.stay R).sharpConstructionHistory N \/
        List.Mem x B.sharpConstructionHistory N -> List.Mem x history)
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
    simp [ManufacturedReflector.sharpConstructionHistory]
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
    obtain Exists.intro finalState hcompleteData := hcomplete
    obtain And.intro hrepair hfinalData := hcompleteData
    obtain And.intro hAfinal hBfinal := hfinalData
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
  have hApathsS : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [<- S.activated]
    exact S.grooves
  have hApaths : PathGrooves A.toSupported.paths A.activatedState := by
    simpa [A, hAeq] using hApathsS
  have hAbase : A.baseState = S.source.base := by
    simpa [A, hAeq] using S.reflector_base
  have hbaseA : B.baseState = A.activatedState := by
    simpa [A] using hbase
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbaseA]
    exact hApaths
  have hpreA : PathGrooves A.toSupported.paths B.preReturn.2 := by
    simpa [A] using hpre
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
  omega

/-- The exact physical obstructions still left after the committed N+4
closures.  Each constructor stores raw trace data rather than a black-box
counting assumption. -/
inductive ProductiveBoundaryNAddFourExactResidual
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N) : Type where
  | secondCycleDamage
      (C : PartialSecondCycleOutcome w
        (S.source.e, S.A.activatedState) N)
      (damage : Not
        (PathGrooves S.A.toSupported.paths C.atRepeat.2))
  | oppositeReflectorDamage
      (P : PartialSecondReflectorCompletion S.A N)
      (damage : Not
        (PathGrooves S.A.toSupported.paths
          P.reflector.preReturn.2))
  | absentPresentWriter
      (R : ManufacturedFlipReflector w S.source.g S.source.e)
      (kind : S.A = ManufacturedReflector.flip R)
      (absentA : Not (Membership.mem
        (S.A.exploration.map passageSwitch) S.source.k0))
      (P : PartialSecondReflectorCompletion S.A N)
      (supportGrooved : PathGrooves S.A.toSupported.paths
        P.reflector.preReturn.2)
      (present : Membership.mem
        (P.reflector.constructionFirstWriterSwitches N)
          S.source.k0)

/-- Complete dead/cycle/reflector assembly.  Death and a support-preserving
stable cycle are impossible.  The committed absent, noncanonical,
first-stay, and canonical closures leave exactly the three constructors
named above. -/
theorem ProductiveBoundaryNAddFourSavingResidual.reduces_to_exact_residual
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    Nonempty (ProductiveBoundaryNAddFourExactResidual S) := by
  cases hprobe :
      stepN w (N + 1) (S.source.e, S.A.activatedState) with
  | none =>
      exact (S.false_of_dead_second_probe hN hprobe).elim
  | some finish =>
      have hback : w.link S.source.g = some S.source.e :=
        w.symm _ _ S.source.entry
      rcases first_activated_trace_outcome_sharp_partial
          hN hprobe hback with hcycle | hreflector
      case inl =>
        let C := Classical.choice hcycle
        by_cases hprotected :
            PathGrooves S.A.toSupported.paths C.atRepeat.2
        case pos =>
          exact (S.false_of_preserved_second_cycle
            hN C hprotected).elim
        case neg =>
          exact Nonempty.intro
            (ProductiveBoundaryNAddFourExactResidual.secondCycleDamage
              C hprotected)
      case inr =>
        let B := Exists.choose hreflector
        have hstateData := Exists.choose_spec hreflector
        let state := Exists.choose hstateData
        have hdata := Exists.choose_spec hstateData
        have hBpathsRaw :
            PathGrooves B.toSupported.paths state :=
          hdata.2.1
        have hbase : B.baseState = S.A.activatedState :=
          hdata.2.2.1
        have hactivated : state = B.activatedState :=
          hdata.2.2.2.1
        have hBpaths :
            PathGrooves B.toSupported.paths B.activatedState := by
          rw [<- hactivated]
          exact hBpathsRaw
        let P : PartialSecondReflectorCompletion S.A N := {
          reflector := B
          state := state
          length_le := hdata.1
          paths := hBpathsRaw
          base := hbase
          activated := hactivated
          reaches := hdata.2.2.2.2.1
          preserves := hdata.2.2.2.2.2
        }
        by_cases hpre :
            PathGrooves S.A.toSupported.paths B.preReturn.2
        case neg =>
          exact Nonempty.intro
            (ProductiveBoundaryNAddFourExactResidual.oppositeReflectorDamage
              P (by simpa [P] using hpre))
        case pos =>
          rcases S.saving with habsent | hoccurrence
          case inl =>
            by_cases hpresent : Membership.mem
                (B.constructionFirstWriterSwitches N) S.source.k0
            case pos =>
              cases hkind : S.A with
              | stay R =>
                  exact (S.false_of_first_stay_protected_pair
                    hN R hkind B
                      (by simpa [hkind] using hbase)
                      hBpaths (by simpa [hkind] using hpre)).elim
              | flip R =>
                  exact Nonempty.intro
                    (ProductiveBoundaryNAddFourExactResidual.absentPresentWriter
                      R hkind habsent.1 P (by simpa [P] using hpre)
                        (by simpa [P] using hpresent))
            case neg =>
              exact (S.false_of_absent_protected_pair_of_second_writer_absent
                hN habsent.1 B hbase hBpaths hpre hpresent).elim
          case inr =>
            let O := Classical.choose hoccurrence
            have hOdata := Classical.choose_spec hoccurrence
            have hstay : O.next = O.middle := hOdata.1
            cases hkind : S.A with
            | stay R =>
                let Ostay : InitialEntryWriterOccurrence
                    w S.source.g S.source.e S.source.k0
                      (ManufacturedReflector.stay R) := {
                  before := O.before
                  after := O.after
                  p := O.p
                  x := O.x
                  nextPort := O.nextPort
                  middle := O.middle
                  next := O.next
                  split := by simpa [hkind] using O.split
                  switch_eq := O.switch_eq
                  before_trace := by
                    simpa [hkind] using O.before_trace
                  arrive_eq := O.arrive_eq
                  link_eq := O.link_eq
                  reach := by simpa [hkind] using O.reach
                  prefix_foreign := O.prefix_foreign
                  prefix_preserves := by
                    simpa [hkind] using O.prefix_preserves
                  state_case := O.state_case
                }
                have hstayStay : Ostay.next = Ostay.middle := by
                  exact hstay
                exact (S.false_of_unchanged_stay_protected_pair
                  hN R hkind Ostay hstayStay B
                    (by simpa [hkind] using hbase)
                    hBpaths (by simpa [hkind] using hpre)).elim
            | flip R =>
                let Oflip : InitialEntryWriterOccurrence
                    w S.source.g S.source.e S.source.k0
                      (ManufacturedReflector.flip R) := {
                  before := O.before
                  after := O.after
                  p := O.p
                  x := O.x
                  nextPort := O.nextPort
                  middle := O.middle
                  next := O.next
                  split := by simpa [hkind] using O.split
                  switch_eq := O.switch_eq
                  before_trace := by
                    simpa [hkind] using O.before_trace
                  arrive_eq := O.arrive_eq
                  link_eq := O.link_eq
                  reach := by simpa [hkind] using O.reach
                  prefix_foreign := O.prefix_foreign
                  prefix_preserves := by
                    simpa [hkind] using O.prefix_preserves
                  state_case := O.state_case
                }
                have hstayFlip : Oflip.next = Oflip.middle := by
                  exact hstay
                by_cases hcanonical :
                    Oflip.before.length = R.runway.length
                case pos =>
                  exact (S.false_of_canonical_unchanged
                    hN R hkind Oflip hstayFlip hcanonical).elim
                case neg =>
                  exact (S.false_of_noncanonical_unchanged_protected_pair
                    hN R hkind Oflip hstayFlip hcanonical B
                      (by simpa [hkind] using hbase)
                      hBpaths (by simpa [hkind] using hpre)).elim


/-- Exact general-`N` completion frontier over raw `Wiring`/`stepN`.

The productive boundary theorem is equivalent to eliminating the three
concrete residual constructors above.  The forward implication uses the
saturated source carried by every residual; the reverse implication uses
the unconditional known-incoming-edge `N+4` theorem and the complete
dead/cycle/reflector reduction. -/
theorem productiveInitialBoundaryNAddFour_iff_no_exact_residual
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    ProductiveInitialBoundaryNAddFour w N <->
      forall S : ProductiveBoundaryNAddFourSavingResidual w N,
        ProductiveBoundaryNAddFourExactResidual S -> False := by
  constructor
  case mp =>
    intro hboundary S _residual
    have hbound := hboundary S.source.entry S.source.stem
      S.source.switch_lt S.source.base_flip S.source.times
        S.source.live S.source.distinct
    have hsaturated := S.source.saturated
    omega
  case mpr =>
    intro hno
    unfold ProductiveInitialBoundaryNAddFour
    intro g e k0 original base hentry hstem hk0 hbase
      times hlive hnd
    rcases productive_initial_boundary_N_add_four_or_saving_saturation
        hN (knownIncomingEdgeNAddFour hN) hentry hstem hk0
          original base hbase times hlive hnd with hbound | hsaving
    case inl =>
      exact hbound
    case inr =>
      let S := Classical.choice hsaving
      exact (hno S
        (Classical.choice (S.reduces_to_exact_residual hN))).elim


end GeneralN
