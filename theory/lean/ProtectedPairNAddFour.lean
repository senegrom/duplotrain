import KnownEdgeNAddFourChangedClosed

/-!
# The protected-pair `N+4` bound

The two manufacturing journeys share one coordinate budget and one canonical
history. A stay reflector costs at most `N+2` historical vectors. For a flip
reflector, either its action coordinate is reserved, again giving `N+2`, or
its occurrence in the second construction recovers a historical Gray corner.
Starting the pair at the protected pre-return state covers the actual
continuation by four action corners. Two corners are historical, and an
action writer recovers a third: `(N+2)+2 = (N+3)+1 = N+4`.

No repair-route classification is needed; the actual boundary is reached by
one traversal of the already grooved second reflector.
-/

namespace GeneralN

section
variable {w : Wiring} {N g e : Nat}
include w N g e

/-- The historical corner recovered from the last action writer belongs
already to the second reflector's uncompressed construction history.  This
form lets boundary arguments use their own smaller two-journey history
instead of the canonical `preservedTwoHistoryCore`. -/
theorem ManufacturedFlipReflector.flipped_preReturn_mem_second_sharp_of_last
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch)
    (hlast : forall j, t < j -> j < B.exploration.length ->
      Not (RawProductiveAt w N (e, B.baseState) j)) :
    VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch) ∈
      B.sharpConstructionHistory N := by
  have htData := mem_rawFirstWriterTimes_iff.mp ht
  have hrecover := last_productive_recovers B.exploration_trace.sound
    htData.1 htData.2.1 hlast
  rw [hwriter] at hrecover
  rw [hrecover]
  exact List.mem_append_left _ (List.mem_map.mpr
    ⟨t, List.mem_range.mpr (by omega), rfl⟩)

section
variable (A : ManufacturedReflector w g e)
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
    NoveltyCoverOn w N (g, B.activatedState) tailTimes
      history budget)
  (times : List Nat)
  (hlive : ∀ k ∈ times,
    (stepN w k (g, A.baseState)).isSome)
include A B hbase hApaths hBpaths history hhistory budget htail times hlive

/-- Lift a novelty cover for the protected repair tail across the two
manufacturing journeys.  Every prefix vector is supplied by the shared
history; only the shifted tail spends the given novelty budget. -/
theorem ManufacturedReflector.two_journeys_then_shared_history_novelty_cover :
    NoveltyCoverOn w N (g, A.baseState) times history budget := by
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
      have hm := B.manufacturing_journey_mem_sharpHistory
        (N := N) hBpaths (j := q)
          (by simpa [secondTravel] using hqLe)
      rw [hdEq, restrictedTonguesAt_add_of_reaches hreachA
        (stepN_prefix_some hqLe hreachB)]
      exact hhistory _ (Or.inr (by simpa [hbase] using hm))
  apply (htail localTimes (by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    obtain ⟨hj, hlate⟩ := List.mem_filter.mp hj
    have hle : totalTravel ≤ j := by simp only [decide_eq_true_eq] at hlate; omega
    have hr := hlive j hj
    rwa [show j = totalTravel + (j - totalTravel) by omega,
      stepN_add, hreachTotal] at hr)).prepend
      hreachTotal hprefixCover hlive
  intro k hk hlate
  exact List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hk, by simp [hlate]⟩, rfl⟩

/-- Generic two-journey bookkeeping over an arbitrary shared history: the
counting form of the novelty cover above. -/
theorem ManufacturedReflector.two_journeys_then_shared_history_novelty_count
    (hnd : (times.map (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ history.length + budget :=
  noveltyCoverOn_distinct_count
    (A.two_journeys_then_shared_history_novelty_cover B hbase hApaths
      hBpaths history hhistory budget htail times hlive) hnd

end

theorem ManufacturedStayReflector.protectedHistory_length_le_N_add_two
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedStayReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = (ManufacturedReflector.stay R).activatedState)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.preReturn.2) :
    ((ManufacturedReflector.stay R).preservedTwoHistoryCore B N).length ≤
      N + 2 := by
  let A : ManufacturedReflector w g e := .stay R
  have hboundary : VectorCount.restrict N A.activatedState ∈
      B.writerConstructionHistory N := by
    dsimp [A]
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge := A.reusable_add_continuation_first_writers_le
    hN B.exploration_trace B.exploration_simple hbaseGrooves hpreGrooves
  have heq : A.exploration.length = A.reusableSwitches.length := by
    simp [A, ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches]
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length, B.writerConstructionHistory_length]
  omega

/-- Every continuation of a fully protected opposite-reflector pair has at
most two fresh vectors over any history which represents both construction
journeys.  Unlike the top-level counting theorem, this statement keeps the
history abstract so a productive-boundary proof can substitute a smaller
history containing its pre-passage vector. -/
theorem ManufacturedReflector.protected_repair_two_novelty_over_history
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (history : List (List Bool))
    (hhistory : forall x,
      x ∈ A.sharpConstructionHistory N \/
        x ∈ B.sharpConstructionHistory N -> x ∈ history)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, B.activatedState)).isSome) :
    NoveltyCoverOn w N (g, B.activatedState) times history 2 := by
  have hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history :=
    hhistory _ (Or.inr B.activated_mem_sharpHistory)
  have hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history :=
    hhistory _ (Or.inr B.preReturn_mem_sharpHistory)
  refine ⟨[VectorCount.restrict N (A.toSupported.action.apply B.preReturn.2),
    VectorCount.restrict N (A.toSupported.action.apply B.activatedState)], by simp, ?_⟩
  intro k hk
  have hp := A.preReturn_pair_corners B hB hpre (hlive k hk)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp <;>
    simp [restrictedTonguesAt, hp, hinitialHistorical, hpreHistorical]

/-- If the first flip reflector's action switch is a productive first writer
of the second construction, every protected repair continuation has only one
fresh vector over any history representing both construction journeys. -/
theorem ManufacturedFlipReflector.protected_repair_one_novelty_over_history_of_action_writer
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (history : List (List Bool))
    (hhistory : forall x,
      x ∈ (ManufacturedReflector.flip R).sharpConstructionHistory N \/
        x ∈ B.sharpConstructionHistory N -> x ∈ history)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, B.activatedState)).isSome) :
    NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
  have hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history :=
    hhistory _ (Or.inr B.activated_mem_sharpHistory)
  have hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history :=
    hhistory _ (Or.inr B.preReturn_mem_sharpHistory)
  have hlast := R.no_productive_after_action_writer
    B.exploration_trace B.exploration_simple hA hpre ht hwriter
  have hcorner : VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch) ∈ history :=
    hhistory _ (Or.inr (R.flipped_preReturn_mem_second_sharp_of_last B ht hwriter hlast))
  refine ⟨[VectorCount.restrict N (flipAt B.activatedState R.actionSwitch)], by simp, ?_⟩
  intro k hk
  have hp := (ManufacturedReflector.flip R).preReturn_pair_corners B hB hpre (hlive k hk)
  change tonguesAt w (g, B.activatedState) k ∈
    [B.preReturn.2, B.activatedState, flipAt B.preReturn.2 R.actionSwitch,
     flipAt B.activatedState R.actionSwitch] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp <;>
    simp [restrictedTonguesAt, hp, hinitialHistorical, hpreHistorical, hcorner]

/-- The protected pair needs only a coordinate-usage split, not a writer-order
split. If the old flip action is absent from the second writer list, reserve
that coordinate and pay `(N+2)+2`. If present, its last-write history recovers
one tail corner and we pay `(N+3)+1`. A stay reflector always uses `(N+2)+2`.
The same canonical history is used in every case; no second erasure is needed. -/
theorem ManufacturedReflector.preReturn_grooved_protected_pair_all_run_distinct_le_N_add_four
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 4 := by
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  let history := A.preservedTwoHistoryCore B N
  have hhistory : ∀ x, x ∈ A.sharpConstructionHistory N ∨
      x ∈ B.sharpConstructionHistory N → x ∈ history := by
    intro x hx
    show x ∈ A.preservedTwoHistoryCore B N
    grind [ManufacturedReflector.mem_sharpHistoryCore_of_mem,
      ManufacturedReflector.mem_writerConstructionHistory_of_mem_sharp,
      ManufacturedReflector.preservedTwoHistoryCore,
      ManufacturedReflector.sharpConstructionHistory]
  have htwo : history.length ≤ N + 2 → times.length ≤ N + 4 := by
    intro hlen
    have hcount := A.two_journeys_then_shared_history_novelty_count
      B hbase hApaths hBpaths history hhistory 2
      (A.protected_repair_two_novelty_over_history B hBpaths hpre history hhistory) times hlive hnd
    omega
  cases A with
  | stay R =>
      exact htwo (R.protectedHistory_length_le_N_add_two
        hN B hbase hAatBase hpre)
  | flip R =>
      by_cases haction : R.actionSwitch ∈ B.constructionFirstWriterSwitches N
      · have hlen := (ManufacturedReflector.flip R).preservedTwoHistoryCore_length_le_N_add_three
          hN B hbase hAatBase hpre
        obtain ⟨t, ht, hwriter⟩ := List.mem_map.mp haction
        have hcount := (ManufacturedReflector.flip R).two_journeys_then_shared_history_novelty_count
          B hbase hApaths hBpaths history hhistory 1
          (R.protected_repair_one_novelty_over_history_of_action_writer
            B hAatBase hBpaths hpre history hhistory ht hwriter)
          times hlive hnd
        change history.length ≤ N + 3 at hlen
        omega
      · exact htwo ((ManufacturedReflector.flip R).preservedTwoHistoryCore_length_le_N_add_two_of_reserved
          hN B hbase hAatBase hpre (R.action_lt hN)
          R.action_not_mem_reusable haction)

end

/-- **Unconditional known-edge protected-pair law, exact raw `N+4`.**
Broken pre-return support is the already-closed changed-contact branch;
fully protected support is the theorem above. -/
theorem knownEdgeProtectedPairNAddFourLaw :
    KnownEdgeProtectedPairNAddFourLaw := by
  intro w N e hN start D times hlive hnd
  by_cases hpre : PathGrooves D.A.toSupported.paths D.B.preReturn.2
  · have hliveA : ∀ k ∈ times,
        (stepN w k (start.1, D.A.baseState)).isSome := by
      simpa [D.A_base] using hlive
    have hndA : (times.map
        (restrictedTonguesAt w N (start.1, D.A.baseState))).Nodup := by
      simpa [D.A_base] using hnd
    exact D.A.preReturn_grooved_protected_pair_all_run_distinct_le_N_add_four
      hN D.B D.B_base D.A_grooves D.B_grooves hpre times hliveA hndA
  · have htrace : PhysicalTrace w (e, D.A.activatedState)
        D.B.exploration D.B.preReturn := by
      simpa [D.B_base] using D.B.exploration_trace
    obtain ⟨S⟩ :=
      PartialSecondRunSharp.ManufacturedReflector.changedContact_of_broken_simple
        D.A
      D.A_grooves htrace D.B.exploration_simple hpre
    have hliveA : ∀ k ∈ times,
        (stepN w k (start.1, D.A.baseState)).isSome := by
      simpa [D.A_base] using hlive
    have hndA : (times.map
        (restrictedTonguesAt w N
          (start.1, D.A.baseState))).Nodup := by
      simpa [D.A_base] using hnd
    exact S.all_run_distinct_le_N_add_four
      hN D.A_grooves times hliveA hndA

end GeneralN
