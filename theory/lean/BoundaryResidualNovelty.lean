import ProtectedPairNAddFour

/-!
# Double-reduced novelty at the productive boundary

This module closes the noncanonical unchanged-occurrence branch once the
second manufactured reflector is fully protected.  The arbitrary boundary
vector and both construction journeys are retained in the double-reduced
history.  If the old action switch occurs among the second construction's
first writers, protected repair costs one fresh vector over an `N + 3`
history.  If it does not occur, the reserved action coordinate sharpens the
history to `N + 2`, while the general protected repair costs two vectors.
Either way the complete cover has size at most `N + 4`.
-/

namespace GeneralN

/-- Lift a novelty cover for the protected repair tail across the two
manufacturing journeys.  Every prefix vector is supplied by the shared
history; only the shifted tail spends the given novelty budget. -/
theorem ManufacturedReflector.two_journeys_then_shared_history_novelty_cover
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
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
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
      have hliveQ := stepN_prefix_some hqLe hreachB
      have hshift := tonguesAt_add_of_reaches hreachA hliveQ
      have hm := B.manufacturing_journey_mem_sharpHistory
        (N := N) hBpaths (j := q)
          (by simpa [secondTravel] using hqLe)
      have hm' : restrictedTonguesAt w N (e, A.activatedState) q ∈
          B.sharpConstructionHistory N := by
        simpa [hbase] using hm
      have heq : restrictedTonguesAt w N (g, A.baseState) d =
          restrictedTonguesAt w N (e, A.activatedState) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      exact hhistory _ (Or.inr hm')
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
        have hstartEq : tonguesAt w (g, A.baseState)
            (totalTravel + (k - totalTravel)) =
            tonguesAt w (g, A.baseState) k := by
          rw [← hkEq]
        unfold restrictedTonguesAt
        exact congrArg (VectorCount.restrict N)
          (hshift.symm.trans hstartEq)
  have hfilteredNodup :
      ((times.filter (fun k => decide (totalTravel < k))).map
        (restrictedTonguesAt w N (g, A.baseState))).Nodup :=
    tailsharp_nodup_map_filter _ hnd
  have hlocalNodup :
      (localTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup := by
    rw [hlocalVector]
    exact hfilteredNodup
  obtain ⟨fresh, hfresh, hlocalMem⟩ :=
    htail localTimes hlocalLive hlocalNodup
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

/-- If the old action switch is a productive first writer of the second
construction, every selected live time of the complete run is represented
by the double-reduced two-journey history plus at most one fresh vector. -/
theorem InitialEntryWriterOccurrence.noncanonical_protected_pair_one_novelty_of_action_writer
    {w : Wiring} {N g e k0 : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hstay : O.next = O.middle)
    (hdifferent : O.before.length ≠ R.runway.length)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hApaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).baseState))).Nodup) :
    NoveltyCoverOn w N
      (g, (ManufacturedReflector.flip R).baseState) times
      (O.doubleReducedTwoHistory B N original) 1 := by
  let history := O.doubleReducedTwoHistory B N original
  have hhistoryData := O.mem_doubleReducedTwoHistory
    (N := N) B original hstay hdifferent hbase
  have hhistory : ∀ x,
      x ∈ (ManufacturedReflector.flip R).sharpConstructionHistory N ∨
        x ∈ B.sharpConstructionHistory N → x ∈ history := by
    intro x hx
    simpa [history] using hhistoryData.2 x hx
  have hAatBase : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes,
        (stepN w k (g, B.activatedState)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
      NoveltyCoverOn w N (g, B.activatedState) tailTimes
        history 1 := by
    intro tailTimes htailLive htailNodup
    exact R.protected_repair_one_novelty_over_history_of_action_writer
      hN B hAatBase hBpaths hpre history hhistory
        ht hwriter tailTimes htailLive htailNodup
  have hcover :=
    (ManufacturedReflector.flip R).two_journeys_then_shared_history_novelty_cover
      B hbase hApaths hBpaths history hhistory 1 htail
        times hlive hnd
  simpa [history] using hcover

/-- In the noncanonical unchanged-occurrence branch, the double-reduced
history and the protected repair tail have combined size at most `N + 4`.
The result is a cover, not merely a cardinality estimate, so it can be used
with an independently known historical boundary vector. -/
theorem InitialEntryWriterOccurrence.noncanonical_protected_pair_cover
    {w : Wiring} {N g e k0 : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hstay : O.next = O.middle)
    (hdifferent : O.before.length ≠ R.runway.length)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hApaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).baseState))).Nodup) :
    ∃ budget,
      (O.doubleReducedTwoHistory B N original).length + budget ≤ N + 4 ∧
      NoveltyCoverOn w N
        (g, (ManufacturedReflector.flip R).baseState) times
        (O.doubleReducedTwoHistory B N original) budget := by
  let history := O.doubleReducedTwoHistory B N original
  have hhistoryData := O.mem_doubleReducedTwoHistory
    (N := N) B original hstay hdifferent hbase
  have hhistory : ∀ x,
      x ∈ (ManufacturedReflector.flip R).sharpConstructionHistory N ∨
        x ∈ B.sharpConstructionHistory N → x ∈ history := by
    intro x hx
    simpa [history] using hhistoryData.2 x hx
  have hAatBase : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  by_cases haction :
      R.actionSwitch ∈ B.constructionFirstWriterSwitches N
  · unfold ManufacturedReflector.constructionFirstWriterSwitches at haction
    obtain ⟨t, ht, hwriter⟩ := List.mem_map.mp haction
    have hcover :=
      O.noncanonical_protected_pair_one_novelty_of_action_writer
        hN B original hstay hdifferent hbase hApaths hBpaths hpre
          ht hwriter times hlive hnd
    have hlength := O.doubleReducedTwoHistory_length_le_N_add_three
      hN B original hdifferent hbase hAatBase hpre
    refine ⟨1, ?_, ?_⟩
    · omega
    · simpa [history] using hcover
  · have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes,
          (stepN w k (g, B.activatedState)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
        NoveltyCoverOn w N (g, B.activatedState) tailTimes
          history 2 := by
      intro tailTimes htailLive htailNodup
      exact (ManufacturedReflector.flip R).protected_repair_two_novelty_over_history
        hN B hAatBase hBpaths hpre history hhistory
          tailTimes htailLive htailNodup
    have hcover :=
      (ManufacturedReflector.flip R).two_journeys_then_shared_history_novelty_cover
        B hbase hApaths hBpaths history hhistory 2 htail
          times hlive hnd
    have hlength :=
      O.doubleReducedTwoHistory_length_le_N_add_two_of_action_absent
        hN B original hdifferent hbase hAatBase hpre haction
    refine ⟨2, ?_, ?_⟩
    · omega
    · simpa [history] using hcover

/-- Exact arbitrary-boundary count for the noncanonical unchanged
occurrence followed by a fully protected opposite reflector. -/
theorem InitialEntryWriterOccurrence.noncanonical_protected_pair_all_run_distinct_le_N_add_four
    {w : Wiring} {N g e k0 : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hstay : O.next = O.middle)
    (hdifferent : O.before.length ≠ R.runway.length)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hApaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).baseState))).Nodup) :
    times.length + 1 ≤ N + 4 := by
  obtain ⟨budget, htotal, hcover⟩ :=
    O.noncanonical_protected_pair_cover hN B original hstay
      hdifferent hbase hApaths hBpaths hpre times hlive
        (List.nodup_cons.mp hnd).2
  have horiginal : VectorCount.restrict N original ∈
      O.doubleReducedTwoHistory B N original :=
    (O.mem_doubleReducedTwoHistory (N := N) B original hstay
      hdifferent hbase).1
  have hcount := novelty_cover_count_with_historical_extra
    (VectorCount.restrict N original) hcover horiginal hnd
  omega

/-- A saturated productive boundary cannot contain a fully protected pair
after a noncanonical unchanged occurrence.  This is the contradiction form
used by the productive-boundary case split. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_noncanonical_unchanged_protected_pair
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hstay : O.next = O.middle)
    (hdifferent : O.before.length ≠ R.runway.length)
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2) :
    False := by
  have hApathsS : PathGrooves S.A.toSupported.paths S.A.activatedState := by
    rw [← S.activated]
    exact S.grooves
  have hApaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState := by
    simpa [hAeq] using hApathsS
  have hAbase : (ManufacturedReflector.flip R).baseState =
      S.source.base := by
    simpa [hAeq] using S.reflector_base
  have hlive : ∀ k ∈ S.source.times,
      (stepN w k
        (S.source.g, (ManufacturedReflector.flip R).baseState)).isSome := by
    intro k hk
    simpa [hAbase] using S.source.live k hk
  have hnd : (VectorCount.restrict N S.source.original ::
      S.source.times.map (restrictedTonguesAt w N
        (S.source.g,
          (ManufacturedReflector.flip R).baseState))).Nodup := by
    simpa [hAbase] using S.source.distinct
  have hbound :=
    O.noncanonical_protected_pair_all_run_distinct_le_N_add_four
      hN B S.source.original hstay hdifferent hbase hApaths
        hBpaths hpre S.source.times hlive hnd
  have hsaturated := S.source.saturated
  omega

end GeneralN
