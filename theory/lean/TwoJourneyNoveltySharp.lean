import TwoHistoryUnionChargeSharp

/-!
# Boundary-aware novelty composition with a sharper history budget

This factors the bookkeeping used by the `N+5` two-reflector theorem.  If the
two completed construction histories have size at most `historyCap`, and the
suffix contributes at most `tailBudget` vectors outside that same history,
then the complete sampled run has at most `historyCap + tailBudget` vectors.
The manufacturing/tail boundary is already represented in the history.

For a stay reflector first, `TwoHistoryUnionChargeSharp` gives history size
`N+2`; a two-novelty suffix therefore costs only `N+4`.
-/

namespace GeneralN

/-- Generic two-journey composition using an explicit novelty cover over the
preserved construction history. -/
theorem ManufacturedReflector.two_journeys_then_novelty_le
    {w : Wiring} {N g e historyCap tailBudget : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hhistory : (A.preservedTwoHistoryCore B N).length ≤ historyCap)
    (htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes,
        (stepN w k (g, B.activatedState)).isSome) →
      NoveltyCoverOn w N (g, B.activatedState) tailTimes
        (A.preservedTwoHistoryCore B N) tailBudget)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ historyCap + tailBudget := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let secondTravel := B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let history := A.preservedTwoHistoryCore B N
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
    · dsimp [history]
      apply A.mem_preservedTwoHistoryCore B
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
      dsimp [history]
      exact A.mem_preservedTwoHistoryCore B (Or.inr hm')
  have hlocalLive : ∀ d ∈ localTimes,
      (stepN w d (g, B.activatedState)).isSome := by
    intro d hd
    obtain ⟨k, hkFiltered, rfl⟩ := List.mem_map.mp hd
    have hk := (List.mem_filter.mp hkFiltered).1
    have hkGt : totalTravel < k := by
      have := (List.mem_filter.mp hkFiltered).2
      simpa using this
    have hkEq : k = totalTravel + (k - totalTravel) := by omega
    have hkLive := hlive k hk
    rw [hkEq, stepN_add, hreachTotal] at hkLive
    exact hkLive
  have hlocalCover : NoveltyCoverOn w N
      (g, B.activatedState) localTimes history tailBudget := by
    dsimp [history]
    exact htail localTimes hlocalLive
  obtain ⟨fresh, hfresh, hlocalMem⟩ := hlocalCover
  have hglobalCover : NoveltyCoverOn w N (g, A.baseState)
      times history tailBudget := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hprefix : k ≤ totalTravel
    · apply List.mem_append_left
      exact hprefixCover k hprefix
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
      have hlocalReach : ∃ finish,
          stepN w d (g, B.activatedState) = some finish :=
        Option.isSome_iff_exists.mp (hlocalLive d hdMem)
      have hshift := tonguesAt_add_of_reaches hreachTotal hlocalReach
      have hvector : restrictedTonguesAt w N (g, A.baseState) k =
          restrictedTonguesAt w N (g, B.activatedState) d := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [hvector]
      exact hlocalMem d hdMem
  have hcount := noveltyCoverOn_distinct_count hglobalCover hnd
  have hhistory' : history.length ≤ historyCap := by
    simpa [history] using hhistory
  omega

/-- Stay-first specialisation: two fresh tail vectors give `N+4`. -/
theorem ManufacturedStayReflector.two_journeys_then_two_novelty_le_N_add_four
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedStayReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = (ManufacturedReflector.stay R).activatedState)
    (hApaths : PathGrooves (ManufacturedReflector.stay R).toSupported.paths
      (ManufacturedReflector.stay R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves (ManufacturedReflector.stay R).toSupported.paths
      B.preReturn.2)
    (htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes,
        (stepN w k (g, B.activatedState)).isSome) →
      NoveltyCoverOn w N (g, B.activatedState) tailTimes
        ((ManufacturedReflector.stay R).preservedTwoHistoryCore B N) 2)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, R.base)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, R.base))).Nodup) :
    times.length ≤ N + 4 := by
  let A : ManufacturedReflector w g e := .stay R
  have hbaseGrooves : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have hhistory : (A.preservedTwoHistoryCore B N).length ≤ N + 2 := by
    exact R.preservedTwoHistoryCore_length_le_N_add_two
      hN B hbase hbaseGrooves hpre
  have h := A.two_journeys_then_novelty_le B hbase hApaths hBpaths
    hhistory htail times hlive hnd
  omega

end GeneralN
