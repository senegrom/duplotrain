import MellitSharpTail
import TrackQuantitative

/-!
# Mellit's first two turnarounds and global novelty

This file isolates the loop-erased-stack shortcut from the six-frame case
tree. A switch-simple exploration has only first writers. Its first repeated
switch either settles immediately or manufactures a reflector; the completed
reverse then contributes at most its single contact vector. If the second
repeat reaches a compatible opposite-reflector pair, the rest of the
trajectory has the four-vector Gray cover.

The principal theorem below is deliberately raw and horizon-independent:
for a literal first manufacturing journey followed by such a pair, at most
five productive repeated writers create globally new tongue vectors. This
does not assert that every second-repeat pair is compatible, so the general
finite-alternation target and StateLaw remain open.
-/

namespace GeneralN

private theorem nodup_subset_length_mellit
    {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs cover : List α},
      xs.Nodup →
      (∀ x ∈ xs, x ∈ cover) →
      xs.length ≤ cover.length := by
  intro xs
  induction xs with
  | nil =>
      intro cover _ _
      exact Nat.zero_le _
  | cons x rest ih =>
      intro cover hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ cover := hsub x List.mem_cons_self
      have hrest : ∀ y ∈ rest, y ∈ cover.erase x := by
        intro y hy
        have hyCover : y ∈ cover :=
          hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun heq => hnd.1 (heq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyCover
      have hle := ih hnd.2 hrest
      have herase : (cover.erase x).length = cover.length - 1 :=
        List.length_erase_of_mem hx
      have hpositive : 0 < cover.length := by
        cases cover with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- Repeated-writer novelty events are monotone with the raw horizon. -/
theorem rawRepeatedWriterNovelTimes_length_mono
    {w : Wiring} {N H K : Nat} {start : Nat × Tongues}
    (hHK : H ≤ K) :
    (rawRepeatedWriterNovelTimes w N start H).length ≤
      (rawRepeatedWriterNovelTimes w N start K).length := by
  apply nodup_subset_length_mellit
  · exact rawRepeatedWriterNovelTimes_nodup w N start H
  · intro k hk
    have hkData := mem_rawRepeatedWriterNovelTimes_iff.mp hk
    exact mem_rawRepeatedWriterNovelTimes_iff.mpr
      ⟨Nat.lt_of_lt_of_le hkData.1 hHK, hkData.2⟩

/-- Every prefix of the canonical first-turnaround journey contains at most
one globally novel repeated-writer post-state. The complete journey theorem
comes from pointwise retrace; horizon monotonicity gives every shorter prefix.
-/
theorem ManufacturedReflector.first_turnaround_repeatedWriterNovelty_le_one
    {w : Wiring} {N g e H : Nat}
    (A : ManufacturedReflector w g e)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    (hH : H ≤ A.exploration.length + A.runway.length + 1) :
    (rawRepeatedWriterNovelTimes w N (g, A.baseState) H).length ≤ 1 := by
  have hmono := rawRepeatedWriterNovelTimes_length_mono
    (w := w) (N := N) (start := (g, A.baseState)) hH
  have hfull := A.manufacturing_repeatedWriterNovelty_le_one hN hpaths
  omega

/-- The raw first-repeat theorem, strengthened with its exact novelty charge.
Either the first repeated switch already gives a bounded lasso, or the actual
manufactured first reflector has at most one repeated-writer novelty through
its complete pop/retrace journey. -/
theorem first_repeat_turnaround_novelty_outcome
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish)
    (hentry : w.link e = some start.1) :
    EventuallyPeriodicWithin w start (3 * N) ∨
      ∃ (A : ManufacturedReflector w start.1 e)
          (state : Tongues) (travel : Nat),
        travel ≤ 2 * N + 1 ∧
        PathGrooves A.toSupported.paths state ∧
        A.baseState = start.2 ∧
        state = A.activatedState ∧
        stepN w travel start = some (e, state) ∧
        (∀ j, j ∉ A.exploration.map passageSwitch →
          state j = start.2 j) ∧
        (rawRepeatedWriterNovelTimes w N start
          (A.exploration.length + A.runway.length + 1)).length ≤ 1 := by
  rcases first_activated_quantitative_outcome hN hlive hentry with
    hperiodic | hreflector
  · exact Or.inl hperiodic
  · right
    obtain ⟨A, state, travel, htravel, hpaths, hbase, hactivated,
      hreach, hpreserves⟩ := hreflector
    have hactivatedPaths :
        PathGrooves A.toSupported.paths A.activatedState := by
      simpa [hactivated] using hpaths
    have hbound :=
      A.manufacturing_repeatedWriterNovelty_le_one hN hactivatedPaths
    have hstart : (start.1, A.baseState) = start := by
      apply Prod.ext
      · rfl
      · exact hbase
    rw [hstart] at hbound
    exact ⟨A, state, travel, htravel, hpaths, hbase,
      hactivated, hreach, hpreserves, hbound⟩

/-- Mellit's literal second-repeat dichotomy, retaining the sharp charge for
the entire first turnaround. The second branch is an actual opposite
reflector, not a conditional certificate. -/
theorem mellit_second_repeat_with_first_turnaround_bound
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
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
        EventuallyPeriodic w (g, B.activatedState) ∧
        (rawRepeatedWriterNovelTimes w N (g, A.baseState)
          (A.exploration.length + A.runway.length + 1)).length ≤ 1) := by
  have hactivatedPaths :
      PathGrooves A.toSupported.paths A.activatedState := by
    simpa [hstate] using hA
  have hfirst :=
    A.manufacturing_repeatedWriterNovelty_le_one hN hactivatedPaths
  rcases mellit_second_repeat_cycle_or_pair A hstate hA htrace hnonsimple with
    hcycle | hpair
  · exact Or.inl hcycle
  · right
    obtain ⟨B, atRepeat, visited, backSteps, hvisited, hreach,
      hAbase, hBactivated, hperiodic⟩ := hpair
    exact ⟨B, atRepeat, visited, backSteps, hvisited, hreach,
      hAbase, hBactivated, hperiodic, hfirst⟩

/-- **First turnaround plus compatible second turnaround: five raw
novelties.**

The first manufactured reflector contributes at most its one contact vector.
At its completed return the run reaches a compatible opposite-reflector pair;
the pair contributes at most its four Gray corners. The statement quantifies
over every raw horizon, so it bounds every globally novel repeated-writer
post-state on this entire physical trajectory, not merely one selected list.
-/
theorem first_turnaround_then_compatible_pair_repeatedWriterNovelty_le_five
    {w : Wiring} {h g e N : Nat}
    (P : ManufacturedReflector w h g)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hPpaths : PathGrooves P.toSupported.paths P.activatedState)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    (hreach : stepN w
      (P.exploration.length + P.runway.length + 1)
      (h, P.baseState) = some (g, state)) :
    ∀ H,
      (rawRepeatedWriterNovelTimes w N (h, P.baseState) H).length ≤ 5 := by
  intro H
  let J := P.exploration.length + P.runway.length + 1
  let start : Nat × Tongues := (h, P.baseState)
  by_cases hHJ : H ≤ J
  · have hmono := rawRepeatedWriterNovelTimes_length_mono
      (w := w) (N := N) (start := start) hHJ
    have hone := P.manufacturing_repeatedWriterNovelty_le_one hN hPpaths
    dsimp [J, start] at hmono
    omega
  · have hJH : J ≤ H := by omega
    let times := rawRepeatedWriterPostTimes w N start H
    let history := rawFirstWriterHistory w N start H
    have hexplorationH : P.exploration.length ≤ H := by
      dsimp [J] at hJH
      omega
    have hpair : FourNoveltyCover w N start times
        (history ++ [VectorCount.restrict N P.activatedState]) := by
      apply manufactured_pair_history_and_tail_four_novelty_cover
        A B state hA hB hAB hBA
          (start := start) (K := J)
      · simpa [J, start] using hreach
      · intro j hj hjJ
        have hjJourney :
            j ≤ P.exploration.length + P.runway.length + 1 := by
          dsimp [J] at hjJ
          omega
        have hm := P.manufacturing_journey_mem_rawHistory_one_extra
          (N := N) (K := H) hPpaths hexplorationH j hjJourney
        simpa [start, history] using hm
    obtain ⟨pairFresh, hpairFresh, hpairMem⟩ := hpair
    have hcover : NoveltyCoverOn w N start times history 5 := by
      refine ⟨VectorCount.restrict N P.activatedState :: pairFresh,
        ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro j hj
        have hm := hpairMem j hj
        simpa [List.append_assoc] using hm
    have hnew : ∀ j ∈ times,
        restrictedTonguesAt w N start j ∉ history := by
      simpa [times, history] using
        (repeatedWriterPostTimes_avoid_firstHistory hN start H)
    have hnd :
        (times.map (restrictedTonguesAt w N start)).Nodup := by
      dsimp [times]
      rw [map_repeatedWriterPostTimes_eq_fresh]
      exact rawRepeatedWriterFresh_nodup w N start H
    have hcount := noveltyCoverOn_fresh_distinct_count hcover hnew hnd
    simpa [times, rawRepeatedWriterPostTimes, start] using hcount

end GeneralN
