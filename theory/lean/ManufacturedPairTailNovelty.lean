import ManufacturedPairNovelty
import FirstReflectorNovelty

/-!
# Absolute-time novelty of a reached manufactured pair

`ManufacturedPairNovelty` proves a four-vector law for a compatible pair
whose local clock starts at zero.  This file transports that law through an
arbitrary successful raw `stepN` prefix.  Liveness of the suffix is derived
from the pair's closed period; it is not an additional premise.

The final theorem combines the `N+2` first-manufacturing-journey bound with
the four-vector tail.  It is a theorem about the raw `Wiring`/`stepN`
dynamics.  It does not assert that every trajectory reaches such a pair, so
the unrestricted `StateLaw` remains a separate question.
-/

namespace GeneralN

/-- A compatible manufactured pair has a successful local run of every
finite length.  This is derived from its positive closed period and makes the
liveness used by the absolute-time transport explicit. -/
theorem manufactured_pair_stepN_some
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    (d : Nat) :
    ∃ finish, stepN w d (g, state) = some finish := by
  let period := 2 * (A.toSupported.travel + B.toSupported.travel)
  have hperiodPos : 0 < period := by
    have hAPos := A.travel_pos
    have hBPos := B.travel_pos
    dsimp [period]
    omega
  have hperiod : stepN w period (g, state) = some (g, state) := by
    dsimp [period]
    exact A.toSupported.paired_period B.toSupported
      hAB hBA state hA hB
  have hfar : stepN w ((d + 1) * period) (g, state) =
      some (g, state) :=
    stepN_mul_period_pair_novelty hperiod (d + 1)
  have hbound : d ≤ (d + 1) * period := by
    have hone : 1 ≤ period := by omega
    have hmul := Nat.mul_le_mul_left (d + 1) hone
    simp only [Nat.mul_one] at hmul
    omega
  exact stepN_prefix_some hbound hfar

/-- Reaching the start of a compatible manufactured pair makes every later
absolute time live.  No separate all-future liveness hypothesis is used. -/
theorem manufactured_pair_absolute_stepN_some
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    {start : Nat × Tongues} {K j : Nat}
    (hreach : stepN w K start = some (g, state))
    (hj : K ≤ j) :
    ∃ finish, stepN w j start = some finish := by
  let d := j - K
  have hjEq : j = K + d := by
    dsimp [d]
    omega
  obtain ⟨finish, hfinish⟩ := manufactured_pair_stepN_some
    A B state hA hB hAB hBA d
  refine ⟨finish, ?_⟩
  rw [hjEq, stepN_add, hreach]
  exact hfinish

/-- **Absolute-time four-phase law.**

After an arbitrary successful prefix reaches a compatible manufactured pair,
every later raw tongue vector is one of the same four local Gray corners. -/
theorem manufactured_pair_absolute_four_phase_tongues
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    {start : Nat × Tongues} {K j : Nat}
    (hreach : stepN w K start = some (g, state))
    (hj : K ≤ j) :
    tonguesAt w start j ∈
      [state,
       A.toSupported.action.apply state,
       B.toSupported.action.apply (A.toSupported.action.apply state),
       A.toSupported.action.apply
         (B.toSupported.action.apply
           (A.toSupported.action.apply state))] := by
  let d := j - K
  have hjEq : j = K + d := by
    dsimp [d]
    omega
  have hlive := manufactured_pair_stepN_some
    A B state hA hB hAB hBA d
  have hshift := tonguesAt_add_of_reaches hreach hlive
  rw [hjEq, hshift]
  exact manufactured_pair_all_time_four_phase_tongues
    A B state hA hB hAB hBA d

/-- The local all-time four-vector cover transported to absolute times after
an arbitrary successful reach step `K`. -/
theorem manufactured_pair_absolute_four_novelty_cover
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some (g, state))
    (times : List Nat) (history : List (List Bool))
    (htimes : ∀ j ∈ times, K ≤ j) :
    FourNoveltyCover w N start times history := by
  let corners : List Tongues :=
    [state,
     A.toSupported.action.apply state,
     B.toSupported.action.apply (A.toSupported.action.apply state),
     A.toSupported.action.apply
       (B.toSupported.action.apply
         (A.toSupported.action.apply state))]
  refine ⟨corners.map (VectorCount.restrict N), ?_, ?_⟩
  · simp [corners]
  · intro j hj
    apply List.mem_append_right history
    apply List.mem_map.mpr
    refine ⟨tonguesAt w start j, ?_, rfl⟩
    exact manufactured_pair_absolute_four_phase_tongues
      A B state hA hB hAB hBA hreach (htimes j hj)

/-- A historical cover and a reached compatible pair form one absolute
four-novelty cover over arbitrary selected times.  Times before `K` must be
historical; times at or after `K` are covered by the four pair corners. -/
theorem manufactured_pair_history_and_tail_four_novelty_cover
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some (g, state))
    (times : List Nat) (history : List (List Bool))
    (hhistory : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    FourNoveltyCover w N start times history := by
  let corners : List Tongues :=
    [state,
     A.toSupported.action.apply state,
     B.toSupported.action.apply (A.toSupported.action.apply state),
     A.toSupported.action.apply
       (B.toSupported.action.apply
         (A.toSupported.action.apply state))]
  refine ⟨corners.map (VectorCount.restrict N), ?_, ?_⟩
  · simp [corners]
  · intro j hj
    by_cases htail : K ≤ j
    · apply List.mem_append_right history
      apply List.mem_map.mpr
      refine ⟨tonguesAt w start j, ?_, rfl⟩
      exact manufactured_pair_absolute_four_phase_tongues
        A B state hA hB hAB hBA hreach htail
    · apply List.mem_append_left
      exact hhistory j hj (by omega)

/-- **Reached-pair `N+6` theorem with an explicit historical cover.**

This is already in the raw language of tracks and switches: a `stepN` run
reaches the pair at time `K`; the selected earlier vectors have a history of
size at most `N+2`; compatibility itself supplies the live four-vector tail.
-/
theorem manufactured_pair_reached_with_history_distinct_le_N_add_six
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some (g, state))
    (times : List Nat) (history : List (List Bool))
    (hhistoryLength : history.length ≤ N + 2)
    (hhistory : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  apply fourNoveltyCover_to_N_add_six hhistoryLength
  · exact manufactured_pair_history_and_tail_four_novelty_cover
      A B state hA hB hAB hBA hreach times history hhistory
  · exact hnd

private theorem nodup_map_filter_pair_tail {α : Type}
    {f : Nat → α} {p : Nat → Bool} :
    ∀ {ks : List Nat},
      (ks.map f).Nodup → ((ks.filter p).map f).Nodup := by
  intro ks
  induction ks with
  | nil => intro _; simp
  | cons k rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p k with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨j, hj, hfj⟩ := List.mem_map.mp hm
            exact hnd.1 (List.mem_map.mpr
              ⟨j, (List.mem_filter.mp hj).1, hfj⟩)
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

/-- Concrete prefix form: if the pairwise-distinct selected vectors before
the reach time number at most `N+2`, every selected vector on the entire raw
trajectory—including arbitrarily late pair cycles—numbers at most `N+6`. -/
theorem manufactured_pair_reached_distinct_le_N_add_six
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some (g, state))
    (times : List Nat)
    (hprefix :
      (times.filter (fun j => decide (j < K))).length ≤ N + 2)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  let before := times.filter (fun j => decide (j < K))
  let history := before.map (restrictedTonguesAt w N start)
  have hhistoryLength : history.length ≤ N + 2 := by
    dsimp [history, before]
    simpa only [List.length_map] using hprefix
  have hhistory : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history := by
    intro j hj hjK
    dsimp [history, before]
    apply List.mem_map.mpr
    exact ⟨j,
      List.mem_filter.mpr ⟨hj, decide_eq_true hjK⟩, rfl⟩
  exact manufactured_pair_reached_with_history_distinct_le_N_add_six
    A B state hA hB hAB hBA hreach times history
    hhistoryLength hhistory hnd

/-- **First manufactured journey followed by a compatible pair.**

The earlier `N+2` bound is discharged here by
`ManufacturedReflector.manufacturing_journey_distinct_le_N_add_two`; the
future `+4` is discharged by the reached-pair theorem above.  The sole reach
premise is the literal raw `stepN` statement joining the two phases.
-/
theorem manufacturing_journey_then_pair_distinct_le_N_add_six
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
      (h, P.baseState) = some (g, state))
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N
      (h, P.baseState))).Nodup) :
    times.length ≤ N + 6 := by
  let K := P.exploration.length + P.runway.length + 1
  let before := times.filter (fun j => decide (j < K))
  have hbeforeTimes : ∀ j ∈ before,
      j ≤ P.exploration.length + P.runway.length + 1 := by
    intro j hj
    have hjK : j < K :=
      of_decide_eq_true (List.mem_filter.mp hj).2
    dsimp [K] at hjK
    omega
  have hbeforeNodup :
      (before.map (restrictedTonguesAt w N
        (h, P.baseState))).Nodup := by
    dsimp [before]
    exact nodup_map_filter_pair_tail hnd
  have hprefix : before.length ≤ N + 2 :=
    P.manufacturing_journey_distinct_le_N_add_two
      hN hPpaths before hbeforeTimes hbeforeNodup
  apply manufactured_pair_reached_distinct_le_N_add_six
    A B state hA hB hAB hBA (K := K)
      (start := (h, P.baseState))
  · simpa [K] using hreach
  · simpa [before] using hprefix
  · exact hnd

end GeneralN
