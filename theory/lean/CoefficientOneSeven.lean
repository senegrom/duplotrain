import SharpSixEventAssembly
import SharpStateLawAssembly

/-!
# Conditional coefficient-one bound

The canonical six-event reduction is already fully raw and finite.  This file
records its exact quantitative payoff: if the displayed sharp six-event
residue is impossible, then a known-edge run has at most five globally novel
repeated-writer events, hence at most `N+6` distinct tongue vectors.  Splitting
off a possible arbitrary time-zero vector gives `N+7` for an arbitrary start.

No certificate or periodicity hypothesis is introduced here.  The only open
premise is `IncomingSharpSixEventResidueImpossible`, the explicit geometric
residue in `SharpSixEventAssembly`.
-/

namespace GeneralN

/-- Known-edge coefficient-one event statement at budget five. -/
def KnownEdgeFiveRepeatedWriterNovelty : Prop :=
  ∀ (w : Wiring) (N e : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (start : Nat × Tongues) (K : Nat),
      w.link e = some start.1 →
      (rawRepeatedWriterNovelTimes w N start K).length ≤ 5

/-- The exact sharp six-event residue is precisely what can violate the
known-edge five-event budget. -/
theorem knownEdgeFiveRepeatedWriterNovelty_of_sharpSixEventResidueImpossible
    (hclose : IncomingSharpSixEventResidueImpossible) :
    KnownEdgeFiveRepeatedWriterNovelty := by
  intro w N e hN start K hentry
  by_contra hnot
  have hsix :
      6 ≤ (rawRepeatedWriterNovelTimes w N start K).length := by
    omega
  obtain ⟨R, hR⟩ :=
    six_repeated_novelties_reduce_to_sharp_residue
      hN start hentry K hsix
  exact hclose w N e hN start hentry R hR

/-- First-writer charging plus five repeated-writer novelties gives the
known-edge `N+6` count. -/
theorem knownEdge_distinct_le_N_add_six_of_fiveRepeatedWriterNovelty
    (hfive : KnownEdgeFiveRepeatedWriterNovelty)
    (w : Wiring) (N e : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hentry : w.link e = some start.1)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  let K := maxRawTime times
  have htimes : ∀ k, k ∈ times → k ≤ K := by
    intro k hk
    exact le_maxRawTime_of_mem hk
  have hbudget :
      (rawRepeatedWriterNovelTimes w N start K).length ≤ 5 :=
    hfive w N e hN start K hentry
  have hcount := distinct_samples_le_of_repeated_writer_novelty
    w N hN start K 5 hbudget times htimes hnd
  omega

/-- Coefficient-one state law with constant seven. -/
def StateLawNAddSeven : Prop :=
  ∀ (w : Wiring) (N : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (start : Nat × Tongues) (times : List Nat),
      (∀ k ∈ times, (stepN w k start).isSome) →
      (times.map (restrictedTonguesAt w N start)).Nodup →
      times.length ≤ N + 7

private theorem coeff1_nodup_of_map_nodup
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

private theorem coeff1_nodup_map_filter
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

private theorem coeff1_nodup_filter_nat (p : Nat → Bool) :
    ∀ {xs : List Nat}, xs.Nodup → (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          constructor
          · intro hm
            exact hnd.1 (List.mem_filter.mp hm).1
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem coeff1_zero_positive_partition :
    ∀ xs : List Nat,
      (xs.filter (fun k => decide (k = 0))).length +
        (xs.filter (fun k => decide (0 < k))).length = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons k rest ih =>
      by_cases hk : k = 0
      · subst k
        simp
        omega
      · have hkPos : 0 < k := by omega
        simp [hk, hkPos]
        omega

private theorem coeff1_zero_filter_length_le_one
    {xs : List Nat} (hnd : xs.Nodup) :
    (xs.filter (fun k => decide (k = 0))).length ≤ 1 := by
  have hfilterNodup :
      (xs.filter (fun k => decide (k = 0))).Nodup :=
    coeff1_nodup_filter_nat _ hnd
  apply nodup_nat_lt_length hfilterNodup
  intro k hk
  have hk0 : k = 0 :=
    of_decide_eq_true (List.mem_filter.mp hk).2
  omega

/-- A known-edge five-event theorem gives the arbitrary-start `N+7` bound.
The sole extra vector is the possible time-zero state before the first
successful physical edge crossing. -/
theorem stateLawNAddSeven_of_knownEdgeFiveRepeatedWriterNovelty
    (hfive : KnownEdgeFiveRepeatedWriterNovelty) :
    StateLawNAddSeven := by
  intro w N hN start times hlive hnd
  have htimesNodup : times.Nodup :=
    coeff1_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  cases hstep : step w start with
  | none =>
      have hlt : ∀ k ∈ times, k < 1 := by
        intro k hk
        cases k with
        | zero => omega
        | succ k =>
            have hkLive := hlive (k + 1) hk
            simp [stepN, hstep] at hkLive
      have hsmall := nodup_nat_lt_length htimesNodup hlt
      omega
  | some next =>
      have hstepOne : stepN w 1 start = some next := by
        simpa [stepN] using hstep
      let positive := times.filter (fun k => decide (0 < k))
      let shifted := positive.map (fun k => k - 1)
      have hshiftVector : shifted.map
          (restrictedTonguesAt w N next) =
          positive.map (restrictedTonguesAt w N start) := by
        dsimp [shifted]
        rw [List.map_map]
        apply List.map_congr_left
        intro k hk
        have hkPos : 0 < k :=
          of_decide_eq_true (List.mem_filter.mp hk).2
        have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
        have hkEq : k = 1 + (k - 1) := by omega
        have hrun : stepN w k start = stepN w (k - 1) next := by
          rw [hkEq, stepN_add, hstepOne]
          simp
        have hkLive := hlive k hkTimes
        cases htail : stepN w (k - 1) next with
        | none =>
            rw [hrun, htail] at hkLive
            simp at hkLive
        | some finish =>
            have hglobal : stepN w k start = some finish := by
              rw [hrun, htail]
            simp [Function.comp_apply, restrictedTonguesAt, tonguesAt,
              hglobal, htail]
      have hpositiveNodup :
          (positive.map (restrictedTonguesAt w N start)).Nodup := by
        dsimp [positive]
        exact coeff1_nodup_map_filter _ hnd
      have hshiftedNodup :
          (shifted.map (restrictedTonguesAt w N next)).Nodup := by
        rw [hshiftVector]
        exact hpositiveNodup
      have hentry : w.link (exitPort start) = some next.1 :=
        (step_some_parts hstep).1
      have hshiftedBound : shifted.length ≤ N + 6 :=
        knownEdge_distinct_le_N_add_six_of_fiveRepeatedWriterNovelty
          hfive w N (exitPort start) hN next shifted hentry
            hshiftedNodup
      have hpositiveLength : positive.length = shifted.length := by
        simp [shifted]
      have hzeroBound :
          (times.filter (fun k => decide (k = 0))).length ≤ 1 :=
        coeff1_zero_filter_length_le_one htimesNodup
      have hpartition := coeff1_zero_positive_partition times
      dsimp [positive] at hpositiveLength
      omega

/-- Closing the single raw six-event residue proves the coefficient-one
`N+7` state bound. -/
theorem stateLawNAddSeven_of_sharpSixEventResidueImpossible
    (hclose : IncomingSharpSixEventResidueImpossible) :
    StateLawNAddSeven :=
  stateLawNAddSeven_of_knownEdgeFiveRepeatedWriterNovelty
    (knownEdgeFiveRepeatedWriterNovelty_of_sharpSixEventResidueImpossible
      hclose)

end GeneralN
