import FirstReflectorNovelty
import ManufacturedPairNovelty
import ForeignSpliceNovelty
import RepeatedNoveltyDecomposition
import RunwaySpliceNovelty
import TrackGlobalRepair

/-!
# Sharp state-law assembly

This file contains only the final novelty bookkeeping around the physical
track constructions.  It deliberately separates two questions:

* the arithmetic/trajectory assembly proved here; and
* the remaining semantic assertion that every raw global-repair trajectory
  admits the advertised five-vector novelty cover.

The budget is exact:

* at most `N+1` historical vectors (the initial vector and at most one vector
  charged to each switch);
* four vectors for a compatible manufactured-reflector orbit; and
* one further vector for the strict foreign candy splice.

Thus a certified trajectory has at most `N+6` distinct tongue vectors.  No
path length or period length occurs in the conclusion.
-/

namespace GeneralN

/-- Five exceptional vectors above a supplied history. -/
def FiveNoveltyCover (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (times : List Nat)
    (history : List (List Bool)) : Prop :=
  NoveltyCoverOn w N start times history 5


theorem ManufacturedReflector.ChangedForwardMerge.distinct_le_N_add_five
    {w : Wiring} {g e N : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R))
    (history : List (List Bool))
    (hhistory : history.length ≤ N + 1)
    (hleadHistorical : ∀ j, j ≤ A.toSupported.travel →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈ history)
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).activatedState))).Nodup) :
    times.length ≤ N + 5 := by
  have hcover := hmerge.runway_or_candy_absolute_four_novelty
    N history hleadHistorical times
  have hcount := fourNoveltyCover_distinct_count hcover hnd
  omega

theorem three_pair_then_one_splice_four
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {pairTimes spliceTimes : List Nat}
    {history : List (List Bool)}
    (hpair : NoveltyCoverOn w N start pairTimes history 3)
    (hsplice : NoveltyCoverOn w N start spliceTimes history 1) :
    FourNoveltyCover w N start (pairTimes ++ spliceTimes) history := by
  have hcombined := noveltyCoverOn_append hpair hsplice
  simpa [FourNoveltyCover] using hcombined

def ManufacturedReflector.sharpConstructionHistory
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (N : Nat) : List (List Bool) :=
  ((List.range (A.exploration.length + 1)).map
      (restrictedTonguesAt w N (g, A.baseState))) ++
    [VectorCount.restrict N A.activatedState]

/-- The canonical first-construction history has size at most `N+2`. -/
theorem ManufacturedReflector.sharpConstructionHistory_length
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N) :
    (A.sharpConstructionHistory N).length ≤ N + 2 := by
  have hlength : A.exploration.length ≤ N :=
    A.exploration_trace.simple_length_le hN A.exploration_simple
  simp [ManufacturedReflector.sharpConstructionHistory]
  omega

/-- Every raw vector through the complete first manufacturing journey lies
in the canonical `N+2` history.  This is pointwise, including the contact and
every depth of the reverse runway. -/
theorem ManufacturedReflector.manufacturing_journey_mem_sharpHistory
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    {j : Nat}
    (hj : j ≤ A.exploration.length + A.runway.length + 1) :
    restrictedTonguesAt w N (g, A.baseState) j ∈
      A.sharpConstructionHistory N := by
  let prefixHistory :=
    (List.range (A.exploration.length + 1)).map
      (restrictedTonguesAt w N (g, A.baseState))
  by_cases hprefix : j ≤ A.exploration.length
  · apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨j, List.mem_range.mpr (by omega), rfl⟩
  · have hvectorAtRepeat :
        restrictedTonguesAt w N (g, A.baseState)
            A.exploration.length =
          VectorCount.restrict N A.preReturn.2 := by
      simp [restrictedTonguesAt, tonguesAt,
        A.exploration_trace.sound]
    have hpre : VectorCount.restrict N A.preReturn.2 ∈
        prefixHistory := by
      rw [← hvectorAtRepeat]
      apply List.mem_map.mpr
      exact ⟨A.exploration.length,
        List.mem_range.mpr (by omega), rfl⟩
    rcases completed_retrace_at_vector_mem_history_or_contact
        A.runway_trace (A.runway_grooved hpaths) A.entryEdge
        A.return_arrive_mouth A.exploration_trace.sound
        N prefixHistory hpre (by omega) hj with hhistory | hactivated
    · exact List.mem_append_left _ hhistory
    · apply List.mem_append_right prefixHistory
      exact List.mem_singleton.mpr hactivated

structure SharpGlobalRepairCertificate
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (times : List Nat) where
  history : List (List Bool)
  pairTimes : List Nat
  spliceTimes : List Nat
  history_length : history.length ≤ N + 2
  times_eq : times = pairTimes ++ spliceTimes
  pair_cover : NoveltyCoverOn w N start pairTimes history 3
  splice_cover : NoveltyCoverOn w N start spliceTimes history 1

structure KnownEdgeSharpRepairCertificate
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (times : List Nat) where
  history : List (List Bool)
  pairTimes : List Nat
  spliceTimes : List Nat
  history_length : history.length ≤ N + 1
  times_eq : times = pairTimes ++ spliceTimes
  pair_cover : NoveltyCoverOn w N start pairTimes history 3
  splice_cover : NoveltyCoverOn w N start spliceTimes history 1


private theorem sharp_nodup_of_map_nodup
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

private theorem sharp_nodup_map_filter
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

private theorem sharp_nodup_filter_nat (p : Nat → Bool) :
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

private theorem sharp_zero_positive_partition :
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

private theorem sharp_zero_filter_length_le_one
    {xs : List Nat} (hnd : xs.Nodup) :
    (xs.filter (fun k => decide (k = 0))).length ≤ 1 := by
  have hfilterNodup :
      (xs.filter (fun k => decide (k = 0))).Nodup :=
    sharp_nodup_filter_nat _ hnd
  apply nodup_nat_lt_length hfilterNodup
  intro k hk
  have hk0 : k = 0 :=
    of_decide_eq_true (List.mem_filter.mp hk).2
  omega

/-- Every repeated-writer novelty already carries the concrete fixed-track
rerouting data needed by a physical obstruction argument.  Its parity
witness is either a genuinely first writer or an interlacing earlier writer
frame, and both the witness and the closing writer leave through their
immutable stem links.

This theorem is not a counting assumption: it is the proved raw geometry of
each event counted by `KnownEdgeFourRepeatedWriterNovelty` below. -/
theorem RawRepeatedWriterNovelAt.open_frame_with_fixed_stem_successors
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {right : Nat}
    (h : RawRepeatedWriterNovelAt w N start right) :
    ∃ left reroute,
      RawLastWriterFrame w N start left right ∧
      RawProductiveAt w N start reroute ∧
      rawWriterAt w start reroute ≠ rawWriterAt w start right ∧
      (∀ j, left < j → j < reroute →
        RawProductiveAt w N start j →
        rawWriterAt w start j ≠ rawWriterAt w start reroute) ∧
      RawOpenReroutingShape w N start left reroute right ∧
      (∃ next,
        stepN w (reroute + 1) start = some next ∧
        w.link (3 * rawWriterAt w start reroute) = some next.1) ∧
      (∃ next,
        stepN w (right + 1) start = some next ∧
        w.link (3 * rawWriterAt w start right) = some next.1) := by
  obtain ⟨left, reroute, F, hprod, hdiff, hfirst, hshape⟩ :=
    h.open_rerouting_decomposition hN
  exact ⟨left, reroute, F, hprod, hdiff, hfirst, hshape,
    rawProductiveAt_fixed_stem_successor hN hprod,
    rawProductiveAt_fixed_stem_successor hN h.1⟩

/-- **EXACT REMAINING RAW SEMANTIC PROPOSITION.  OPEN.**

Start on the far endpoint of a known physical edge.  In every finite prefix,
at most four productive passes through an already-written switch can create
a tongue vector never seen earlier in that prefix.

The predicate contains no certificate, manufactured-object choice, period,
or asymptotic shorthand.  `rawRepeatedWriterNovelTimes` is literally the
list of event indices satisfying those three raw conditions.  By
`open_frame_with_fixed_stem_successors`, every event in this list already has
a fixed-stem fresh/interlacing rerouting frame.  The missing proof is exactly
that five such novel closing events cannot coexist in a known-edge run. -/
def KnownEdgeFourRepeatedWriterNovelty : Prop :=
  ∀ (w : Wiring) (N e : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (start : Nat × Tongues) (K : Nat),
      w.link e = some start.1 →
      (rawRepeatedWriterNovelTimes w N start K).length ≤ 4

/-- The exact four-event proposition gives the sharp known-edge `N+5`
count directly: first writers contribute at most `N+1` vectors, and the raw
repeated-writer list contributes at most four more. -/
theorem knownEdge_distinct_le_N_add_five_of_fourRepeatedWriterNovelty
    (hfour : KnownEdgeFourRepeatedWriterNovelty)
    (w : Wiring) (N e : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hentry : w.link e = some start.1)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 5 := by
  let K := maxRawTime times
  have htimes : ∀ k, k ∈ times → k ≤ K := by
    intro k hk
    exact le_maxRawTime_of_mem hk
  have hbudget :
      (rawRepeatedWriterNovelTimes w N start K).length ≤ 4 :=
    hfour w N e hN start K hentry
  have hcount := distinct_samples_le_of_repeated_writer_novelty
    w N hN start K 4 hbudget times htimes hnd
  omega

/-- The exact known-edge four-event proposition closes the public raw-track
`StateLaw`.  For an arbitrary start, time zero is separated off; after one
successful step the train is on the far endpoint of the known external edge
it just crossed, so the shifted positive-time sample has the `N+5` bound. -/
theorem stateLaw_of_knownEdgeFourRepeatedWriterNovelty
    (hfour : KnownEdgeFourRepeatedWriterNovelty) : StateLaw := by
  intro w N hN start times hlive hnd
  have htimesNodup : times.Nodup :=
    sharp_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  cases hstep : step w start with
  | none =>
      have hlt : ∀ k ∈ times, k < 1 := by
        intro k hk
        cases k with
        | zero => omega
        | succ k =>
            have hkLive := hlive (k+1) hk
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
        exact sharp_nodup_map_filter _ hnd
      have hshiftedNodup :
          (shifted.map (restrictedTonguesAt w N next)).Nodup := by
        rw [hshiftVector]
        exact hpositiveNodup
      have hentry : w.link (exitPort start) = some next.1 :=
        (step_some_parts hstep).1
      have hshiftedBound : shifted.length ≤ N + 5 :=
        knownEdge_distinct_le_N_add_five_of_fourRepeatedWriterNovelty
          hfour w N (exitPort start) hN next shifted hentry
            hshiftedNodup
      have hpositiveLength : positive.length = shifted.length := by
        simp [shifted]
      have hzeroBound :
          (times.filter (fun k => decide (k = 0))).length ≤ 1 :=
        sharp_zero_filter_length_le_one htimesNodup
      have hpartition := sharp_zero_positive_partition times
      dsimp [positive] at hpositiveLength
      omega

end GeneralN
