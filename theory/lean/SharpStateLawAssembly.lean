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

/-- Four pair-orbit vectors followed by the single strict-candy vector use
exactly the five exceptional slots available in the sharp accounting. -/
theorem four_pair_then_one_splice_five
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {pairTimes spliceTimes : List Nat}
    {history : List (List Bool)}
    (hpair : FourNoveltyCover w N start pairTimes history)
    (hsplice : NoveltyCoverOn w N start spliceTimes history 1) :
    FiveNoveltyCover w N start (pairTimes ++ spliceTimes) history := by
  exact four_cover_then_candy_splice_five hpair hsplice

/-- A history of size at most `N+1` and a five-vector novelty cover imply the
requested `N+6` count. -/
theorem fiveNoveltyCover_to_N_add_six
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times : List Nat} {history : List (List Bool)}
    (hhistory : history.length ≤ N + 1)
    (hcover : FiveNoveltyCover w N start times history)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  omega

/-- The concrete final assembly used by the global-repair proof.  The sample
times are partitioned into the four-corner manufactured-pair phase and the
one-vector strict-candy residual. -/
theorem pair_and_splice_distinct_le_N_add_six
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {pairTimes spliceTimes : List Nat}
    {history : List (List Bool)}
    (hhistory : history.length ≤ N + 1)
    (hpair : FourNoveltyCover w N start pairTimes history)
    (hsplice : NoveltyCoverOn w N start spliceTimes history 1)
    (hnd : ((pairTimes ++ spliceTimes).map
      (restrictedTonguesAt w N start)).Nodup) :
    (pairTimes ++ spliceTimes).length ≤ N + 6 := by
  apply fiveNoveltyCover_to_N_add_six hhistory
  · exact four_pair_then_one_splice_five hpair hsplice
  · exact hnd

/-- Novelty-annotated form of the last changed-forward flip case.

The strict-candy branch is completely discharged: it composes with an
existing four-corner cover to give the sharp five-vector exceptional cover.
The disjunction retains the *only* branch not covered by the candy theorem,
namely that the touched selected passage lies on the old runway. -/
theorem four_pair_then_changed_flip_five_or_runway
    {w : Wiring} {g e N : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R))
    (history : List (List Bool))
    (hleadHistorical : ∀ j, j ≤ A.toSupported.travel →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈ history)
    (pairTimes spliceTimes : List Nat)
    (hpair : FourNoveltyCover w N
      (g, (ManufacturedReflector.flip R).activatedState)
      pairTimes history) :
    (∃ entry mouth state,
      (entry, mouth) ∈
        (ManufacturedReflector.flip R).orientedRoute state ∧
      (entry, mouth) ∈ R.runway) ∨
    FiveNoveltyCover w N
      (g, (ManufacturedReflector.flip R).activatedState)
      (pairTimes ++ spliceTimes) history := by
  rcases hmerge.runway_or_candy_absolute_one_novelty
      N history hleadHistorical spliceTimes with hrunway | hcandy
  · exact Or.inl hrunway
  · exact Or.inr (four_pair_then_one_splice_five hpair hcandy)

/-- The changed-forward branch no longer has a runway residual.  The
pointwise runway/candy theorem covers every selected raw time by four vectors
above the supplied construction history.  Consequently an `N+1` known-edge
history gives the sharp `N+5` bound directly, without a route-length or
eventual-periodicity argument. -/
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

/-- A compatible pair needs only three *new* vectors when its starting
corner is already historical.  This is useful in the alternative
`N+2 + 3 + 1 = N+6` accounting. -/
theorem manufactured_pair_three_novelty_cover_of_start_mem
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    (times : List Nat) (history : List (List Bool))
    (hstart : VectorCount.restrict N state ∈ history) :
    NoveltyCoverOn w N (g, state) times history 3 := by
  let aState := A.toSupported.action.apply state
  let baState := B.toSupported.action.apply aState
  let abaState := A.toSupported.action.apply baState
  refine ⟨[VectorCount.restrict N aState,
      VectorCount.restrict N baState,
      VectorCount.restrict N abaState], by simp, ?_⟩
  intro k _hk
  have hphase := manufactured_pair_all_time_four_phase_tongues
    A B state hA hB hAB hBA k
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hphase
  rcases hphase with hstate | ha | hba | haba
  · apply List.mem_append_left
    simpa [restrictedTonguesAt, hstate] using hstart
  · apply List.mem_append_right history
    simp [restrictedTonguesAt, aState, ha]
  · apply List.mem_append_right history
    simp [restrictedTonguesAt, hba, baState, aState]
  · apply List.mem_append_right history
    simp [restrictedTonguesAt, haba, abaState, baState, aState]

/-- Three new manufactured-pair corners plus the one candy-splice vector are
a four-vector tail above an `N+2` history. -/
theorem three_pair_then_one_splice_four
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {pairTimes spliceTimes : List Nat}
    {history : List (List Bool)}
    (hpair : NoveltyCoverOn w N start pairTimes history 3)
    (hsplice : NoveltyCoverOn w N start spliceTimes history 1) :
    FourNoveltyCover w N start (pairTimes ++ spliceTimes) history := by
  have hcombined := noveltyCoverOn_append hpair hsplice
  simpa [FourNoveltyCover] using hcombined

/-- Alternative exact arithmetic: an `N+2` construction history, three new
pair corners, and one splice vector also give `N+6`. -/
theorem historical_start_pair_and_splice_distinct_le_N_add_six
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {pairTimes spliceTimes : List Nat}
    {history : List (List Bool)}
    (hhistory : history.length ≤ N + 2)
    (hpair : NoveltyCoverOn w N start pairTimes history 3)
    (hsplice : NoveltyCoverOn w N start spliceTimes history 1)
    (hnd : ((pairTimes ++ spliceTimes).map
      (restrictedTonguesAt w N start)).Nodup) :
    (pairTimes ++ spliceTimes).length ≤ N + 6 := by
  apply fourNoveltyCover_to_N_add_six hhistory
  · exact three_pair_then_one_splice_four hpair hsplice
  · exact hnd

/-- Canonical history for the first manufactured reflector: every outward
exploration vector, followed by the single activated vector carried by the
completed reverse runway. -/
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

/-- **Concrete sharp raw-track assembly.**

The first manufactured journey is charged to its canonical `N+2` history.
The continuation is partitioned into at most three new compatible-pair
corners and the one strict-candy vector.  Therefore all selected vectors in
the complete raw trajectory number at most `N+6`. -/
theorem manufacturing_then_pair_and_splice_distinct_le_N_add_six
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    (constructionTimes pairTimes spliceTimes : List Nat)
    (hconstruction : ∀ j ∈ constructionTimes,
      j ≤ A.exploration.length + A.runway.length + 1)
    (hpair : NoveltyCoverOn w N (g, A.baseState)
      pairTimes (A.sharpConstructionHistory N) 3)
    (hsplice : NoveltyCoverOn w N (g, A.baseState)
      spliceTimes (A.sharpConstructionHistory N) 1)
    (hnd : (((constructionTimes ++ pairTimes) ++ spliceTimes).map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    ((constructionTimes ++ pairTimes) ++ spliceTimes).length ≤ N + 6 := by
  have hfirst : NoveltyCoverOn w N (g, A.baseState)
      constructionTimes (A.sharpConstructionHistory N) 0 := by
    refine ⟨[], by simp, ?_⟩
    intro j hj
    simpa using A.manufacturing_journey_mem_sharpHistory
      hpaths (hconstruction j hj)
  have hfirstPair := noveltyCoverOn_append hfirst hpair
  have hall := noveltyCoverOn_append hfirstPair hsplice
  have hfour : FourNoveltyCover w N (g, A.baseState)
      ((constructionTimes ++ pairTimes) ++ spliceTimes)
      (A.sharpConstructionHistory N) := by
    simpa [FourNoveltyCover] using hall
  exact fourNoveltyCover_to_N_add_six
    (A.sharpConstructionHistory_length hN) hfour hnd

/-- A fully explicit certificate for the sharp global-repair accounting.

`history` contains the construction vectors.  `pairTimes` are covered by at
most three new manufactured-pair corners because the entering corner is
historical.  `spliceTimes` are covered by the one strict-candy vector.  The
time-list equation makes this a statement about every selected raw time,
not merely about endpoints or periods. -/
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

/-- Every sharp global-repair certificate proves the target count for its
raw sample list. -/
theorem SharpGlobalRepairCertificate.distinct_le_N_add_six
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times : List Nat}
    (C : SharpGlobalRepairCertificate w N start times)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  rw [C.times_eq] at hnd ⊢
  exact historical_start_pair_and_splice_distinct_le_N_add_six
    C.history_length C.pair_cover C.splice_cover hnd

/-- Known-edge version of the certificate.  Because the global physical
construction starts on the near side of an actual track edge, its history
budget is `N+1`; the four continuation slots then give the stronger `N+5`
bound. -/
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

/-- A known-edge certificate gives the sharp `N+5` count needed before the
single possible initial dangling-edge state is restored. -/
theorem KnownEdgeSharpRepairCertificate.distinct_le_N_add_five
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times : List Nat}
    (C : KnownEdgeSharpRepairCertificate w N start times)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 5 := by
  rw [C.times_eq] at hnd ⊢
  have hfour := three_pair_then_one_splice_four
    C.pair_cover C.splice_cover
  have hcount := fourNoveltyCover_distinct_count hfour hnd
  have hhistory := C.history_length
  omega

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

/-- **STRONGER STRUCTURAL CERTIFICATE LAW.  OPEN.**

Start the train on the near side of a known physical edge.  For every finite
selection of live raw times, the physical global-repair construction must
produce an `N+1` construction history, a three-corner manufactured-pair
part, and a one-vector splice part.

This certificate decomposition is stronger than the exact event bound above
and is no longer the preferred statement of the residual.  In particular,
`ChangedForwardMerge.runway_or_candy_absolute_four_novelty` has eliminated
the old runway/candy case completely.  What remains is the global bridge from
the fixed-stem open frames of arbitrary raw repeated novelties to at most four
tail vectors; that bridge is stated exactly by
`KnownEdgeFourRepeatedWriterNovelty`. -/
def KnownEdgeSharpRepairCertificateLaw : Prop :=
  ∀ (w : Wiring) (N e : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (start : Nat × Tongues) (times : List Nat),
      w.link e = some start.1 →
      (∀ k ∈ times, (stepN w k start).isSome) →
      Nonempty (KnownEdgeSharpRepairCertificate w N start times)

/-- Closing the known-edge certificate law closes the actual raw-track
`StateLaw`.  An arbitrary start either falls off immediately, or its first
successful step supplies the required known edge.  The former contributes
one vector; in the latter case time zero is the sole vector not represented
in the shifted known-edge sample, hence `N+5+1 = N+6`. -/
theorem stateLaw_of_knownEdgeSharpRepairCertificateLaw
    (hsharp : KnownEdgeSharpRepairCertificateLaw) : StateLaw := by
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
      have hshiftedLive : ∀ d ∈ shifted,
          (stepN w d next).isSome := by
        intro d hd
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
        have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
        have hkPos : 0 < k :=
          of_decide_eq_true (List.mem_filter.mp hk).2
        have hkEq : k = 1 + (k - 1) := by omega
        have hkLive := hlive k hkTimes
        rw [hkEq, stepN_add, hstepOne] at hkLive
        exact hkLive
      have hentry : w.link (exitPort start) = some next.1 :=
        (step_some_parts hstep).1
      obtain ⟨C⟩ := hsharp w N (exitPort start) hN next shifted
        hentry hshiftedLive
      have hshiftedBound : shifted.length ≤ N + 5 :=
        C.distinct_le_N_add_five hshiftedNodup
      have hpositiveLength : positive.length = shifted.length := by
        simp [shifted]
      have hzeroBound :
          (times.filter (fun k => decide (k = 0))).length ≤ 1 :=
        sharp_zero_filter_length_le_one htimesNodup
      have hpartition := sharp_zero_positive_partition times
      dsimp [positive] at hpositiveLength
      omega

end GeneralN
