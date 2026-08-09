import TrackNoveltyCover

/-!
# The finite repeated-writer target

This file states the sharp finite-prefix interface directly over the raw
lazy-point dynamics. There is no periodic-tail premise.

A productive event is a live raw step whose restricted tongue vector changes.
Its writer is the switch entered at the start of that step. A writer is
`first` at its first productive event. A repeated-writer novelty is a later
productive event of the same switch whose resulting restricted tongue vector
has never occurred at any earlier raw time.

The exact remaining structural claim is that there are at most five such
events. The theorem `stateLaw_of_fiveRepeatedWriterNovelty` below proves,
without any further dynamical assumption, that this claim implies the open
`GeneralN.StateLaw` bound `N + 6`:

* one initial vector;
* at most `N` first productive writers;
* at most five repeated-writer novelties.

Thus the constant-five claim is not called a lemma hiding another important
gap: it is named as the complete remaining endpoint/matching theorem.
-/

namespace GeneralN

/-- The entry port at raw time `k`; the default is irrelevant whenever the
run is live at that time. -/
def rawEntryAt (w : Wiring) (start : Nat × Tongues) (k : Nat) : Nat :=
  ((stepN w k start).getD start).1

/-- The switch written by a productive raw step at time `k`. -/
def rawWriterAt (w : Wiring) (start : Nat × Tongues) (k : Nat) : Nat :=
  rawEntryAt w start k / 3

/-- A live raw step changes the visible `N`-switch tongue vector. -/
def RawProductiveAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : Prop :=
  (stepN w (k+1) start).isSome ∧
  restrictedTonguesAt w N start (k+1) ≠
    restrictedTonguesAt w N start k

/-- This is the first productive occurrence of its writer. -/
def RawFirstWriterAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : Prop :=
  RawProductiveAt w N start k ∧
  ∀ j, j < k → RawProductiveAt w N start j →
    rawWriterAt w start j ≠ rawWriterAt w start k

/-- The post-step vector at `k+1` has not appeared at any earlier raw time. -/
def RawNovelAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : Prop :=
  restrictedTonguesAt w N start (k+1) ∉
    (List.range (k+1)).map (restrictedTonguesAt w N start)

/-- A novel productive event whose writer was already productive earlier. -/
def RawRepeatedWriterNovelAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : Prop :=
  RawProductiveAt w N start k ∧
  ¬ RawFirstWriterAt w N start k ∧
  RawNovelAt w N start k

noncomputable def rawFirstWriterTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (List.range K).filter
    (fun k => decide (RawFirstWriterAt w N start k))

noncomputable def rawRepeatedWriterNovelTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (List.range K).filter
    (fun k => decide (RawRepeatedWriterNovelAt w N start k))

/-- Productive repeated-writer times, without assuming their post-vectors
are new.  On a duplicate-free prefix these are exactly the events in the
user's compressed formulation. -/
noncomputable def rawRepeatedWriterTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (List.range K).filter (fun k => decide
    (RawProductiveAt w N start k ∧
      ¬ RawFirstWriterAt w N start k))

theorem mem_rawFirstWriterTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawFirstWriterTimes w N start K ↔
      k < K ∧ RawFirstWriterAt w N start k := by
  classical
  simp [rawFirstWriterTimes]

theorem mem_rawRepeatedWriterNovelTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawRepeatedWriterNovelTimes w N start K ↔
      k < K ∧ RawRepeatedWriterNovelAt w N start k := by
  classical
  simp [rawRepeatedWriterNovelTimes]

theorem mem_rawRepeatedWriterTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawRepeatedWriterTimes w N start K ↔
      k < K ∧ RawProductiveAt w N start k ∧
        ¬ RawFirstWriterAt w N start k := by
  classical
  simp [rawRepeatedWriterTimes]

/-- **THE FINITE ALTERNATION TARGET. OPEN.**

In every finite raw prefix, at most five productive events both revisit a
previously productive writer and create a globally new restricted tongue
vector. This is the exact matching/endpoint theorem sought by the sharp
proof; it quantifies over arbitrary `N`, arbitrary symmetric wirings, every
start, and every finite horizon. -/
def FiveRepeatedWriterNovelty : Prop :=
  ∀ (w : Wiring) (N : Nat),
    (∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N) →
    ∀ (start : Nat × Tongues) (K : Nat),
      (rawRepeatedWriterNovelTimes w N start K).length ≤ 5

private theorem nodup_filter_nat (p : Nat → Bool) :
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
          exact ⟨fun hmem => hnd.1 ((List.mem_filter.mp hmem).1),
            ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem nodup_map_of_injective_on_raw
    {α : Type} [BEq α] [LawfulBEq α]
    {f : Nat → α} {xs : List Nat}
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y)
    (hnd : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
        have hxy := hinj x List.mem_cons_self y
          (List.mem_cons_of_mem _ hy) hfy.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih
          (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb)) hnd.2

private theorem nodup_subset_length_raw
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

private theorem map_nodup_injective_on_raw
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    {f : α → β} {xs : List α}
    (hnd : (xs.map f).Nodup) :
    ∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y := by
  induction xs with
  | nil =>
      intro x hx
      cases hx
  | cons a rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      intro x hx y hy hxy
      rcases List.mem_cons.mp hx with rfl | hxRest
      · rcases List.mem_cons.mp hy with rfl | hyRest
        · rfl
        · exfalso
          apply hnd.1
          apply List.mem_map.mpr
          exact ⟨y, hyRest, hxy.symm⟩
      · rcases List.mem_cons.mp hy with rfl | hyRest
        · exfalso
          apply hnd.1
          apply List.mem_map.mpr
          exact ⟨x, hxRest, hxy⟩
        · exact ih hnd.2 x hxRest y hyRest hxy

/-- Every visible novelty is necessarily a live productive event. -/
theorem rawNovelAt_productive
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {k : Nat}
    (hnovel : RawNovelAt w N start k) :
    RawProductiveAt w N start k := by
  constructor
  · cases hnext : stepN w (k+1) start with
    | some next => simp
    | none =>
        exfalso
        apply hnovel
        apply List.mem_map.mpr
        refine ⟨0, List.mem_range.mpr (by omega), ?_⟩
        calc
          restrictedTonguesAt w N start 0 =
              VectorCount.restrict N start.2 := by
            simp [restrictedTonguesAt, tonguesAt, stepN]
          _ = restrictedTonguesAt w N start (k+1) := by
            simp [restrictedTonguesAt, tonguesAt, hnext]
  · intro heq
    apply hnovel
    apply List.mem_map.mpr
    refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
    exact heq.symm

/-- Two novel events cannot create the same post-step tongue vector.  This
is purely temporal: whichever event occurs second would see the first
event's post-vector in its own history. -/
theorem rawNovelAt_post_injective
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {i j : Nat}
    (hi : RawNovelAt w N start i)
    (hj : RawNovelAt w N start j)
    (hvector : restrictedTonguesAt w N start (i+1) =
      restrictedTonguesAt w N start (j+1)) :
    i = j := by
  by_cases hij : i = j
  · exact hij
  · by_cases hlt : i < j
    · exfalso
      apply hj
      apply List.mem_map.mpr
      exact ⟨i+1, List.mem_range.mpr (by omega), hvector⟩
    · have hgt : j < i := by omega
      exfalso
      apply hi
      apply List.mem_map.mpr
      exact ⟨j+1, List.mem_range.mpr (by omega), hvector.symm⟩

/-- On a raw prefix whose complete restricted tongue-vector list is
duplicate-free, every productive repeated-writer event is globally novel at
that point. -/
theorem repeatedWriterAt_novel_of_distinct_prefix
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues}
    (hk : k < K)
    (hnd : ((List.range (K+1)).map
      (restrictedTonguesAt w N start)).Nodup)
    (hrepeat : RawProductiveAt w N start k ∧
      ¬ RawFirstWriterAt w N start k) :
    RawRepeatedWriterNovelAt w N start k := by
  refine ⟨hrepeat.1, hrepeat.2, ?_⟩
  intro hseen
  obtain ⟨j, hj, hvector⟩ := List.mem_map.mp hseen
  have hjlt : j < k+1 := List.mem_range.mp hj
  have heq : j = k+1 := map_nodup_injective_on_raw hnd
    j (List.mem_range.mpr (by omega))
    (k+1) (List.mem_range.mpr (by omega)) hvector
  omega

/-- **Literal distinct-prefix form requested by the endpoint argument.**
Assuming the stronger global constant-five target, a prefix with no repeated
restricted tongue vector contains at most five productive occurrences of an
already productive writer. -/
theorem distinct_prefix_repeated_writers_le_five
    (hfive : FiveRepeatedWriterNovelty)
    {w : Wiring} {N K : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    (start : Nat × Tongues)
    (hnd : ((List.range (K+1)).map
      (restrictedTonguesAt w N start)).Nodup) :
    (rawRepeatedWriterTimes w N start K).length ≤ 5 := by
  classical
  have htimesNodup : (rawRepeatedWriterTimes w N start K).Nodup := by
    unfold rawRepeatedWriterTimes
    exact nodup_filter_nat _ List.nodup_range
  have hsubset : ∀ k, k ∈ rawRepeatedWriterTimes w N start K →
      k ∈ rawRepeatedWriterNovelTimes w N start K := by
    intro k hk
    have hdata := mem_rawRepeatedWriterTimes_iff.mp hk
    apply mem_rawRepeatedWriterNovelTimes_iff.mpr
    exact ⟨hdata.1,
      repeatedWriterAt_novel_of_distinct_prefix hdata.1 hnd
        ⟨hdata.2.1, hdata.2.2⟩⟩
  have hle := nodup_subset_length_raw htimesNodup hsubset
  exact Nat.le_trans hle (hfive w N hN start K)

/-- A productive raw writer belongs to one of the `N` physical switches. -/
theorem rawProductiveAt_writer_lt
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    rawWriterAt w start k < N := by
  cases hnext : stepN w (k+1) start with
  | none =>
      have hlive := hprod.1
      simp [hnext] at hlive
  | some next =>
      have hsplit := stepN_add w k 1 start
      rw [hnext] at hsplit
      cases hcur : stepN w k start with
      | none => simp [hcur] at hsplit
      | some cur =>
          rw [hcur] at hsplit
          have hone : stepN w 1 cur = some next := by
            simpa using hsplit.symm
          have hstep : step w cur = some next := by
            simpa [stepN] using hone
          have hparts := step_some_parts hstep
          have hexit : exitPort cur < 3*N :=
            (hN (exitPort cur) next.1 hparts.1).1
          have hswitch := arrive_exit_switch cur.2 cur.1
          unfold rawWriterAt rawEntryAt
          simp [hcur]
          unfold exitPort at hexit
          omega

/-- First productive writers are injective by their switch label. -/
theorem rawFirstWriterAt_injective
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {i j : Nat}
    (hi : RawFirstWriterAt w N start i)
    (hj : RawFirstWriterAt w N start j)
    (hwriter : rawWriterAt w start i = rawWriterAt w start j) :
    i = j := by
  by_cases hij : i = j
  · exact hij
  · by_cases hlt : i < j
    · exact (hj.2 i hlt hi.1 hwriter).elim
    · have hgt : j < i := by omega
      exact (hi.2 j hgt hj.1 hwriter.symm).elim

/-- There are at most `N` first productive writer events in any prefix. -/
theorem rawFirstWriterTimes_length_le
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    (start : Nat × Tongues) (K : Nat) :
    (rawFirstWriterTimes w N start K).length ≤ N := by
  classical
  let times := rawFirstWriterTimes w N start K
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact nodup_filter_nat
      (fun k => decide (RawFirstWriterAt w N start k))
      List.nodup_range
  have hmapNodup : (times.map (rawWriterAt w start)).Nodup := by
    apply nodup_map_of_injective_on_raw
    · intro i hi j hj hEq
      have hiFilter : i ∈ (List.range K).filter
          (fun k => decide (RawFirstWriterAt w N start k)) := by
        simpa [times, rawFirstWriterTimes] using hi
      have hjFilter : j ∈ (List.range K).filter
          (fun k => decide (RawFirstWriterAt w N start k)) := by
        simpa [times, rawFirstWriterTimes] using hj
      have hiFirst : RawFirstWriterAt w N start i :=
        of_decide_eq_true (List.mem_filter.mp hiFilter).2
      have hjFirst : RawFirstWriterAt w N start j :=
        of_decide_eq_true (List.mem_filter.mp hjFilter).2
      exact rawFirstWriterAt_injective hiFirst hjFirst hEq
    · exact htimesNodup
  have hlt : ∀ C, C ∈ times.map (rawWriterAt w start) → C < N := by
    intro C hC
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hC
    have hkFilter : k ∈ (List.range K).filter
        (fun t => decide (RawFirstWriterAt w N start t)) := by
      simpa [times, rawFirstWriterTimes] using hk
    have hkFirst : RawFirstWriterAt w N start k :=
      of_decide_eq_true (List.mem_filter.mp hkFilter).2
    exact rawProductiveAt_writer_lt hN hkFirst.1
  have hle := nodup_nat_lt_length hmapNodup hlt
  simpa only [List.length_map] using hle

/-- Initial vector plus first-writer post-vectors. -/
noncomputable def rawFirstWriterHistory
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List (List Bool) :=
  restrictedTonguesAt w N start 0 ::
    (rawFirstWriterTimes w N start K).map
      (fun k => restrictedTonguesAt w N start (k+1))

/-- Post-vectors of the repeated-writer novelties. -/
noncomputable def rawRepeatedWriterFresh
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List (List Bool) :=
  (rawRepeatedWriterNovelTimes w N start K).map
    (fun k => restrictedTonguesAt w N start (k+1))

/-- Absolute post-step times of all repeated-writer novelty events in the
prefix.  This is the time list to which local reflector novelty-cover
theorems are applied. -/
noncomputable def rawRepeatedWriterPostTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat :=
  (rawRepeatedWriterNovelTimes w N start K).map (fun k => k+1)

theorem rawRepeatedWriterNovelTimes_nodup
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawRepeatedWriterNovelTimes w N start K).Nodup := by
  classical
  unfold rawRepeatedWriterNovelTimes
  exact nodup_filter_nat
    (fun k => decide (RawRepeatedWriterNovelAt w N start k))
    List.nodup_range

/-- The post-vectors of repeated-writer novelty events are themselves
duplicate-free. -/
theorem rawRepeatedWriterFresh_nodup
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawRepeatedWriterFresh w N start K).Nodup := by
  classical
  unfold rawRepeatedWriterFresh
  apply nodup_map_of_injective_on_raw
  · intro i hi j hj hvector
    have hiEvent : RawRepeatedWriterNovelAt w N start i :=
      (mem_rawRepeatedWriterNovelTimes_iff.mp hi).2
    have hjEvent : RawRepeatedWriterNovelAt w N start j :=
      (mem_rawRepeatedWriterNovelTimes_iff.mp hj).2
    exact rawNovelAt_post_injective hiEvent.2.2 hjEvent.2.2 hvector
  · exact rawRepeatedWriterNovelTimes_nodup w N start K

/-- Sampling the run at `rawRepeatedWriterPostTimes` gives exactly
`rawRepeatedWriterFresh`. -/
theorem map_repeatedWriterPostTimes_eq_fresh
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawRepeatedWriterPostTimes w N start K).map
      (restrictedTonguesAt w N start) =
        rawRepeatedWriterFresh w N start K := by
  simp [rawRepeatedWriterPostTimes, rawRepeatedWriterFresh, List.map_map]

/-- A novelty cover whose sampled vectors are all genuinely absent from its
history spends only its exceptional budget; the history contributes zero to
the count. -/
theorem noveltyCoverOn_fresh_distinct_count
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times : List Nat} {history : List (List Bool)} {budget : Nat}
    (hcover : NoveltyCoverOn w N start times history budget)
    (hnew : ∀ k ∈ times,
      restrictedTonguesAt w N start k ∉ history)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ budget := by
  obtain ⟨fresh, hfresh, hmem⟩ := hcover
  have hsubset : ∀ x ∈ times.map (restrictedTonguesAt w N start),
      x ∈ fresh := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    rcases List.mem_append.mp (hmem k hk) with hhistory | hfreshMem
    · exact (hnew k hk hhistory).elim
    · exact hfreshMem
  have hbound : times.length ≤ fresh.length := by
    simpa only [List.length_map] using
      (nodup_subset_length_raw hnd hsubset)
  omega

/-- Every state up to `K` is initial, the post-state of a first writer, or
the post-state of a repeated-writer novelty. -/
theorem restrictedTonguesAt_mem_finite_writer_cover
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    ∀ k, k ≤ K →
      restrictedTonguesAt w N start k ∈
        rawFirstWriterHistory w N start K ++
          rawRepeatedWriterFresh w N start K := by
  classical
  have main : ∀ bound k, k ≤ bound → bound ≤ K →
      restrictedTonguesAt w N start k ∈
        rawFirstWriterHistory w N start K ++
          rawRepeatedWriterFresh w N start K := by
    intro bound
    induction bound with
    | zero =>
        intro k hk _hK
        have hk0 : k = 0 := by omega
        subst k
        simp [rawFirstWriterHistory]
    | succ n ih =>
        intro k hk hboundK
        by_cases hkn : k ≤ n
        · exact ih k hkn (by omega)
        · have hkEq : k = n+1 := by omega
          subst k
          by_cases hnovel : RawNovelAt w N start n
          · have hprod := rawNovelAt_productive hnovel
            by_cases hfirst : RawFirstWriterAt w N start n
            · apply List.mem_append_left
              apply List.mem_cons_of_mem
              apply List.mem_map.mpr
              refine ⟨n, ?_, rfl⟩
              have hnK : n < K := by omega
              simp [rawFirstWriterTimes, hnK, hfirst]
            · apply List.mem_append_right
              apply List.mem_map.mpr
              refine ⟨n, ?_, rfl⟩
              have hnK : n < K := by omega
              have hrepeat : RawRepeatedWriterNovelAt w N start n :=
                ⟨hprod, hfirst, hnovel⟩
              simp [rawRepeatedWriterNovelTimes, hnK, hrepeat]
          · have hseen : restrictedTonguesAt w N start (n+1) ∈
                (List.range (n+1)).map
                  (restrictedTonguesAt w N start) := by
              exact Classical.not_not.mp hnovel
            obtain ⟨j, hj, hEq⟩ := List.mem_map.mp hseen
            have hjlt : j < n+1 := List.mem_range.mp hj
            rw [← hEq]
            exact ih j (by omega) (by omega)
  intro k hk
  exact main K k hk (Nat.le_refl _)

/-- Finite bookkeeping theorem: a budget `B` on repeated-writer novelties
gives `N + B + 1` distinct vectors, with no periodicity premise. -/
theorem distinct_samples_le_of_repeated_writer_novelty
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    (start : Nat × Tongues) (K B : Nat)
    (hbudget : (rawRepeatedWriterNovelTimes w N start K).length ≤ B)
    (times : List Nat) (htimes : ∀ k, k ∈ times → k ≤ K)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + B + 1 := by
  let history := rawFirstWriterHistory w N start K
  let fresh := rawRepeatedWriterFresh w N start K
  have hhistory : history.length ≤ N + 1 := by
    dsimp [history, rawFirstWriterHistory]
    simp only [List.length_map]
    have hfirst := rawFirstWriterTimes_length_le hN start K
    omega
  have hfresh : fresh.length ≤ B := by
    dsimp [fresh, rawRepeatedWriterFresh]
    simpa only [List.length_map] using hbudget
  have hcover : NoveltyCoverOn w N start times history B := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    exact restrictedTonguesAt_mem_finite_writer_cover
      w N start K k (htimes k hk)
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  omega

/-- Maximum of a finite list of raw times. -/
def maxRawTime : List Nat → Nat
  | [] => 0
  | k :: rest => max k (maxRawTime rest)

theorem le_maxRawTime_of_mem {k : Nat} :
    ∀ {times : List Nat}, k ∈ times → k ≤ maxRawTime times := by
  intro times hk
  induction times with
  | nil => cases hk
  | cons x rest ih =>
      rcases List.mem_cons.mp hk with rfl | hkRest
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hkRest) (Nat.le_max_right _ _)

/-- **Exact reduction of the open state law to the finite alternation
target.** Proving `FiveRepeatedWriterNovelty` proves `StateLaw`. -/
theorem stateLaw_of_fiveRepeatedWriterNovelty
    (hfive : FiveRepeatedWriterNovelty) : StateLaw := by
  intro w N hN start times _hlive hnd
  let K := maxRawTime times
  have htimes : ∀ k, k ∈ times → k ≤ K := by
    intro k hk
    exact le_maxRawTime_of_mem hk
  have hbudget :
      (rawRepeatedWriterNovelTimes w N start K).length ≤ 5 :=
    hfive w N hN start K
  have hcount := distinct_samples_le_of_repeated_writer_novelty
    w N hN start K 5 hbudget times htimes hnd
  omega

end GeneralN
