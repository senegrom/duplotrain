import RepeatedNoveltyDecomposition
import ConcreteTreeRetrace
import ReversalFacts
import EmptyCurvePotential

/-!
# Parametric falsification audit for the state law

This file tests the most direct coefficient-two counterfamily: a first sweep
of distinct productive writers followed by the same sweep again.  In an
arbitrary word of bit flips that would expose almost `2*N` distinct vectors.
The raw lazy-point dynamics forbid the required repeated adjacent pair.

Every productive write to a switch leaves through its unique stem edge, so
two productive occurrences of the same writer have the same next entry port.
If the following writer were also the same on both occasions, it would be
entered through the same branch.  That branch was selected by the first write;
unless the following writer is written again in the open interval, its second
arrival is unproductive.  Hence an `A,B,...,A,B` productive pattern forces a
third `B` in the gap.

This is a symbolic theorem for arbitrary `N`; it is not a finite search and it
does not assert the still-open `GeneralN.StateLaw`.
-/

namespace GeneralN

/-- Every prefix of a successful finite run is successful. -/
private theorem audit_stepN_prefix_some
    {w : Wiring} {start finish : Nat × Tongues} {d K : Nat}
    (hd : d ≤ K) (hfinish : stepN w K start = some finish) :
    ∃ middle, stepN w d start = some middle := by
  let rest := K - d
  have hsplit : K = d + rest := by
    dsimp [rest]
    omega
  rw [hsplit, stepN_add] at hfinish
  cases hprefix : stepN w d start with
  | none => simp [hprefix] at hfinish
  | some middle => exact ⟨middle, rfl⟩

/-- If one represented switch is not productively written on a live interval,
its tongue is unchanged across that interval. -/
private theorem audit_tongue_eq_of_no_writer_interval
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start finish : Nat × Tongues} {first span : Nat}
    (hfinish : stepN w (first + span) start = some finish)
    (hno : ∀ j, first ≤ j → j < first + span →
      RawProductiveAt w N start j → rawWriterAt w start j ≠ C) :
    (tonguesAt w start (first + span)) C =
      (tonguesAt w start first) C := by
  induction span generalizing finish with
  | zero => simp
  | succ n ih =>
      have harith : first + (n + 1) = first + n + 1 := by omega
      obtain ⟨middle, hmiddle⟩ := audit_stepN_prefix_some
        (d := first + n) (K := first + (n + 1)) (by omega) hfinish
      have hprev := ih hmiddle
        (fun j hj hbound hprod => hno j hj (by omega) hprod)
      have hlive : (stepN w (first + n + 1) start).isSome := by
        rw [← harith, hfinish]
        simp
      obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
        live_successor_configs hlive
      have hcurEq : cur = middle :=
        (Option.some.inj (hmiddle.symm.trans hcur)).symm
      subst cur
      have hfinish' : stepN w (first + n + 1) start = some finish := by
        rwa [← harith]
      have hnextEq : next = finish :=
        Option.some.inj (hnext.symm.trans hfinish')
      subst next
      have hbit : finish.2 C = middle.2 C := by
        apply Classical.byContradiction
        intro hchange
        obtain ⟨hprod, hwriter⟩ :=
          raw_tongue_change_is_productive_writer
            hC hmiddle hfinish' hstep hchange
        exact hno (first + n) (by omega) (by omega) hprod hwriter
      calc
        (tonguesAt w start (first + (n + 1))) C = finish.2 C := by
          rw [harith]
          simp [tonguesAt, hfinish']
        _ = middle.2 C := hbit
        _ = (tonguesAt w start (first + n)) C := by
          simp [tonguesAt, hmiddle]
        _ = (tonguesAt w start first) C := hprev

/-- A noduplicated list whose entries are all one fixed value has length at
most one. -/
private theorem audit_nodup_constant_length_le_one
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {xs : List alpha} {a : alpha}
    (hnd : xs.Nodup) (hconst : ∀ x ∈ xs, x = a) :
    xs.length ≤ 1 := by
  cases xs with
  | nil => simp
  | cons x rest =>
      rw [List.nodup_cons] at hnd
      have hrestNil : rest = [] := by
        cases rest with
        | nil => rfl
        | cons y ys =>
            have hx : x = a := hconst x List.mem_cons_self
            have hy : y = a := hconst y
              (List.mem_cons_of_mem _ List.mem_cons_self)
            exfalso
            apply hnd.1
            rw [hx, hy]
            exact List.mem_cons_self
      subst rest
      simp

/-- Generic finite-cover count, kept local to this audit file. -/
private theorem audit_nodup_subset_length
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    ∀ {xs cover : List alpha},
      xs.Nodup → (∀ x ∈ xs, x ∈ cover) →
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

/-- **Repeated productive pairs need a third write.**

Suppose productive writer `A` is followed immediately by productive writer
`B`, and later the same productive pair `A,B` occurs again.  Then `B` must be
productively written somewhere strictly between its two displayed
occurrences.  Thus the apparent two-pass word `A,B,...,A,B`, with `B` absent
from the gap, is impossible in every raw symmetric wiring.

This is the fixed-stem merge obstruction to the naive `1,2,...,N,1,2,...,N`
counterfamily. -/
theorem repeated_productive_pair_forces_intermediate_second_writer
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {first second : Nat}
    (hgap : first + 1 < second)
    (hfirst : RawProductiveAt w N start first)
    (hfirstNext : RawProductiveAt w N start (first + 1))
    (hsecond : RawProductiveAt w N start second)
    (hsecondNext : RawProductiveAt w N start (second + 1))
    (hsameOuter :
      rawWriterAt w start first = rawWriterAt w start second)
    (hsameInner :
      rawWriterAt w start (first + 1) =
        rawWriterAt w start (second + 1)) :
    ∃ t, first + 1 < t ∧ t < second + 1 ∧
      RawProductiveAt w N start t ∧
      rawWriterAt w start t = rawWriterAt w start (second + 1) := by
  apply Classical.byContradiction
  intro hnone
  have hno : ∀ t, first + 1 < t → t < second + 1 →
      RawProductiveAt w N start t →
      rawWriterAt w start t ≠ rawWriterAt w start (second + 1) := by
    intro t hleft hright hprod heq
    exact hnone ⟨t, hleft, hright, hprod, heq⟩
  obtain ⟨curFirst, nextFirst, CFirst, hCFirst, hcurFirst,
      hnextFirst, _hstepFirst, hentryFirst, _hexitFirst,
      hflipFirst, _hbackFirst⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hfirstNext
  obtain ⟨curSecond, _nextSecond, CSecond, hCSecond, hcurSecond,
      _hnextSecond, _hstepSecond, hentrySecond, _hexitSecond,
      _hflipSecond, _hbackSecond⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hsecondNext
  let C := rawWriterAt w start (second + 1)
  have hCFirstEq : CFirst = C := by
    exact hCFirst.trans hsameInner
  have hCSecondEq : CSecond = C := hCSecond
  subst CFirst
  subst CSecond
  rw [hCFirstEq] at hentryFirst hflipFirst
  rw [hCSecondEq] at hentrySecond
  have hsameEntryRaw :=
    same_raw_writer_post_entries_eq hN hfirst hsecond hsameOuter
  have hsameEntry : curFirst.1 = curSecond.1 := by
    simpa [rawEntryAt, hcurFirst, hcurSecond] using hsameEntryRaw
  have hCLt : C < N := by
    exact rawProductiveAt_writer_lt hN hsecondNext
  let span := second + 1 - (first + 2)
  have hspan : first + 2 + span = second + 1 := by
    dsimp [span]
    omega
  have hstable : curSecond.2 C = nextFirst.2 C := by
    have h := audit_tongue_eq_of_no_writer_interval hCLt
      (first := first + 2) (span := span) (finish := curSecond)
      (by rw [hspan]; exact hcurSecond)
      (fun t hleft hright hprod => by
        intro heq
        exact hno t (by omega) (by omega) hprod heq)
    rw [hspan] at h
    simpa [tonguesAt, hcurSecond, hnextFirst] using h
  have hfirstValue : nextFirst.2 C = bval curFirst.1 := by
    rw [hflipFirst, hentryFirst]
    cases hbit : curFirst.2 C <;>
      simp [flipAt, unmatchedBranch, branchPort, bval, hbit]
  have hsecondOpposite : bval curSecond.1 = !(curSecond.2 C) := by
    rw [hentrySecond]
    cases hbit : curSecond.2 C <;>
      simp [unmatchedBranch, branchPort, bval, hbit]
  have himpossible : curSecond.2 C = !(curSecond.2 C) := by
    calc
      curSecond.2 C = nextFirst.2 C := hstable
      _ = bval curFirst.1 := hfirstValue
      _ = bval curSecond.1 := by rw [hsameEntry]
      _ = !(curSecond.2 C) := hsecondOpposite
  cases hbit : curSecond.2 C <;> simp [hbit] at himpossible

/-- **A repeated writer has one fixed immediate successor writer.**

All productive occurrences of writer `A` leave through `A`'s unique stem
edge.  Therefore the raw entry port one step later is identical, and hence so
is the switch coordinate visited one step later.  In particular a literal
productive-word pattern `A,B,A,C` with `B ≠ C` cannot occur when the displayed
letters are consecutive raw steps. -/
theorem same_productive_writer_forces_same_immediate_successor_writer
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {i j : Nat}
    (hi : RawProductiveAt w N start i)
    (hj : RawProductiveAt w N start j)
    (hsame : rawWriterAt w start i = rawWriterAt w start j) :
    rawWriterAt w start (i + 1) =
      rawWriterAt w start (j + 1) := by
  have hentry := same_raw_writer_post_entries_eq hN hi hj hsame
  exact congrArg (fun p => p / 3) hentry

/-- Parametric form of the `ABA-new-C` obstruction: no number of productive
visits to one hub writer can expose different writers on their immediately
following raw steps. -/
theorem repeated_hub_immediate_successor_writer_constant
    {w : Wiring} {N hub : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} (hubTime : Nat → Nat)
    (hproductive : ∀ r, RawProductiveAt w N start (hubTime r))
    (hhub : ∀ r, rawWriterAt w start (hubTime r) = hub) :
    ∀ r s,
      rawWriterAt w start (hubTime r + 1) =
        rawWriterAt w start (hubTime s + 1) := by
  intro r s
  apply same_productive_writer_forces_same_immediate_successor_writer
    hN (hproductive r) (hproductive s)
  exact (hhub r).trans (hhub s).symm

/-- **No direct two-sweep counterfamily.**

Let a block of `width` consecutive productive events have pairwise-distinct
writers, and suppose the immediately following block repeats those writers in
the same order, with every event still productive.  For every `width ≥ 2` this
is impossible.

This is the fully parametric rejection of the natural near-`2*N` candidate
`1,2,...,N,1,2,...,N`.  The proof does not enumerate any width: it applies the
repeated-pair obstruction to the first two writers. -/
theorem no_productive_direct_double_sweep
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {base width : Nat}
    (hwidth : 2 ≤ width)
    (hproductive : ∀ d, d < 2 * width →
      RawProductiveAt w N start (base + d))
    (hrepeat : ∀ d, d < width →
      rawWriterAt w start (base + d) =
        rawWriterAt w start (base + width + d))
    (hfirstInjective : ∀ i j, i < width → j < width →
      rawWriterAt w start (base + i) =
        rawWriterAt w start (base + j) → i = j) :
    False := by
  have hOne : 1 < width := by omega
  have hZero : 0 < width := by omega
  obtain ⟨t, htLeft, htRight, _htProductive, htWriter⟩ :=
    repeated_productive_pair_forces_intermediate_second_writer
      hN (first := base) (second := base + width)
      (by omega)
      (by simpa using hproductive 0 (by omega))
      (by simpa [Nat.add_assoc] using hproductive 1 (by omega))
      (by simpa [Nat.add_assoc] using hproductive width (by omega))
      (by simpa [Nat.add_assoc] using
        hproductive (width + 1) (by omega))
      (by simpa [Nat.add_assoc] using hrepeat 0 hZero)
      (by simpa [Nat.add_assoc] using hrepeat 1 hOne)
  have hTarget :
      rawWriterAt w start (base + width + 1) =
        rawWriterAt w start (base + 1) := by
    exact (hrepeat 1 hOne).symm
  let d := t - base
  have htEq : t = base + d := by
    dsimp [d]
    omega
  have hdOne : 1 < d := by
    dsimp [d]
    omega
  have hdLe : d ≤ width := by
    dsimp [d]
    omega
  have hdWriter :
      rawWriterAt w start (base + d) =
        rawWriterAt w start (base + 1) := by
    rw [← htEq]
    exact htWriter.trans hTarget
  by_cases hdLt : d < width
  · have hEq := hfirstInjective d 1 hdLt hOne hdWriter
    omega
  · have hdEq : d = width := by omega
    have hdWriterWidth :
        rawWriterAt w start (base + width) =
          rawWriterAt w start (base + 1) := by
      rw [← hdEq]
      exact hdWriter
    have hBaseWriter :
        rawWriterAt w start (base + 0) =
          rawWriterAt w start (base + 1) := by
      exact (hrepeat 0 hZero).trans (by simpa using hdWriterWidth)
    have hEq := hfirstInjective 0 1 hZero hOne hBaseWriter
    omega

/-! ## Exact cancellation of the nested writer extremal -/

/-- Apply a finite word of productive writer flips. -/
def auditApplyWriters (u : Tongues) : List Nat → Tongues
  | [] => u
  | writer :: rest => auditApplyWriters (flipAt u writer) rest

/-- Writer-word execution respects concatenation. -/
theorem auditApplyWriters_append (u : Tongues) (left right : List Nat) :
    auditApplyWriters u (left ++ right) =
      auditApplyWriters (auditApplyWriters u left) right := by
  induction left generalizing u with
  | nil => rfl
  | cons writer rest ih =>
      simpa [auditApplyWriters] using
        ih (u := flipAt u writer)

/-- A word followed by the same writers in reverse order restores the exact
tongue vector.  No commutativity assumption is used: this is genuine stack
cancellation. -/
theorem auditApplyWriters_reverse_cancel (u : Tongues) :
    ∀ writers,
      auditApplyWriters (auditApplyWriters u writers) writers.reverse = u := by
  intro writers
  induction writers generalizing u with
  | nil => rfl
  | cons writer rest ih =>
      simp only [auditApplyWriters, List.reverse_cons]
      rw [auditApplyWriters_append]
      rw [ih (u := flipAt u writer)]
      simp [auditApplyWriters, flipAt_flipAt]

/-- **Every nested close replays an earlier opening vector.**

Split the opening writer stack into `before ++ stillOpen`.  After all writers
have opened, closing exactly `stillOpen` in reverse order returns to the
vector which existed just after `before`.  This is the arbitrary-depth
`A1,A2,...,Am,Am,...,A2,A1` cancellation theorem. -/
theorem nested_writer_split_replay
    (u : Tongues) (before stillOpen : List Nat) :
    auditApplyWriters
        (auditApplyWriters u (before ++ stillOpen)) stillOpen.reverse =
      auditApplyWriters u before := by
  rw [auditApplyWriters_append]
  exact auditApplyWriters_reverse_cancel
    (auditApplyWriters u before) stillOpen

/-- Opening-prefix vectors of one writer stack. -/
def auditOpeningStates (u : Tongues) : List Nat → List Tongues
  | [] => [u]
  | writer :: rest => u :: auditOpeningStates (flipAt u writer) rest

/-- Complete state list of a properly nested writer stack: open the head,
run the nested body, then close the head. -/
def auditNestedStates (u : Tongues) : List Nat → List Tongues
  | [] => [u]
  | writer :: rest =>
      u :: (auditNestedStates (flipAt u writer) rest ++ [u])

/-- Every vector on the complete nested trajectory already occurred on its
opening half. -/
theorem auditNestedStates_mem_opening
    (u : Tongues) (writers : List Nat) :
    ∀ v, v ∈ auditNestedStates u writers →
      v ∈ auditOpeningStates u writers := by
  induction writers generalizing u with
  | nil =>
      intro v hv
      simpa [auditNestedStates, auditOpeningStates] using hv
  | cons writer rest ih =>
      intro v hv
      simp only [auditNestedStates, auditOpeningStates,
        List.mem_cons] at hv ⊢
      rcases hv with hhead | htail
      · exact Or.inl hhead
      · rcases List.mem_append.mp htail with hinner | hreturn
        · exact Or.inr (ih (flipAt u writer) v hinner)
        · have hvu : v = u := by simpa using hreturn
          exact Or.inl hvu

theorem auditOpeningStates_length (u : Tongues) (writers : List Nat) :
    (auditOpeningStates u writers).length = writers.length + 1 := by
  induction writers generalizing u with
  | nil => rfl
  | cons writer rest ih =>
      simp [auditOpeningStates, ih (flipAt u writer)]

/-- **Global distinct-state bound for the complete nested extremal.**

`samples` may contain any distinct restricted tongue vectors selected from
the complete open-then-LIFO-close trajectory.  Every such vector is covered
by the `writers.length + 1` opening-prefix vectors, so the closing half has
zero novelty budget. -/
theorem nested_writer_distinct_vectors_le_length_succ
    (N : Nat) (u : Tongues) (writers : List Nat)
    (samples : List (List Bool))
    (hnd : samples.Nodup)
    (hfrom : ∀ x ∈ samples,
      x ∈ (auditNestedStates u writers).map
        (VectorCount.restrict N)) :
    samples.length ≤ writers.length + 1 := by
  let cover := (auditOpeningStates u writers).map
    (VectorCount.restrict N)
  have hsub : ∀ x ∈ samples, x ∈ cover := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (hfrom x hx)
    apply List.mem_map.mpr
    exact ⟨v, auditNestedStates_mem_opening u writers v hv, rfl⟩
  have hle := audit_nodup_subset_length hnd hsub
  dsimp [cover] at hle
  rw [List.length_map, auditOpeningStates_length] at hle
  exact hle

/-- With distinct represented writers below `N`, the complete nested
trajectory has at most `N+1` distinct restricted tongue vectors. -/
theorem nested_writer_distinct_vectors_le_N_succ
    (N : Nat) (u : Tongues) (writers : List Nat)
    (hwriters : writers.Nodup)
    (hbounded : ∀ writer ∈ writers, writer < N)
    (samples : List (List Bool))
    (hnd : samples.Nodup)
    (hfrom : ∀ x ∈ samples,
      x ∈ (auditNestedStates u writers).map
        (VectorCount.restrict N)) :
    samples.length ≤ N + 1 := by
  have hstates := nested_writer_distinct_vectors_le_length_succ
    N u writers samples hnd hfrom
  have hwritersLength : writers.length ≤ N :=
    bounded_cell_list_length_le hwriters hbounded
  omega

/-! ## The nested push/pop audit -/

/-- **Every prefix of a cascade retrace is tongue-quiet.**

The original `retrace` theorem identifies the endpoint of a complete reverse
traversal.  For state counting we need the stronger prefix statement: while
the train pops an arbitrarily long cascade, *every intermediate raw state*
has exactly the tongue vector with which the pop began.

This is fully parametric in the cascade length.  In particular, a push of
`k` distinct lazy switches followed by the mechanically forced reverse pop
cannot contribute another `k` tongue vectors: the whole pop contributes only
the already-present vector `u`. -/
theorem retrace_prefix_tongues_unchanged
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    ∀ ell : Nat, w.link ell = some p →
    ∀ u : Tongues, Agrees u (p :: ps) →
    ∀ d, d ≤ (p :: ps).length →
      ∃ q, stepN w d (3 * (lastOf p ps / 3), u) = some (q, u) := by
  induction h with
  | @last t p s hp hlink hs =>
      intro ell hentry u hagree d hd
      have hdCases : d = 0 ∨ d = 1 := by
        simp only [List.length_cons, List.length_nil] at hd
        omega
      rcases hdCases with rfl | rfl
      · exact ⟨3 * (lastOf p [] / 3), rfl⟩
      · let hD : Descent w t p [] s (pin t p) :=
          Descent.last hp hlink hs
        exact ⟨ell, retrace hD ell hentry u hagree⟩
  | @cons t p p' s ps t' hp hlink hp' hrest ih =>
      intro ell hentry u hagree d hd
      have htail : Agrees u (p' :: ps) := by
        intro b hb
        exact hagree b (List.mem_cons_of_mem _ hb)
      by_cases hprefix : d ≤ (p' :: ps).length
      · obtain ⟨q, hq⟩ :=
          ih (3 * (p / 3)) hlink u htail d hprefix
        exact ⟨q, by simpa [lastOf] using hq⟩
      · have hdFull : d = (p :: p' :: ps).length := by
          have hlen : (p :: p' :: ps).length =
              (p' :: ps).length + 1 := by simp
          rw [hlen] at hd ⊢
          omega
        subst d
        let hD : Descent w t p (p' :: ps) s t' :=
          Descent.cons hp hlink hp' hrest
        exact ⟨ell, retrace hD ell hentry u hagree⟩

/-- **Arbitrarily nested other-tree traffic still has a quiet pop.**

`entries` may contain any finite number of inner cascade pushes, of any
sizes, provided they belong to other root trees.  Those pushes can modify the
tongue vector.  Once the train returns to the outer frame, however, every
prefix of its forced reverse traversal preserves that complete modified
vector exactly.

This is the raw `Wiring`/`stepN` obstruction to obtaining a coefficient-two
family from nested push/pop permutations.  A putative construction must
re-enter and overwrite an open root frame; an untouched stack pop supplies no
new switch vector. -/
theorem nested_retrace_prefixes_are_tongue_quiet
    {w : Wiring} {t : Tongues} {p s ell : Nat}
    {ps : List Nat} {t' : Tongues}
    (hd : Descent w t p ps s t')
    (hentry : w.link ell = some p)
    (entries : List Nat)
    (hentries : ∀ q ∈ entries, IsDescentEntry w q)
    (hroots : ∀ q ∈ entries,
      entryRoot w p ≠ entryRoot w q) :
    ∀ d, d ≤ (p :: ps).length →
      ∃ q,
        stepN w d
            (3 * (lastOf p ps / 3), runEntryActions w entries t') =
          some (q, runEntryActions w entries t') := by
  apply retrace_prefix_tongues_unchanged hd ell hentry
  exact descent_result_survives_other_roots hd entries hentries hroots

/-- **A nested closing half contributes at most one distinct vector.**

All sample times may be chosen adversarially and the cascade may have
arbitrary length.  Since every closing prefix has the same tongue vector, a
`Nodup` sample of closing-half vectors has length at most one.  This is the
counting form of the cancellation obstruction needed for the nested
`A1,A2,...,Am,Am,...,A2,A1` extremal word. -/
theorem nested_retrace_nodup_vectors_le_one
    {w : Wiring} {t : Tongues} {p s ell : Nat}
    {ps : List Nat} {t' : Tongues}
    (hd : Descent w t p ps s t')
    (hentry : w.link ell = some p)
    (entries : List Nat)
    (hentries : ∀ q ∈ entries, IsDescentEntry w q)
    (hroots : ∀ q ∈ entries,
      entryRoot w p ≠ entryRoot w q)
    (N : Nat) (times : List Nat)
    (htimes : ∀ d ∈ times, d ≤ (p :: ps).length)
    (hnd : (times.map (restrictedTonguesAt w N
      (3 * (lastOf p ps / 3), runEntryActions w entries t'))).Nodup) :
    times.length ≤ 1 := by
  have hconst : ∀ x ∈ times.map (restrictedTonguesAt w N
      (3 * (lastOf p ps / 3), runEntryActions w entries t')),
      x = VectorCount.restrict N (runEntryActions w entries t') := by
    intro x hx
    obtain ⟨d, hdMem, rfl⟩ := List.mem_map.mp hx
    obtain ⟨q, hq⟩ := nested_retrace_prefixes_are_tongue_quiet
      hd hentry entries hentries hroots d (htimes d hdMem)
    simp [restrictedTonguesAt, tonguesAt, hq]
  have hbound := audit_nodup_constant_length_le_one hnd hconst
  simpa using hbound

end GeneralN

namespace Echo

/-! The same obstruction at the compiled cell level. -/

/-- **A frame whose stored arrow is unchanged has only its mirror return.**

The real liveness invariant is register equality, not absence of re-entry.
After the transition at `openTime`, even arbitrary later traffic through the
arrival cell is harmless provided that, at `closeTime`, its register has the
same value it had immediately after opening.  A visit to the mirror of that
cell must then leave through the mirror of the frame's source. -/
theorem live_frame_mirror_return_is_forced
    {m : Machine} {e r0 : Nat → Nat}
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {openTime closeTime : Nat}
    (hregister :
      reg m e r0 closeTime (m.cellOf (e (openTime + 1))) =
        reg m e r0 (openTime + 1) (m.cellOf (e (openTime + 1))))
    (hmirror : m.cellOf (e closeTime) =
      m.star (m.cellOf (e (openTime + 1)))) :
    m.cellOf (e (closeTime + 1)) =
      m.star (m.cellOf (e openTime)) := by
  have hopenWrite :
      reg m e r0 (openTime + 1) (m.cellOf (e (openTime + 1))) =
        e (openTime + 1) :=
    reg_write m e r0 rfl
  have hnext : e (closeTime + 1) = m.bar (e (openTime + 1)) := by
    rw [hrun closeTime, hmirror, m.star_invol, hregister, hopenWrite]
  calc
    m.cellOf (e (closeTime + 1)) =
        m.cellOf (m.bar (e (openTime + 1))) := congrArg m.cellOf hnext
    _ = m.star (m.cellOf (e openTime)) :=
      (witness m e r0 hrun hr0 openTime).1

/-- The older no-re-entry formulation is a direct corollary of register
stability.  It is retained only as a convenient way to establish the stronger
register invariant above. -/
theorem no_reentry_live_frame_mirror_return_is_forced
    {m : Machine} {e r0 : Nat → Nat}
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {openTime closeTime : Nat}
    (horder : openTime + 1 ≤ closeTime)
    (hlive : ∀ l, openTime + 1 < l → l ≤ closeTime →
      m.cellOf (e l) ≠ m.cellOf (e (openTime + 1)))
    (hmirror : m.cellOf (e closeTime) =
      m.star (m.cellOf (e (openTime + 1)))) :
    m.cellOf (e (closeTime + 1)) =
      m.star (m.cellOf (e openTime)) := by
  let d := closeTime - (openTime + 1)
  have hclose : openTime + 1 + d = closeTime := by
    dsimp [d]
    omega
  apply live_frame_mirror_return_is_forced hrun hr0
  · rw [← hclose]
    apply reg_stable
    intro l hlo hhi
    apply hlive l hlo
    rwa [hclose] at hhi
  · exact hmirror

/-- **Non-LIFO routing must overwrite the open frame.**

Contrapositive of the register-level live-frame law: if a later visit to the
mirror of the arrival cell does not return to the mirror of the source, then
that arrival cell's register changed.  `change_has_productive_le` turns this
into a *productive* write of precisely the open frame cell.  Thus a nested
construction may depart from stack order only by spending a state-changing
overwrite; a merely unproductive re-entry cannot pay for non-LIFO routing. -/
theorem non_lifo_return_forces_frame_overwrite
    {m : Machine} {e r0 : Nat → Nat}
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {openTime closeTime : Nat}
    (horder : openTime + 1 ≤ closeTime)
    (hmirror : m.cellOf (e closeTime) =
      m.star (m.cellOf (e (openTime + 1))))
    (hwrong : m.cellOf (e (closeTime + 1)) ≠
      m.star (m.cellOf (e openTime))) :
    ∃ t, openTime + 1 ≤ t ∧ t < closeTime ∧
      ProductiveStep m e r0 t ∧
      m.cellOf (e (t + 1)) = m.cellOf (e (openTime + 1)) := by
  have hregister :
      reg m e r0 closeTime (m.cellOf (e (openTime + 1))) ≠
        reg m e r0 (openTime + 1) (m.cellOf (e (openTime + 1))) := by
    intro heq
    exact hwrong (live_frame_mirror_return_is_forced
      hrun hr0 heq hmirror)
  exact change_has_productive_le m e r0 horder hregister

/-- Pointwise, arbitrary-depth version: every non-LIFO return in a family of
open frames has a concrete productive overwrite of that frame cell. -/
theorem nested_non_lifo_returns_each_force_overwrite
    {m : Machine} {e r0 : Nat → Nat}
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (openTime closeTime : Nat → Nat)
    (horder : ∀ n, openTime n + 1 ≤ closeTime n)
    (hmirror : ∀ n, m.cellOf (e (closeTime n)) =
      m.star (m.cellOf (e (openTime n + 1))))
    (hwrong : ∀ n, m.cellOf (e (closeTime n + 1)) ≠
      m.star (m.cellOf (e (openTime n)))) :
    ∀ n, ∃ t, openTime n + 1 ≤ t ∧ t < closeTime n ∧
      ProductiveStep m e r0 t ∧
      m.cellOf (e (t + 1)) = m.cellOf (e (openTime n + 1)) := by
  intro n
  exact non_lifo_return_forces_frame_overwrite
    hrun hr0 (horder n) (hmirror n) (hwrong n)

/-- **Distinct non-LIFO live frames have distinct productive charges.**

For an arbitrary family of wrong mirror returns, choose a productive overwrite
supplied by `non_lifo_return_forces_frame_overwrite`.  If the open
frame cells are pairwise distinct on `frames`, their chosen overwrite times
are pairwise distinct as well: one productive step writes only one cell.

This is the injective accounting statement needed by a global stack proof.
It also exposes the remaining truth-audit risk precisely: a coefficient-two
family would have to recycle the *same frame cell*, not merely branch among
many distinct open frames. -/
theorem distinct_non_lifo_frames_have_injective_productive_charge
    {m : Machine} {e r0 : Nat → Nat}
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (openTime closeTime : Nat → Nat)
    (horder : ∀ n, openTime n + 1 ≤ closeTime n)
    (hmirror : ∀ n, m.cellOf (e (closeTime n)) =
      m.star (m.cellOf (e (openTime n + 1))))
    (hwrong : ∀ n, m.cellOf (e (closeTime n + 1)) ≠
      m.star (m.cellOf (e (openTime n))))
    (frames : List Nat)
    (hframeCells : ∀ i ∈ frames, ∀ j ∈ frames,
      m.cellOf (e (openTime i + 1)) =
        m.cellOf (e (openTime j + 1)) → i = j) :
    ∃ charge : Nat → Nat,
      (∀ n ∈ frames,
        openTime n + 1 ≤ charge n ∧ charge n < closeTime n ∧
        ProductiveStep m e r0 (charge n) ∧
        m.cellOf (e (charge n + 1)) =
          m.cellOf (e (openTime n + 1))) ∧
      (∀ i ∈ frames, ∀ j ∈ frames, charge i = charge j → i = j) := by
  have hwitness : ∀ n, ∃ t,
      openTime n + 1 ≤ t ∧ t < closeTime n ∧
      ProductiveStep m e r0 t ∧
      m.cellOf (e (t + 1)) = m.cellOf (e (openTime n + 1)) :=
    nested_non_lifo_returns_each_force_overwrite
      hrun hr0 openTime closeTime horder hmirror hwrong
  let charge : Nat → Nat := fun n => Classical.choose (hwitness n)
  have hcharge : ∀ n,
      openTime n + 1 ≤ charge n ∧ charge n < closeTime n ∧
      ProductiveStep m e r0 (charge n) ∧
      m.cellOf (e (charge n + 1)) =
        m.cellOf (e (openTime n + 1)) := by
    intro n
    exact Classical.choose_spec (hwitness n)
  refine ⟨charge, ?_, ?_⟩
  · intro n _hn
    exact hcharge n
  · intro i hi j hj hij
    apply hframeCells i hi j hj
    calc
      m.cellOf (e (openTime i + 1)) =
          m.cellOf (e (charge i + 1)) := (hcharge i).2.2.2.symm
      _ = m.cellOf (e (charge j + 1)) := by rw [hij]
      _ = m.cellOf (e (openTime j + 1)) := (hcharge j).2.2.2

end Echo

namespace GeneralN

/-! ## Coefficient-one state accounting before self-contact -/

/-- The initial vector together with every post-productive vector in a raw
prefix.  Quiet steps are omitted because they do not change the represented
tongue vector. -/
noncomputable def auditProductiveVectorCover
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List (List Bool) :=
  restrictedTonguesAt w N start 0 ::
    (rawProductiveCurveTimes w N start K).map
      (fun k => restrictedTonguesAt w N start (k + 1))

/-- **Every raw-prefix vector is initial or follows a productive write.**

This is the exact bridge from event accounting to state accounting.  It has
no non-self hypothesis: nonproductive steps are collapsed using
`restrictedTonguesAt_succ_eq_of_not_productive`. -/
theorem raw_prefix_vector_mem_productive_cover
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {K : Nat}
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome) :
    ∀ k, k ≤ K →
      restrictedTonguesAt w N start k ∈
        auditProductiveVectorCover w N start K := by
  intro k hk
  unfold auditProductiveVectorCover
  induction k with
  | zero =>
      exact List.mem_cons_self
  | succ j ih =>
      by_cases hprod : RawProductiveAt w N start j
      · apply List.mem_cons_of_mem _
        apply List.mem_map.mpr
        refine ⟨j, ?_, rfl⟩
        exact mem_rawProductiveCurveTimes_iff.mpr ⟨by omega, hprod⟩
      · have heq := restrictedTonguesAt_succ_eq_of_not_productive
          (hlive (j + 1) hk) hprod
        rw [heq]
        exact ih (by omega)

/-- **Unconditional state-to-event accounting.**

Any noduplicated sample from a live prefix has at most one more vector than
the number of productive writes in that prefix.  This is an actual bound on
raw switch vectors, not a conditional replay interface. -/
theorem raw_prefix_distinct_vectors_le_productive_succ
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {K : Nat}
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (times : List Nat)
    (htimes : ∀ k ∈ times, k ≤ K)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤
      (rawProductiveCurveTimes w N start K).length + 1 := by
  have hsub : ∀ x ∈ times.map (restrictedTonguesAt w N start),
      x ∈ auditProductiveVectorCover w N start K := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact raw_prefix_vector_mem_productive_cover
      hlive k (htimes k hk)
  have hle := audit_nodup_subset_length hnd hsub
  simpa only [List.length_map, auditProductiveVectorCover,
    List.length_cons] using hle

/-- **Coefficient one for every all-non-self raw prefix.**

If every productive contact in a live prefix grows the empty-curve carrier
rather than hitting its own curve, then *all* distinct switch vectors in the
prefix number at most `N+1`.  This combines the unconditional state cover
above with `nonself_productive_times_le_N`. -/
theorem nonself_prefix_distinct_vectors_le_N_succ
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (hnonself : ∀ k, k < K → RawProductiveAt w N start k →
      ¬ RawCurveSelfAt w start k)
    (times : List Nat)
    (htimes : ∀ k ∈ times, k ≤ K)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 1 := by
  have hstates := raw_prefix_distinct_vectors_le_productive_succ
    hlive times htimes hnd
  have hproductive := nonself_productive_times_le_N
    hN start K hlive hnonself
  omega

/-- **Any super-`N+1` state family must use a raw self-contact.**

This is the falsification-audit boundary.  A parametric branching construction
with more than `N+1` distinct vectors cannot consist only of fresh/non-self
pushes; it must exhibit a concrete productive pivot back into its currently
selected curve.  Pure double sweeps and pure nested pops are therefore not
counterfamilies. -/
theorem more_than_N_succ_distinct_vectors_forces_self_contact
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (times : List Nat)
    (htimes : ∀ k ∈ times, k ≤ K)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup)
    (hmore : N + 1 < times.length) :
    ∃ k, k < K ∧ RawProductiveAt w N start k ∧
      RawCurveSelfAt w start k := by
  have hstates := raw_prefix_distinct_vectors_le_productive_succ
    hlive times htimes hnd
  have hproductive :
      N < (rawProductiveCurveTimes w N start K).length := by
    omega
  exact more_than_N_productive_forces_self_contact
    hN start K hlive hproductive

end GeneralN
