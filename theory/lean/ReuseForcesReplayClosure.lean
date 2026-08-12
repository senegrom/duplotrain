import SelfPivotStrictShrink

/-!
# What reuse of a discarded curve port really forces

`ReusedNovelStrictShrinkPortForcesReplay` asks for a *global* tongue-vector
replay when two strict self-shrinks discard the same physical curve port.
The local curve argument does not, by itself, freeze switches outside the
discarded component.  This file therefore proves the strongest raw
consequence available before any such global-freezing theorem is supplied.

If a port is absent immediately after one shrink and belongs to the train
curve again before a later shrink, there is a first step restoring that
port.  That step is necessarily a productive non-self pivot and hence a
strict curve-growth event.  Its state contribution has an exhaustive raw
trichotomy:

* it is the first productive write of its switch;
* its post-vector already occurred earlier; or
* it is an earlier repeated-writer novelty.

The final section makes the global-state issue explicit.  If a later vector
does not replay the first-restoration vector, some represented coordinate
which differs between them has a named productive writer in the intervening
raw interval.  Thus outside activity is not silently assumed away.

Everything here is general in `N` and stated over `Wiring`/`stepN`.  The file
does **not** assert `ReusedNovelStrictShrinkPortForcesReplay` or `StateLaw`.
-/

namespace GeneralN

/-! ## First restoration of one discarded physical port -/

/-- The first transition from `¬ P` to `P` in a nonempty finite interval.
The returned prefix is still entirely outside `P`. -/
private theorem first_false_true_transition
    (P : Nat → Prop) [DecidablePred P] :
    ∀ (a span : Nat), 0 < span → ¬ P a → P (a + span) →
      ∃ r, a ≤ r ∧ r < a + span ∧
        (∀ t, a ≤ t → t ≤ r → ¬ P t) ∧ P (r + 1) := by
  intro a span
  induction span generalizing a with
  | zero =>
      intro hpositive
      omega
  | succ n ih =>
      intro _hpositive ha hlast
      by_cases hnext : P (a + 1)
      · refine ⟨a, Nat.le_refl _, by omega, ?_, hnext⟩
        intro t hat hta
        have htaeq : t = a := by omega
        simpa [htaeq] using ha
      · cases n with
        | zero =>
            have hcontr : P (a + 1) := by simpa using hlast
            exact (hnext hcontr).elim
        | succ n =>
            have hlast' : P ((a + 1) + (n + 1)) := by
              have harith : (a + 1) + (n + 1) =
                  a + (n + 1 + 1) := by omega
              rw [harith]
              exact hlast
            obtain ⟨r, har, hrend, habsent, hrestore⟩ :=
              ih (a + 1) (by omega) hnext hlast'
            refine ⟨r, by omega, by omega, ?_, hrestore⟩
            intro t hat htr
            by_cases htaeq : t = a
            · subst t
              exact ha
            · exact habsent t (by omega) htr

/-- Every prefix of a successful raw run is successful. -/
private theorem prefix_isSome_of_later_isSome
    {w : Wiring} {start : Nat × Tongues} {d K : Nat}
    (hd : d ≤ K) (hK : (stepN w K start).isSome) :
    (stepN w d start).isSome := by
  obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hK
  let rest := K - d
  have hsplit : K = d + rest := by
    dsimp [rest]
    omega
  rw [hsplit, stepN_add] at hfinish
  cases hprefix : stepN w d start with
  | none => simp [hprefix] at hfinish
  | some middle => simp

/-- A concrete first restoration of one physical carrier port.  The port is
absent throughout `[afterDrop, restore]`, appears at `restore + 1`, and the
restoring transition is a strict non-self curve growth. -/
structure RawFirstPortRestoration
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (afterDrop restore p : Nat) : Prop where
  afterDrop_le_restore : afterDrop ≤ restore
  absent_through : ∀ t, afterDrop ≤ t → t ≤ restore →
    p ∉ rawFiniteCurvePortsAt w N start t
  restored_next : p ∈ rawFiniteCurvePortsAt w N start (restore + 1)
  productive : RawProductiveAt w N start restore
  nonself : ¬ RawCurveSelfAt w start restore
  strict_growth :
    rawFiniteCurveSizeAt w N start restore <
      rawFiniteCurveSizeAt w N start (restore + 1)

/-- **First-restoration extraction.**  Reappearance of a port discarded at
time `i` forces a concrete productive non-self event strictly before the
later time `j`.  No recurrence, novelty, planarity, or periodicity premise
is used. -/
theorem dropped_port_reuse_has_first_restoration
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {i j p : Nat}
    (hij : i < j)
    (hlater : (stepN w (j + 1) start).isSome)
    (hlost : p ∉ rawFiniteCurvePortsAt w N start (i + 1))
    (hreused : p ∈ rawFiniteCurvePortsAt w N start j) :
    ∃ restore, restore < j ∧
      RawFirstPortRestoration w N start (i + 1) restore p := by
  classical
  have hgap : i + 1 < j := by
    by_cases heq : i + 1 = j
    · subst j
      exact (hlost hreused).elim
    · omega
  let P : Nat → Prop := fun t =>
    p ∈ rawFiniteCurvePortsAt w N start t
  let span := j - (i + 1)
  have hspan : 0 < span := by
    dsimp [span]
    omega
  have hsum : i + 1 + span = j := by
    dsimp [span]
    omega
  have hnotP : ¬ P (i + 1) := by
    simpa [P] using hlost
  have hlastP : P (i + 1 + span) := by
    simpa [P, hsum] using hreused
  obtain ⟨restore, hafter, hbeforeJ, habsent, hrestored⟩ :=
    first_false_true_transition P (i + 1) span hspan hnotP hlastP
  have hrestoreLt : restore < j := by simpa [hsum] using hbeforeJ
  have hliveRestore : (stepN w (restore + 1) start).isSome :=
    prefix_isSome_of_later_isSome (by omega) hlater
  have hrestoredMem :
      p ∈ rawFiniteCurvePortsAt w N start (restore + 1) := by
    simpa [P] using hrestored
  have habsentMem : ∀ t, i + 1 ≤ t → t ≤ restore →
      p ∉ rawFiniteCurvePortsAt w N start t := by
    intro t hlo hhi
    simpa [P] using habsent t hlo hhi
  have hproductive : RawProductiveAt w N start restore := by
    apply Classical.byContradiction
    intro hquiet
    have hback := raw_nonproductive_carrier_subset
      hN hliveRestore hquiet p hrestoredMem
    exact habsentMem restore hafter (Nat.le_refl _) hback
  have hnonself : ¬ RawCurveSelfAt w start restore := by
    intro hself
    have hback := raw_self_pivot_carrier_subset
      hN hproductive hself p hrestoredMem
    exact habsentMem restore hafter (Nat.le_refl _) hback
  refine ⟨restore, hrestoreLt, {
    afterDrop_le_restore := hafter
    absent_through := habsentMem
    restored_next := hrestoredMem
    productive := hproductive
    nonself := hnonself
    strict_growth := rawProductiveAt_nonself_curve_growth
      hN hproductive hnonself
  }⟩

/-! ## Exhaustive state contribution of the restoring event -/

/-- The restoring non-self pivot is paid for in exactly one of three raw
ways: a first writer, a replaying post-vector, or an earlier repeated-writer
novelty. -/
inductive RawFirstPortRestorationOutcome
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (restore : Nat) : Prop where
  | firstWriter
      (h : RawFirstWriterAt w N start restore) :
      RawFirstPortRestorationOutcome w N start restore
  | earlierReplay
      (h : restrictedTonguesAt w N start (restore + 1) ∈
        (List.range (restore + 1)).map
          (restrictedTonguesAt w N start)) :
      RawFirstPortRestorationOutcome w N start restore
  | earlierRepeatedNovelty
      (h : RawRepeatedWriterNovelAt w N start restore) :
      RawFirstPortRestorationOutcome w N start restore

/-- The first restoring event has the exhaustive first/replay/repeated-novel
trichotomy.  This is where an attempted global lost-port injection must pay
for restoration activity; it cannot simply declare outside tongues frozen. -/
theorem RawFirstPortRestoration.outcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {afterDrop restore p : Nat}
    (F : RawFirstPortRestoration w N start afterDrop restore p) :
    RawFirstPortRestorationOutcome w N start restore := by
  classical
  by_cases hfirst : RawFirstWriterAt w N start restore
  · exact RawFirstPortRestorationOutcome.firstWriter hfirst
  · by_cases hnovel : RawNovelAt w N start restore
    · exact RawFirstPortRestorationOutcome.earlierRepeatedNovelty
        ⟨F.productive, hfirst, hnovel⟩
    · have hseen : restrictedTonguesAt w N start (restore + 1) ∈
          (List.range (restore + 1)).map
            (restrictedTonguesAt w N start) := by
        apply Classical.byContradiction
        intro hmissing
        exact hnovel hmissing
      exact RawFirstPortRestorationOutcome.earlierReplay hseen

/-- **Two reused strict-shrink frames: unconditional closure.**  Under the
ordinary bounded-wiring hypothesis, all local consequences of reusing the
same discarded port are discharged by a first strict non-self restoration
and the preceding exhaustive trichotomy.

Unlike `ReusedNovelStrictShrinkPortForcesReplay`, this theorem does not turn
local carrier restoration into an unsupported global-vector equality. -/
theorem reused_novel_strict_shrink_port_restoration_trichotomy
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {i j p : Nat}
    (hij : i < j)
    (_hi : RawNovelRepeatedStrictShrinkAt w N start i)
    (hj : RawNovelRepeatedStrictShrinkAt w N start j)
    (_hpOldI : p ∈ rawFiniteCurvePortsAt w N start i)
    (hpLostI : p ∉ rawFiniteCurvePortsAt w N start (i + 1))
    (hpOldJ : p ∈ rawFiniteCurvePortsAt w N start j)
    (_hpLostJ : p ∉ rawFiniteCurvePortsAt w N start (j + 1)) :
    ∃ restore,
      i < restore ∧ restore < j ∧
      RawFirstPortRestoration w N start (i + 1) restore p ∧
      RawFirstPortRestorationOutcome w N start restore := by
  obtain ⟨restore, hrestoreJ, F⟩ :=
    dropped_port_reuse_has_first_restoration hN hij
      hj.1.1.1 hpLostI hpOldJ
  have hiRestore : i < restore := by
    have hafter := F.afterDrop_le_restore
    omega
  exact ⟨restore, hiRestore, hrestoreJ, F, F.outcome⟩

/-! ## The precise global-state gap -/

/-- Inequality of represented vectors names a differing represented
coordinate. -/
private theorem restrict_ne_has_coordinate_reuse
    {N : Nat} {u v : Tongues}
    (hne : VectorCount.restrict N u ≠ VectorCount.restrict N v) :
    ∃ C, C < N ∧ u C ≠ v C := by
  apply Classical.byContradiction
  intro hnone
  apply hne
  unfold VectorCount.restrict
  apply List.map_congr_left
  intro C hC
  apply Classical.byContradiction
  intro hneC
  exact hnone ⟨C, List.mem_range.mp hC, hneC⟩

/-- If coordinate `C` is never productively written on a live half-open
interval, its tongue is unchanged across that interval. -/
private theorem tongue_eq_of_no_writer_interval_reuse
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start finish : Nat × Tongues} {first span : Nat}
    (hfinish : stepN w (first + span) start = some finish)
    (hno : ∀ t, first ≤ t → t < first + span →
      RawProductiveAt w N start t → rawWriterAt w start t ≠ C) :
    (tonguesAt w start (first + span)) C =
      (tonguesAt w start first) C := by
  induction span generalizing finish with
  | zero => simp
  | succ n ih =>
      have hprefixSome : (stepN w (first + n) start).isSome :=
        prefix_isSome_of_later_isSome
          (d := first + n) (K := first + n + 1) (by omega) (by
          have harith : first + (n + 1) = first + n + 1 := by omega
          rw [← harith, hfinish]
          simp)
      obtain ⟨middle, hmiddle⟩ := Option.isSome_iff_exists.mp hprefixSome
      have hprev := ih hmiddle
        (fun t hfirst hbound hprod => hno t hfirst (by omega) hprod)
      have hlive : (stepN w (first + n + 1) start).isSome := by
        have harith : first + (n + 1) = first + n + 1 := by omega
        rw [← harith, hfinish]
        simp
      obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
        live_successor_configs hlive
      have hcurEq : cur = middle := by
        exact (Option.some.inj (hmiddle.symm.trans hcur)).symm
      subst cur
      have hfinish' : stepN w (first + n + 1) start = some finish := by
        have harith : first + (n + 1) = first + n + 1 := by omega
        rwa [← harith]
      have hnextEq : next = finish := by
        exact Option.some.inj (hnext.symm.trans hfinish')
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
          simp [tonguesAt, hfinish]
        _ = middle.2 C := hbit
        _ = (tonguesAt w start (first + n)) C := by
          simp [tonguesAt, hmiddle]
        _ = (tonguesAt w start first) C := hprev

/-- A changed represented coordinate over a live interval has a concrete
productive write by that coordinate's switch in the interval. -/
theorem changed_coordinate_has_writer_between
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start finish : Nat × Tongues} {first span : Nat}
    (hfinish : stepN w (first + span) start = some finish)
    (hchange : (tonguesAt w start (first + span)) C ≠
      (tonguesAt w start first) C) :
    ∃ t, first ≤ t ∧ t < first + span ∧
      RawProductiveAt w N start t ∧ rawWriterAt w start t = C := by
  apply Classical.byContradiction
  intro hnone
  have hstable := tongue_eq_of_no_writer_interval_reuse hC hfinish
    (fun t hlo hhi hprod => by
      intro hwriter
      exact hnone ⟨t, hlo, hhi, hprod, hwriter⟩)
  exact hchange hstable

/-- **Global replay or named outside activity.**  Once a discarded port has
first been restored at `restore`, failure of a later global replay is not a
local curve fact: it names a represented switch productively written after
that restoration whose bit differs in the later vector. -/
theorem post_restoration_replay_or_named_writer
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {afterDrop restore p later : Nat}
    (_F : RawFirstPortRestoration w N start afterDrop restore p)
    (hrestoreLater : restore < later)
    (hlater : (stepN w (later + 1) start).isSome) :
    restrictedTonguesAt w N start (later + 1) ∈
        (List.range (later + 1)).map
          (restrictedTonguesAt w N start) ∨
      ∃ C t,
        C < N ∧ restore + 1 ≤ t ∧ t < later + 1 ∧
        RawProductiveAt w N start t ∧
        rawWriterAt w start t = C ∧
        (tonguesAt w start (later + 1)) C ≠
          (tonguesAt w start (restore + 1)) C := by
  classical
  by_cases hreplay : restrictedTonguesAt w N start (later + 1) ∈
      (List.range (later + 1)).map
        (restrictedTonguesAt w N start)
  · exact Or.inl hreplay
  · right
    have hvectorNe :
        restrictedTonguesAt w N start (later + 1) ≠
          restrictedTonguesAt w N start (restore + 1) := by
      intro heq
      apply hreplay
      apply List.mem_map.mpr
      exact ⟨restore + 1, List.mem_range.mpr (by omega), heq.symm⟩
    obtain ⟨C, hC, hbit⟩ :=
      restrict_ne_has_coordinate_reuse hvectorNe
    obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hlater
    let span := later - restore
    have hspan : restore + 1 + span = later + 1 := by
      dsimp [span]
      omega
    have hfinish' :
        stepN w (restore + 1 + span) start = some finish := by
      simpa [hspan] using hfinish
    have hchange :
        (tonguesAt w start (restore + 1 + span)) C ≠
          (tonguesAt w start (restore + 1)) C := by
      simpa [hspan] using hbit
    obtain ⟨t, htlo, hthi, htprod, htwriter⟩ :=
      changed_coordinate_has_writer_between hC hfinish' hchange
    exact ⟨C, t, hC, htlo, by simpa [hspan] using hthi,
      htprod, htwriter, hbit⟩

end GeneralN
