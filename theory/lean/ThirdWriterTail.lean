import OverwriteDynamics
import FiveFrameObstruction
import TrackTrace
import ConcreteCascadeFacts
import TrackFiniteAlternation

/-!
# The third productive occurrence: restored mouth, foreign steering

This file tests a tempting sharp route directly over raw `Wiring`/`stepN`:
perhaps the third productive occurrence of one switch already forces a loop
or the four-state dogbone tail.

That statement is too strong.  Three productive occurrences of the same
writer do restore that writer's local bit, and all three leave through the
same immutable stem successor.  Nevertheless, a globally novel third
post-state can differ on other switches.  The exact obstruction is not an
opaque premise: the novel third occurrence forces a productive foreign
writer between the second and third occurrences.  That foreign writer is
either

* genuinely first (one first-writer charge), or
* itself repeated, with a last-writer frame interlacing the final frame of
  the original writer: `B < A < B < A`.

Thus the direct third-write tail claim reduces unconditionally to the
two-writer interlacing case.  Closing that `BABA` case to a dogbone or to a
new first-writer charge remains the sharp global step.
-/

namespace GeneralN

/-- Three *consecutive* productive occurrences of one writer, beginning at
that writer's first productive occurrence, whose third post-vector is
globally novel.  This is the literal raw form of "the third productive
occurrence of a switch". -/
structure RawThirdWriterNovelAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (first second third : Nat) : Prop where
  first_lt_second : first < second
  second_lt_third : second < third
  first_writer : RawFirstWriterAt w N start first
  second_productive : RawProductiveAt w N start second
  third_productive : RawProductiveAt w N start third
  same_first_second :
    rawWriterAt w start first = rawWriterAt w start second
  same_second_third :
    rawWriterAt w start second = rawWriterAt w start third
  no_same_first_second : ∀ t, first < t → t < second →
    RawProductiveAt w N start t →
    rawWriterAt w start t ≠ rawWriterAt w start second
  no_same_second_third : ∀ t, second < t → t < third →
    RawProductiveAt w N start t →
    rawWriterAt w start t ≠ rawWriterAt w start third
  third_novel : RawNovelAt w N start third

/-- The second and third occurrences form the actual last-writer frame of
the third occurrence. -/
theorem RawThirdWriterNovelAt.secondThirdFrame
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    RawLastWriterFrame w N start second third where
  order := T.second_lt_third
  open_productive := T.second_productive
  close_productive := T.third_productive
  same_writer := T.same_second_third
  no_same_writer_between := T.no_same_second_third

/-- The third occurrence is a repeated-writer novelty in the existing raw
finite-alternation language. -/
theorem RawThirdWriterNovelAt.repeatedNovel
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    RawRepeatedWriterNovelAt w N start third := by
  refine ⟨T.third_productive, ?_, T.third_novel⟩
  intro hfirst
  exact (hfirst.2 second T.second_lt_third T.second_productive
    T.same_second_third).elim

/-- All three productive occurrences leave through one immutable external
stem edge, hence have exactly the same post-write entry port. -/
theorem RawThirdWriterNovelAt.post_entries_eq
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    rawEntryAt w start (first+1) = rawEntryAt w start (second+1) ∧
      rawEntryAt w start (second+1) = rawEntryAt w start (third+1) := by
  constructor
  · exact same_raw_writer_post_entries_eq hN T.first_writer.1
      T.second_productive T.same_first_second
  · exact same_raw_writer_post_entries_eq hN T.second_productive
      T.third_productive T.same_second_third

/-- If one represented switch is not productively written on a live
half-open interval, its bit is unchanged across that interval.  This local
version is kept here because the corresponding helper in the decomposition
library is intentionally private. -/
private theorem thirdWriter_tongue_eq_of_no_writer_interval
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start finish : Nat × Tongues} {first span : Nat}
    (hfinish : stepN w (first+span) start = some finish)
    (hno : ∀ j, first ≤ j → j < first+span →
      RawProductiveAt w N start j → rawWriterAt w start j ≠ C) :
    (tonguesAt w start (first+span)) C =
      (tonguesAt w start first) C := by
  induction span generalizing finish with
  | zero => simp
  | succ n ih =>
      have harith : first + (n+1) = first+n+1 := by omega
      obtain ⟨middle, hmiddle⟩ := stepN_prefix_some
        (d := first+n) (K := first+(n+1)) (by omega) hfinish
      have hprev := ih hmiddle
        (fun j hj hbound hprod => hno j hj (by omega) hprod)
      have hlive : (stepN w (first+n+1) start).isSome := by
        rw [← harith, hfinish]
        simp
      obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
        live_successor_configs hlive
      have hcurEq : cur = middle :=
        (Option.some.inj (hmiddle.symm.trans hcur)).symm
      subst cur
      have hfinish' : stepN w (first+n+1) start = some finish := by
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
        exact hno (first+n) (by omega) (by omega) hprod hwriter
      calc
        (tonguesAt w start (first+(n+1))) C = finish.2 C := by
          rw [harith]
          simp [tonguesAt, hfinish']
        _ = middle.2 C := hbit
        _ = (tonguesAt w start (first+n)) C := by
          simp [tonguesAt, hmiddle]
        _ = (tonguesAt w start first) C := hprev

/-- Three consecutive flips of one writer restore, at the first and third
post-times, that writer's own bit.  Other writers may still differ. -/
theorem RawThirdWriterNovelAt.first_third_post_writer_bit_eq
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    (tonguesAt w start (first+1)) (rawWriterAt w start first) =
      (tonguesAt w start (third+1)) (rawWriterAt w start first) := by
  let C := rawWriterAt w start first
  have hC : C < N := rawProductiveAt_writer_lt hN T.first_writer.1
  obtain ⟨curI, nextI, CI, hCI, _hcurI, hnextI, _hstepI,
      _hentryI, _hexitI, _hflipI, _hbackI⟩ :=
    rawProductiveAt_is_endpoint_pivot hN T.first_writer.1
  obtain ⟨curJ, nextJ, CJ, hCJ, hcurJ, hnextJ, _hstepJ,
      _hentryJ, _hexitJ, hflipJ, _hbackJ⟩ :=
    rawProductiveAt_is_endpoint_pivot hN T.second_productive
  obtain ⟨curK, nextK, CK, hCK, hcurK, hnextK, _hstepK,
      _hentryK, _hexitK, hflipK, _hbackK⟩ :=
    rawProductiveAt_is_endpoint_pivot hN T.third_productive
  have hCJ' : CJ = C := by
    exact hCJ.trans T.same_first_second.symm
  have hCK' : CK = C := by
    exact hCK.trans
      (T.same_first_second.trans T.same_second_third).symm
  have hflipJ' : nextJ.2 = flipAt curJ.2 C := by
    simpa [hCJ'] using hflipJ
  have hflipK' : nextK.2 = flipAt curK.2 C := by
    simpa [hCK'] using hflipK
  let spanIJ := second - (first+1)
  have hsumIJ : first+1+spanIJ = second := by
    have horder := T.first_lt_second
    dsimp [spanIJ]
    omega
  have hstableIJ :
      (tonguesAt w start second) C =
        (tonguesAt w start (first+1)) C := by
    have h := thirdWriter_tongue_eq_of_no_writer_interval hC
      (first := first+1) (span := spanIJ) (finish := curJ)
      (by simpa [hsumIJ] using hcurJ)
      (fun t hlo hhi hprod => by
        intro heq
        exact T.no_same_first_second t (by omega) (by omega) hprod
          (heq.trans T.same_first_second))
    simpa [hsumIJ] using h
  let spanJK := third - (second+1)
  have hsumJK : second+1+spanJK = third := by
    have horder := T.second_lt_third
    dsimp [spanJK]
    omega
  have hCthird : C = rawWriterAt w start third :=
    T.same_first_second.trans T.same_second_third
  have hstableJK :
      (tonguesAt w start third) C =
        (tonguesAt w start (second+1)) C := by
    have h := thirdWriter_tongue_eq_of_no_writer_interval hC
      (first := second+1) (span := spanJK) (finish := curK)
      (by simpa [hsumJK] using hcurK)
      (fun t hlo hhi hprod => by
        intro heq
        exact T.no_same_second_third t (by omega) (by omega) hprod
          (heq.trans hCthird))
    simpa [hsumJK] using h
  have hstableIJ' : curJ.2 C = nextI.2 C := by
    simpa [tonguesAt, hcurJ, hnextI] using hstableIJ
  have hstableJK' : curK.2 C = nextJ.2 C := by
    simpa [tonguesAt, hcurK, hnextJ] using hstableJK
  have hJbit : nextJ.2 C = !(curJ.2 C) := by
    rw [hflipJ']
    simp [flipAt]
  have hKbit : nextK.2 C = !(curK.2 C) := by
    rw [hflipK']
    simp [flipAt]
  change (tonguesAt w start (first+1)) C =
    (tonguesAt w start (third+1)) C
  calc
    (tonguesAt w start (first+1)) C = nextI.2 C := by
      simp [tonguesAt, hnextI]
    _ = curJ.2 C := hstableIJ'.symm
    _ = !(!(curJ.2 C)) := by cases curJ.2 C <;> rfl
    _ = !(nextJ.2 C) := by rw [hJbit]
    _ = !(curK.2 C) := by rw [hstableJK']
    _ = nextK.2 C := hKbit.symm
    _ = (tonguesAt w start (third+1)) C := by
      simp [tonguesAt, hnextK]

/-- Novelty of the third post-vector makes it different from the first
post-vector. -/
theorem RawThirdWriterNovelAt.first_third_post_vector_ne
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    restrictedTonguesAt w N start (third+1) ≠
      restrictedTonguesAt w N start (first+1) := by
  intro heq
  apply T.third_novel
  apply List.mem_map.mpr
  have horder := Nat.lt_trans T.first_lt_second T.second_lt_third
  exact ⟨first+1, List.mem_range.mpr (by omega), heq.symm⟩

private theorem thirdWriter_restrict_ne_has_coordinate
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

/-- The globally novel third post-state differs from the first post-state on
some *other* represented switch.  The third writer's own bit is already
restored, so it cannot account for the novelty. -/
theorem RawThirdWriterNovelAt.has_foreign_post_bit
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    ∃ C, C < N ∧ C ≠ rawWriterAt w start first ∧
      (tonguesAt w start (third+1)) C ≠
        (tonguesAt w start (first+1)) C := by
  have hne :
      VectorCount.restrict N (tonguesAt w start (third+1)) ≠
        VectorCount.restrict N (tonguesAt w start (first+1)) := by
    simpa [restrictedTonguesAt] using T.first_third_post_vector_ne
  obtain ⟨C, hC, hdiff⟩ :=
    thirdWriter_restrict_ne_has_coordinate hne
  refine ⟨C, hC, ?_, hdiff⟩
  intro hsame
  subst C
  exact hdiff (T.first_third_post_writer_bit_eq hN).symm

/-- **Exact counterpattern to the naive third-write tail claim.**

At the first and third post-times the train is at the same physical entry
port and the repeated switch has the same tongue bit, but the represented
tongue vectors are different.  Hence the third occurrence is not yet an
exact repeated train configuration; its novelty is carried by foreign
switches. -/
theorem RawThirdWriterNovelAt.same_mouth_restored_but_foreign_state
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    ∃ firstPost thirdPost,
      stepN w (first+1) start = some firstPost ∧
      stepN w (third+1) start = some thirdPost ∧
      firstPost.1 = thirdPost.1 ∧
      firstPost.2 (rawWriterAt w start first) =
        thirdPost.2 (rawWriterAt w start first) ∧
      VectorCount.restrict N firstPost.2 ≠
        VectorCount.restrict N thirdPost.2 := by
  obtain ⟨firstPost, hfirstPost, _⟩ :=
    rawProductiveAt_fixed_stem_successor hN T.first_writer.1
  obtain ⟨thirdPost, hthirdPost, _⟩ :=
    rawProductiveAt_fixed_stem_successor hN T.third_productive
  have hentry := T.post_entries_eq hN
  have hport : firstPost.1 = thirdPost.1 := by
    simpa [rawEntryAt, hfirstPost, hthirdPost] using hentry.1.trans hentry.2
  have hbit := T.first_third_post_writer_bit_eq hN
  have hbit' : firstPost.2 (rawWriterAt w start first) =
      thirdPost.2 (rawWriterAt w start first) := by
    simpa [tonguesAt, hfirstPost, hthirdPost] using hbit
  have hvector := T.first_third_post_vector_ne
  have hvector' : VectorCount.restrict N firstPost.2 ≠
      VectorCount.restrict N thirdPost.2 := by
    intro heq
    apply hvector
    simpa [restrictedTonguesAt, tonguesAt, hfirstPost, hthirdPost]
      using heq.symm
  exact ⟨firstPost, thirdPost, hfirstPost, hthirdPost,
    hport, hbit', hvector'⟩

/-- **Third-writer sharp dichotomy.**

The novel third occurrence forces a productive foreign rerouter strictly
between the second and third occurrences.  Either it is a first productive
writer (one charge to the `N`-switch budget), or its own last-writer frame
opens before the second occurrence.  The latter is the exact interlacing
word `B < A < B < A`; no tail or recurrence premise is assumed. -/
theorem RawThirdWriterNovelAt.first_charge_or_interlaced_writer
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    ∃ reroute,
      second < reroute ∧ reroute < third ∧
      RawProductiveAt w N start reroute ∧
      rawWriterAt w start reroute ≠ rawWriterAt w start third ∧
      (∀ t, second < t → t < reroute →
        RawProductiveAt w N start t →
        rawWriterAt w start t ≠ rawWriterAt w start reroute) ∧
      (RawFirstWriterAt w N start reroute ∨
        ∃ prior,
          RawLastWriterFrame w N start prior reroute ∧ prior < second) := by
  let F := T.secondThirdFrame
  obtain ⟨C, reroute, _hC, hsr, hrt, hprod, hwriter,
      _hchange, hno⟩ :=
    T.repeatedNovel.first_changed_writer hN F
  have hdiff : rawWriterAt w start reroute ≠
      rawWriterAt w start third :=
    F.no_same_writer_between reroute hsr hrt hprod
  refine ⟨reroute, hsr, hrt, hprod, hdiff, ?_, ?_⟩
  · intro t hst htr htprod
    rw [hwriter]
    exact hno t hst htr htprod
  · by_cases hfirst : RawFirstWriterAt w N start reroute
    · exact Or.inl hfirst
    · obtain ⟨prior, G⟩ :=
        last_writer_frame_of_productive_not_first hprod hfirst
      have hprior : prior < second := by
        by_cases hlt : prior < second
        · exact hlt
        · by_cases heq : prior = second
          · subst prior
            exact (hdiff
              (G.same_writer.symm.trans T.same_second_third)).elim
          · have hsp : second < prior := by omega
            exact (hno prior hsp G.order G.open_productive
              (G.same_writer.trans hwriter)).elim
      exact Or.inr ⟨prior, G, hprior⟩

/-- If the final `A`-frame contains no first-writer charge, the missing
alternative is an explicit `BABA` interlacing by a different writer. -/
theorem RawThirdWriterNovelAt.interlaced_writer_of_no_first_charge
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third)
    (hnoCharge : ∀ t, second < t → t < third →
      ¬ RawFirstWriterAt w N start t) :
    ∃ prior reroute,
      prior < second ∧ second < reroute ∧ reroute < third ∧
      RawLastWriterFrame w N start prior reroute ∧
      rawWriterAt w start reroute ≠ rawWriterAt w start third := by
  obtain ⟨reroute, hsr, hrt, _hprod, hdiff, _hno,
      hfirst | ⟨prior, G, hprior⟩⟩ :=
    T.first_charge_or_interlaced_writer hN
  · exact (hnoCharge reroute hsr hrt hfirst).elim
  · exact ⟨prior, reroute, hprior, hsr, hrt, G, hdiff⟩

end GeneralN
