import ReuseForcesReplayClosure
import SelfShrinkChargeClosure

/-!
# Charging restoration families to switches

`SelfShrinkChargeClosure` charges the first loss of a physical carrier port
to one of the `3 * N` ports.  Reusing that charge does not by itself force a
global replay: `ReuseForcesReplayClosure` correctly exposes a first non-self
restoration and a later productive writer which accounts for the changed
closing vector.

This file performs the next unconditional finite charge.  For every reused
strict-shrink novelty we choose one such restoration witness and charge it to
the witness's post-restoration writer.  There are only `N` possible writers.
Consequently either all reused strict-shrink novelties number at most `N`, or
two distinct restoration families share a writer.  In the collision branch
we do not assert replay.  Instead we use novelty of the two closing states to
extract a concrete productive steering write between them.

Thus every finite prefix satisfies the raw dichotomy

* novel strict self-shrinks are bounded by `4 * N`; or
* there is a shared-restoration-writer collision with a named intervening
  steering switch.

The second branch is the exact remaining global interaction.  Eliminating it
or proving that repeated collisions enter a four-state tail would improve the
raw strict-shrink charge.  This file does not claim `StateLaw`.
-/

namespace GeneralN

/-! ## One complete witness for a reused physical charge -/

/-- The data forced by one reused canonical strict-shrink charge.

`previous` is an earlier strict shrink losing the same physical port.
`restore` is the first restoration of that port.  Since the closing state at
`close + 1` is globally novel, failure to replay the restoration state names
a productive `writer` at `writerTime` after the restoration. -/
structure RawReuseRestorationWitness
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (close : Nat) where
  previous : Nat
  restore : Nat
  writer : Nat
  writerTime : Nat
  previous_lt_restore : previous < restore
  restore_lt_close : restore < close
  previous_novel : RawNovelRepeatedStrictShrinkAt w N start previous
  close_novel : RawNovelRepeatedStrictShrinkAt w N start close
  same_charge :
    rawNovelStrictShrinkCharge w N start previous =
      rawNovelStrictShrinkCharge w N start close
  first_restoration :
    RawFirstPortRestoration w N start (previous + 1) restore
      (rawNovelStrictShrinkCharge w N start close)
  restoration_outcome :
    RawFirstPortRestorationOutcome w N start restore
  writer_lt : writer < N
  writer_after_restoration : restore + 1 ≤ writerTime
  writer_before_close : writerTime < close + 1
  writer_productive : RawProductiveAt w N start writerTime
  writer_name : rawWriterAt w start writerTime = writer
  writer_bit_changed :
    (tonguesAt w start (close + 1)) writer ≠
      (tonguesAt w start (restore + 1)) writer

/-- Every member of the reused-charge list has a complete restoration and
post-restoration-writer witness. -/
theorem rawReuseRestorationWitness_exists
    {w : Wiring} {N K close : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hclose : close ∈
      rawReusedNovelStrictShrinkTimes w N start K) :
    Nonempty (RawReuseRestorationWitness w N start close) := by
  have hcloseData :=
    mem_rawReusedNovelStrictShrinkTimes_iff.mp hclose
  obtain ⟨previous, hpreviousClose, hpreviousNovel, hcharge⟩ :=
    hcloseData.2.2
  have hpreviousCharge :=
    rawNovelStrictShrinkCharge_spec hpreviousNovel.2
  have hcloseCharge :=
    rawNovelStrictShrinkCharge_spec hcloseData.2.1.2
  have hcloseOld :
      rawNovelStrictShrinkCharge w N start previous ∈
        rawFiniteCurvePortsAt w N start close := by
    rw [hcharge]
    exact hcloseCharge.1
  have hcloseLost :
      rawNovelStrictShrinkCharge w N start previous ∉
        rawFiniteCurvePortsAt w N start (close + 1) := by
    rw [hcharge]
    exact hcloseCharge.2
  obtain ⟨restore, C, t, hpreviousRestore, hrestoreClose,
      F, houtcome, hC, htlo, hthi, htprod, htwriter, hbit⟩ :=
    reused_novel_strict_shrink_requires_restoration_and_writer
      hN hpreviousClose hpreviousNovel hcloseData.2.1
        hpreviousCharge.1 hpreviousCharge.2 hcloseOld hcloseLost
  refine ⟨{
    previous := previous
    restore := restore
    writer := C
    writerTime := t
    previous_lt_restore := hpreviousRestore
    restore_lt_close := hrestoreClose
    previous_novel := hpreviousNovel
    close_novel := hcloseData.2.1
    same_charge := hcharge
    first_restoration := ?_
    restoration_outcome := houtcome
    writer_lt := hC
    writer_after_restoration := htlo
    writer_before_close := hthi
    writer_productive := htprod
    writer_name := htwriter
    writer_bit_changed := hbit
  }⟩
  simpa [hcharge] using F

/-! ## A canonical switch charge -/

/-- Choose the post-restoration writer of one reused strict-shrink event.
Outside the reuse domain the value is irrelevant. -/
noncomputable def rawReuseRestorationWriter
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (close : Nat) : Nat := by
  classical
  exact if h : Nonempty (RawReuseRestorationWitness w N start close) then
    (Classical.choice h).writer
  else
    0

/-- On the reuse domain, the canonical writer comes with the complete raw
witness from which it was selected. -/
theorem rawReuseRestorationWriter_spec
    {w : Wiring} {N K close : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hclose : close ∈
      rawReusedNovelStrictShrinkTimes w N start K) :
    ∃ W : RawReuseRestorationWitness w N start close,
      W.writer = rawReuseRestorationWriter w N start close := by
  classical
  have hex := rawReuseRestorationWitness_exists hN hclose
  unfold rawReuseRestorationWriter
  rw [dif_pos hex]
  exact ⟨Classical.choice hex, rfl⟩

/-- Every canonical restoration-family charge is a represented switch. -/
theorem rawReuseRestorationWriter_lt
    {w : Wiring} {N K close : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hclose : close ∈
      rawReusedNovelStrictShrinkTimes w N start K) :
    rawReuseRestorationWriter w N start close < N := by
  obtain ⟨W, hW⟩ := rawReuseRestorationWriter_spec hN hclose
  rw [← hW]
  exact W.writer_lt

/-! ## What a duplicate writer charge really implies -/

/-- Two distinct restoration families charged to the same writer, together
with a productive steering write forced between their distinct novel closing
states.  The steering switch is intentionally not assumed to be the shared
writer: equality is the self-steering case, while inequality is the genuine
cross-switch escape. -/
structure RawSharedRestorationWriterCollision
    (w : Wiring) (N : Nat) (start : Nat × Tongues) where
  earlier : Nat
  later : Nat
  earlier_lt_later : earlier < later
  earlier_witness : RawReuseRestorationWitness w N start earlier
  later_witness : RawReuseRestorationWitness w N start later
  shared_writer : earlier_witness.writer = later_witness.writer
  steeringSwitch : Nat
  steeringTime : Nat
  steeringSwitch_lt : steeringSwitch < N
  steering_after_earlier : earlier + 1 ≤ steeringTime
  steering_before_later : steeringTime < later + 1
  steering_productive : RawProductiveAt w N start steeringTime
  steering_writer : rawWriterAt w start steeringTime = steeringSwitch
  steering_bit_changed :
    (tonguesAt w start (later + 1)) steeringSwitch ≠
      (tonguesAt w start (earlier + 1)) steeringSwitch

private theorem restrict_ne_has_coordinate_family
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

/-- Distinct witnessed closing novelties charged to the same writer produce
the full shared-writer collision, including a named intervening steering
write. -/
theorem sharedRestorationWriterCollision_of_witnesses
    {w : Wiring} {N earlier later : Nat} {start : Nat × Tongues}
    (hlt : earlier < later)
    (A : RawReuseRestorationWitness w N start earlier)
    (B : RawReuseRestorationWitness w N start later)
    (hshared : A.writer = B.writer) :
    Nonempty (RawSharedRestorationWriterCollision w N start) := by
  have hvectorNe :
      restrictedTonguesAt w N start (later + 1) ≠
        restrictedTonguesAt w N start (earlier + 1) := by
    intro heq
    have htimes := rawNovelAt_post_injective
      B.close_novel.1.2.2 A.close_novel.1.2.2 heq
    omega
  obtain ⟨C, hC, hbit⟩ :=
    restrict_ne_has_coordinate_family hvectorNe
  obtain ⟨finish, hfinish⟩ :=
    Option.isSome_iff_exists.mp B.close_novel.1.1.1
  let span := later - earlier
  have hspan : earlier + 1 + span = later + 1 := by
    dsimp [span]
    omega
  have hfinish' :
      stepN w (earlier + 1 + span) start = some finish := by
    simpa [hspan] using hfinish
  have hbit' :
      (tonguesAt w start (earlier + 1 + span)) C ≠
        (tonguesAt w start (earlier + 1)) C := by
    simpa [hspan] using hbit
  obtain ⟨t, htlo, hthi, htprod, htwriter⟩ :=
    changed_coordinate_has_writer_between hC hfinish' hbit'
  refine ⟨{
    earlier := earlier
    later := later
    earlier_lt_later := hlt
    earlier_witness := A
    later_witness := B
    shared_writer := hshared
    steeringSwitch := C
    steeringTime := t
    steeringSwitch_lt := hC
    steering_after_earlier := htlo
    steering_before_later := ?_
    steering_productive := htprod
    steering_writer := htwriter
    steering_bit_changed := hbit
  }⟩
  simpa [hspan] using hthi

private theorem nodup_or_equal_pair_family
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) : ∀ {xs : List α}, xs.Nodup →
      (xs.map f).Nodup ∨
        ∃ a, a ∈ xs ∧ ∃ b, b ∈ xs ∧ a ≠ b ∧ f a = f b := by
  intro xs hxs
  induction xs with
  | nil => exact Or.inl (by simp)
  | cons a rest ih =>
      rw [List.nodup_cons] at hxs
      rcases ih hxs.2 with hrest | hpair
      · by_cases hmem : f a ∈ rest.map f
        · obtain ⟨b, hb, hEq⟩ := List.mem_map.mp hmem
          exact Or.inr ⟨a, List.mem_cons_self, b,
            List.mem_cons_of_mem _ hb,
            fun hab => hxs.1 (hab ▸ hb), hEq.symm⟩
        · exact Or.inl (by
            simp only [List.map_cons, List.nodup_cons]
            exact ⟨hmem, hrest⟩)
      · rcases hpair with ⟨x, hx, y, hy, hxy, hEq⟩
        exact Or.inr ⟨x, List.mem_cons_of_mem _ hx,
          y, List.mem_cons_of_mem _ hy, hxy, hEq⟩

/-! ## The general finite-family bound -/

/-- **Unconditional restoration-family dichotomy.**

For every finite raw prefix, either reused canonical strict-shrink charges
number at most `N`, or two distinct reuse families share their selected
post-restoration writer and force a concrete steering write between their
novel closing states. -/
theorem reused_strict_shrinks_le_switches_or_shared_writer_collision
    {w : Wiring} {N : Nat} (start : Nat × Tongues) (K : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) :
    (rawReusedNovelStrictShrinkTimes w N start K).length ≤ N ∨
      Nonempty (RawSharedRestorationWriterCollision w N start) := by
  classical
  let events := rawReusedNovelStrictShrinkTimes w N start K
  let charge := rawReuseRestorationWriter w N start
  have heventsNodup : events.Nodup := by
    dsimp [events, rawReusedNovelStrictShrinkTimes,
      rawNovelRepeatedStrictShrinkTimes]
    exact (List.nodup_range.filter _).filter _
  rcases nodup_or_equal_pair_family charge heventsNodup with
      hcharges | hcollision
  · left
    have hlt : ∀ C, C ∈ events.map charge → C < N := by
      intro C hC
      obtain ⟨close, hclose, rfl⟩ := List.mem_map.mp hC
      exact rawReuseRestorationWriter_lt hN hclose
    have hbound := nodup_nat_lt_length hcharges hlt
    simpa [events, charge] using hbound
  · right
    obtain ⟨i, hi, j, hj, hij, hcharge⟩ := hcollision
    obtain ⟨A, hA⟩ := rawReuseRestorationWriter_spec hN hi
    obtain ⟨B, hB⟩ := rawReuseRestorationWriter_spec hN hj
    have hshared : A.writer = B.writer := by
      rw [hA, hB]
      exact hcharge
    by_cases hlt : i < j
    · exact sharedRestorationWriterCollision_of_witnesses hlt A B hshared
    · have hjlt : j < i := by omega
      exact sharedRestorationWriterCollision_of_witnesses
        hjlt B A hshared.symm

/-- **Raw strict-shrink corollary.**  Every finite prefix has at most
`4 * N` globally novel repeated-writer strict shrinks, unless the explicit
shared-restoration-writer steering collision occurs. -/
theorem novel_strict_shrinks_le_four_mul_or_shared_writer_collision
    {w : Wiring} {N : Nat} (start : Nat × Tongues) (K : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) :
    (rawNovelRepeatedStrictShrinkTimes w N start K).length ≤ 4 * N ∨
      Nonempty (RawSharedRestorationWriterCollision w N start) := by
  rcases reused_strict_shrinks_le_switches_or_shared_writer_collision
      start K hN with hreuse | hcollision
  · left
    have hcharge :=
      novel_strict_shrinks_le_three_mul_add_reuses w N start K
    omega
  · exact Or.inr hcollision

/-- Exact interface for the remaining interaction: no two selected
restoration families share a writer.  The definition is deliberately about
the raw collision structure above, not a hidden compiler certificate. -/
def NoSharedRestorationWriterCollision
    (w : Wiring) (N : Nat) (start : Nat × Tongues) : Prop :=
  ¬ Nonempty (RawSharedRestorationWriterCollision w N start)

/-- If the remaining shared-writer interaction is excluded, the reused
families charge injectively to switches. -/
theorem reused_strict_shrinks_le_switches
    {w : Wiring} {N : Nat} (start : Nat × Tongues) (K : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hfree : NoSharedRestorationWriterCollision w N start) :
    (rawReusedNovelStrictShrinkTimes w N start K).length ≤ N := by
  rcases reused_strict_shrinks_le_switches_or_shared_writer_collision
      start K hN with hbound | hcollision
  · exact hbound
  · exact (hfree hcollision).elim

/-- Under the same explicit interaction exclusion, all globally novel
strict-shrink events in a finite prefix are bounded by `4 * N`. -/
theorem novel_strict_shrinks_le_four_mul
    {w : Wiring} {N : Nat} (start : Nat × Tongues) (K : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hfree : NoSharedRestorationWriterCollision w N start) :
    (rawNovelRepeatedStrictShrinkTimes w N start K).length ≤ 4 * N := by
  rcases novel_strict_shrinks_le_four_mul_or_shared_writer_collision
      start K hN with hbound | hcollision
  · exact hbound
  · exact (hfree hcollision).elim

end GeneralN
