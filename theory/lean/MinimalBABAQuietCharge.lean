import MinimalBABAQuietDogbone

/-!
# Charging the quiet residue of an overlap-minimal BABA

The order-theoretic Raman residue has two branches.  If there is no raw
last-writer frame nested in the overlap, every productive event there must be
a globally first writer: a non-first event supplies its last-writer frame,
and that frame either lies in the forbidden region or makes a strictly
smaller BABA.  If a least nested frame is quiet, its closing vector is an
earlier replay and its complete finite segment has only two vectors.

These are direct raw `Wiring`/`stepN` statements.  The second conclusion is
a finite replay certificate, not an unproved infinite-tail assertion.
-/

namespace GeneralN

/-- A quiet last-writer frame is a literal two-vector finite segment. -/
theorem RawLastWriterFrame.quiet_segment_two_vectors
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {left right : Nat}
    (F : RawLastWriterFrame w N start left right)
    (hquiet : ∀ k, left < k → k < right →
      ¬ RawProductiveAt w N start k) :
    ∀ t, left ≤ t → t ≤ right + 1 →
      restrictedTonguesAt w N start t ∈
        [restrictedTonguesAt w N start left,
         restrictedTonguesAt w N start (left + 1)] := by
  intro t hleftT htRight
  obtain ⟨final, hfinal⟩ :=
    Option.isSome_iff_exists.mp F.close_productive.1
  obtain ⟨atT, ht⟩ := stepN_prefix_some
    (d := t) (K := right + 1) htRight hfinal
  by_cases hAtLeft : t = left
  · subst t
    simp
  by_cases hThroughRight : t ≤ right
  · let span := t - (left + 1)
    have hsum : left + 1 + span = t := by
      dsimp [span]
      omega
    have hstable : restrictedTonguesAt w N start t =
        restrictedTonguesAt w N start (left + 1) := by
      have h := restrictedTonguesAt_eq_of_quiet_interval
        (first := left + 1) (span := span) (finish := atT)
        (by simpa [hsum] using ht) (by
          intro k hkLeft hkRight
          apply hquiet k <;> omega)
      simpa [hsum] using h
    simp [hstable]
  have hAtClosePost : t = right + 1 := by omega
  subst t
  have hreturn := F.closes_vector_of_quiet hN hquiet
  simp [hreturn]

/-- The close of a quiet last-writer frame cannot be globally novel: its
post-vector is exactly the earlier vector at the opening time. -/
theorem RawLastWriterFrame.quiet_close_not_novel
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {left right : Nat}
    (F : RawLastWriterFrame w N start left right)
    (hquiet : ∀ k, left < k → k < right →
      ¬ RawProductiveAt w N start k) :
    ¬ RawNovelAt w N start right := by
  intro hnovel
  have hleftRight : left < right := F.order
  apply hnovel.post_ne_earlier (earlier := left) (by omega)
  exact F.closes_vector_of_quiet hN hquiet

/-- In the no-nested-frame branch, every productive overlap event is a
first writer.  A non-first event's canonical last-writer frame either starts
inside the overlap, contradicting the premise, or starts before `second` and
forms a BABA with strictly smaller overlap. -/
theorem RawBABAOverlapMinimal.no_interior_frame_productive_is_first
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hnoFrame : ∀ opening closing,
      second < opening → opening < reroute →
      RawLastWriterFrame w N start opening closing → False) :
    ∀ k, second < k → k < reroute →
      RawProductiveAt w N start k →
      RawFirstWriterAt w N start k := by
  intro k hsecondK hkReroute hprod
  by_cases hfirst : RawFirstWriterAt w N start k
  · exact hfirst
  obtain ⟨left, F⟩ :=
    last_writer_frame_of_productive_not_first hprod hfirst
  have hkThird : k < third :=
    Nat.lt_trans hkReroute B.reroute_lt_third
  have hdiff : rawWriterAt w start k ≠ rawWriterAt w start third :=
    B.rightFrame.no_same_writer_between k hsecondK hkThird hprod
  by_cases hleftLe : left ≤ second
  · by_cases hleftEq : left = second
    · subst left
      apply (hdiff (F.same_writer.symm.trans B.rightFrame.same_writer)).elim
    · have hleftSecond : left < second := by omega
      let C : RawBABAInterlacement
          w N start left second k third := {
        prior_lt_second := hleftSecond
        second_lt_reroute := hsecondK
        reroute_lt_third := hkThird
        leftFrame := F
        rightFrame := B.rightFrame
        different_writers := hdiff
      }
      have hsmaller : C.overlap < B.overlap := by
        change k - second < reroute - second
        omega
      exact (hmin left second k third C hsmaller).elim
  · have hsecondLeft : second < left := Nat.lt_of_not_ge hleftLe
    exact (hnoFrame left k hsecondLeft
      (Nat.lt_trans F.order hkReroute) F).elim

/-- Proof-relevant package for the least quiet nested frame. -/
structure RawQuietFrameReplay
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (second reroute : Nat) : Type where
  opening : Nat
  closing : Nat
  inside_left : second < opening
  inside_right : closing < reroute
  frame : RawLastWriterFrame w N start opening closing
  foreign : Echo.ForeignRestorationFrame
    (rawOverwriteMachine w) (rawOverwriteEntry w N start)
    (rawOverwriteInitial start) opening closing
  minimal_close : ∀ opening' closing',
    second < opening' → opening' < reroute →
    RawLastWriterFrame w N start opening' closing' →
    closing' < closing → False
  quiet : ∀ k, opening < k → k < closing →
    ¬ RawProductiveAt w N start k
  close_replay : ¬ RawNovelAt w N start closing
  two_vectors : ∀ t, opening ≤ t → t ≤ closing + 1 →
    restrictedTonguesAt w N start t ∈
      [restrictedTonguesAt w N start opening,
       restrictedTonguesAt w N start (opening + 1)]

/-- Exact charge/replay closure of the order-theoretic quiet residue.

The first alternative charges every productive overlap event to the global
first-writer history.  The second exposes the least nested quiet frame as a
two-vector segment whose close is a literal replay. -/
theorem RawBABAOverlapMinimal.quiet_residue_charge_or_replay
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hresidue :
      (∀ opening closing,
        second < opening → opening < reroute →
        RawLastWriterFrame w N start opening closing → False) ∨
      ∃ opening closing,
        second < opening ∧
        opening < reroute ∧
        opening < closing ∧
        closing < reroute ∧
        Echo.ForeignRestorationFrame
          (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) opening closing ∧
        (∀ opening' closing',
          second < opening' →
          opening' < reroute →
          RawLastWriterFrame w N start opening' closing' →
          closing' < closing → False) ∧
        (∀ k, opening < k → k < closing →
          ¬ RawProductiveAt w N start k)) :
    (∀ k, second < k → k < reroute →
      RawProductiveAt w N start k →
      RawFirstWriterAt w N start k) ∨
      Nonempty (RawQuietFrameReplay w N start second reroute) := by
  rcases hresidue with hnoFrame | hquietFrame
  · exact Or.inl
      (hmin.no_interior_frame_productive_is_first hnoFrame)
  · obtain ⟨opening, closing, hsecond, hopenReroute,
        hopenClose, hcloseReroute, hforeign, hminimal, hquiet⟩ :=
      hquietFrame
    let F : RawLastWriterFrame w N start opening closing :=
      sparse_foreignRestoration_to_rawLastWriterFrame hN hforeign
    exact Or.inr ⟨{
      opening := opening
      closing := closing
      inside_left := hsecond
      inside_right := hcloseReroute
      frame := F
      foreign := hforeign
      minimal_close := hminimal
      quiet := hquiet
      close_replay := F.quiet_close_not_novel hN hquiet
      two_vectors := F.quiet_segment_two_vectors hN hquiet
    }⟩

end GeneralN
