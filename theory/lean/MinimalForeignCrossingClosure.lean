import BABAPartnerReflectorTail
import TripleInterlacementObstruction

/-!
# The exact minimal foreign-crossing residue

This file studies the pure ForeignRestorationCrossing branch of an
overlap-minimal raw BABA.  It first proves the missing reverse compiler:
productive steps and first-restoration frames of the sparse overwrite
sequence are exactly raw productive steps and raw last-writer frames.

This makes raw overlap minimality available to every sparse foreign crossing,
not only to crossings originally presented as raw frames.  The resulting
unconditional conclusion is a strict nesting law: every additional foreign
frame opened in the BABA overlap closes strictly before the left close.
For a raw frame, either an endpoint is a reached direct lobe or its closing
time strictly descends.

The original pure crossing itself is not eliminated by ordering alone; no
Echo.IsRun or periodic-tail premise is smuggled into the sparse compiler.
-/

namespace GeneralN

/-- The sentinel cell N of the sparse overwrite sequence is permanently
equal to its sentinel slot 3*N. -/
theorem rawOverwrite_reg_sentinel
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) :
    ∀ k,
      Echo.reg (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) k N = 3 * N := by
  intro k
  induction k with
  | zero =>
      simp [Echo.reg, rawOverwriteEntry, rawOverwriteMachine]
  | succ k ih =>
      by_cases hprod : RawProductiveAt w N start k
      · have hlt : rawWriterAt w start k < N :=
          rawProductiveAt_writer_lt hN hprod
        have hcell :
            (rawOverwriteMachine w).cellOf
                (rawOverwriteEntry w N start (k + 1)) ≠ N := by
          rw [rawOverwriteEntry_cell_of_productive hprod]
          omega
        rw [Echo.reg_skip _ _ _ hcell, ih]
      · have hentry :
            rawOverwriteEntry w N start (k + 1) = 3 * N := by
          simp [rawOverwriteEntry, hprod]
        have hcell :
            (rawOverwriteMachine w).cellOf
                (rawOverwriteEntry w N start (k + 1)) = N := by
          rw [hentry]
          simp [rawOverwriteMachine]
        rw [Echo.reg_write _ _ _ hcell, hentry]

/-- Sparse productivity is equivalent to raw productivity.  The reverse
implication is the point: a quiet raw time writes the already-stable
sentinel and therefore cannot be sparse-productive. -/
theorem rawOverwrite_productive_iff_rawProductive
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat} :
    Echo.ProductiveStep (rawOverwriteMachine w)
        (rawOverwriteEntry w N start) (rawOverwriteInitial start) k ↔
      RawProductiveAt w N start k := by
  constructor
  · intro hsparse
    apply Classical.byContradiction
    intro hquiet
    apply hsparse
    have hentry :
        rawOverwriteEntry w N start (k + 1) = 3 * N := by
      simp [rawOverwriteEntry, hquiet]
    have hcell :
        (rawOverwriteMachine w).cellOf
            (rawOverwriteEntry w N start (k + 1)) = N := by
      rw [hentry]
      simp [rawOverwriteMachine]
    rw [hcell, hentry, rawOverwrite_reg_sentinel hN start k]
  · exact rawProductiveAt_is_rawOverwriteProductive hN

/-- A bounded nonempty set of natural times has a first member. -/
private theorem exists_first_between_of_exists
    (P : Nat → Prop) :
    ∀ lower upper,
      (∃ i, lower < i ∧ i < upper ∧ P i) →
      ∃ i, lower < i ∧ i < upper ∧ P i ∧
        ∀ j, lower < j → j < i → ¬ P j := by
  classical
  intro lower upper
  induction upper with
  | zero =>
      rintro ⟨i, _hi, hzero, _hPi⟩
      omega
  | succ n ih =>
      intro hex
      by_cases hbelow : ∃ i, lower < i ∧ i < n ∧ P i
      · obtain ⟨i, hlo, hi, hPi, hfirst⟩ := ih hbelow
        exact ⟨i, hlo, by omega, hPi, hfirst⟩
      · obtain ⟨i, hlo, hi, hPi⟩ := hex
        have hinLe : i ≤ n := by omega
        have hnotLt : ¬ i < n := by
          intro hin
          exact hbelow ⟨i, hlo, hin, hPi⟩
        have hnLe : n ≤ i := Nat.le_of_not_gt hnotLt
        have hin : i = n := Nat.le_antisymm hinLe hnLe
        subst i
        refine ⟨n, hlo, by omega, hPi, ?_⟩
        intro j hlow hj hPj
        exact hbelow ⟨j, hlow, hj, hPj⟩

/-- Every first-restoration frame of the sparse overwrite sequence is exactly
a raw last-writer frame.  A hypothetical earlier same-writer raw event has a
first such occurrence; the raw two-flip restoration theorem then violates
the sparse first-return condition. -/
theorem sparse_firstRestoration_to_rawLastWriterFrame
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {left right : Nat}
    (H : Echo.FirstRestorationFrame
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) left right) :
    RawLastWriterFrame w N start left right := by
  have hopen : RawProductiveAt w N start left :=
    (rawOverwrite_productive_iff_rawProductive hN).mp H.1.1
  have hclose : RawProductiveAt w N start right :=
    (rawOverwrite_productive_iff_rawProductive hN).mp H.1.2.2.1
  have hwriterSparse := H.1.2.2.2.1
  rw [rawOverwrite_writerAt_eq hclose,
    rawOverwrite_writerAt_eq hopen] at hwriterSparse
  have hsame :
      rawWriterAt w start left = rawWriterAt w start right :=
    hwriterSparse.symm
  refine
    { order := H.1.2.1
      open_productive := hopen
      close_productive := hclose
      same_writer := hsame
      no_same_writer_between := ?_ }
  intro v hleftV hvRight hvprod
  intro hvWriter
  let P : Nat → Prop := fun j =>
    RawProductiveAt w N start j ∧
      rawWriterAt w start j = rawWriterAt w start left
  have hex : ∃ j, left < j ∧ j < right ∧ P j := by
    exact ⟨v, hleftV, hvRight, hvprod,
      hvWriter.trans hsame.symm⟩
  obtain ⟨j, hleftJ, hjRight, hPj, hfirst⟩ :=
    exists_first_between_of_exists P left right hex
  let F : RawLastWriterFrame w N start left j := {
    order := hleftJ
    open_productive := hopen
    close_productive := hPj.1
    same_writer := hPj.2.symm
    no_same_writer_between := by
      intro s hleftS hsJ hsprod
      intro hsWriter
      exact hfirst s hleftS hsJ
        ⟨hsprod, hsWriter.trans hPj.2⟩
  }
  have hrestore := F.restores_selected_branch hN
  have hentry :
      rawOverwriteEntry w N start (j + 1) =
        selectedBranch (tonguesAt w start (j + 1))
          (rawWriterAt w start j) := by
    simp [rawOverwriteEntry, hPj.1]
  have holdSlot :=
    rawOverwrite_oldSlot_eq_selected hN hopen
  have hreturned :
      rawOverwriteEntry w N start (j + 1) =
        Echo.oldSlot (rawOverwriteMachine w)
          (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) left := by
    calc
      rawOverwriteEntry w N start (j + 1) =
          selectedBranch (tonguesAt w start (j + 1))
            (rawWriterAt w start j) := hentry
      _ = selectedBranch (tonguesAt w start left)
            (rawWriterAt w start left) := hrestore
      _ = Echo.oldSlot (rawOverwriteMachine w)
            (rawOverwriteEntry w N start)
            (rawOverwriteInitial start) left := holdSlot.symm
  exact H.2 j hleftJ hjRight hreturned

/-- Sparse foreign frames therefore retain their exact raw last-writer
endpoints. -/
theorem sparse_foreignRestoration_to_rawLastWriterFrame
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {left right : Nat}
    (H : Echo.ForeignRestorationFrame
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) left right) :
    RawLastWriterFrame w N start left right :=
  sparse_firstRestoration_to_rawLastWriterFrame hN H.1

/-- Every sparse foreign crossing is a raw BABA with the same four
endpoints.  The two writers are distinct because the second opening lies
strictly inside the first raw last-writer frame. -/
theorem sparse_foreignCrossing_to_rawBABA
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {t0 u0 t1 u1 : Nat}
    (H : Echo.ForeignRestorationCrossing
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) t0 u0 t1 u1) :
    RawBABAInterlacement w N start t0 t1 u0 u1 := by
  have F0 : RawLastWriterFrame w N start t0 u0 :=
    sparse_foreignRestoration_to_rawLastWriterFrame hN H.1
  have F1 : RawLastWriterFrame w N start t1 u1 :=
    sparse_foreignRestoration_to_rawLastWriterFrame hN H.2.1
  have hdiff :
      rawWriterAt w start u0 ≠ rawWriterAt w start u1 := by
    intro heq
    have ht1u0 :
        rawWriterAt w start t1 = rawWriterAt w start u0 :=
      F1.same_writer.trans heq.symm
    exact F0.no_same_writer_between t1
      H.2.2.1 H.2.2.2.1 F1.open_productive ht1u0
  exact
    { prior_lt_second := H.2.2.1
      second_lt_reroute := H.2.2.2.1
      reroute_lt_third := H.2.2.2.2
      leftFrame := F0
      rightFrame := F1
      different_writers := hdiff }

/-- Raw overlap minimality excludes every sparse foreign crossing with
strictly smaller simultaneous-open interval. -/
theorem RawBABAOverlapMinimal.excludes_smaller_sparse_foreign_crossing
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    {t0 u0 t1 u1 : Nat}
    (H : Echo.ForeignRestorationCrossing
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) t0 u0 t1 u1)
    (hsmaller :
      Echo.crossingOverlap t0 u0 t1 u1 < B.overlap) :
    False := by
  let C := sparse_foreignCrossing_to_rawBABA hN H
  apply hmin t0 t1 u0 u1 C
  simpa [RawBABAInterlacement.overlap, Echo.crossingOverlap]
    using hsmaller

/-- In a pure overlap-minimal foreign crossing, every additional foreign
frame opened strictly inside the overlap closes strictly before the left
close.  Crossing past the left close creates a smaller crossing; sharing
the close contradicts first-restoration uniqueness. -/
theorem RawBABAOverlapMinimal.inner_sparse_foreign_strictly_nests
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third opening closing : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hpure : Echo.ForeignRestorationCrossing
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start)
      prior reroute second third)
    (F : Echo.ForeignRestorationFrame
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) opening closing)
    (hsecond : second < opening)
    (hopening : opening < reroute) :
    closing < reroute := by
  by_cases hlt : closing < reroute
  · exact hlt
  by_cases heq : closing = reroute
  · subst closing
    have G : RawLastWriterFrame w N start opening reroute :=
      sparse_foreignRestoration_to_rawLastWriterFrame hN F
    have hpriorOpening : prior < opening :=
      Nat.lt_trans B.prior_lt_second hsecond
    exact (B.leftFrame.no_same_writer_between opening
      hpriorOpening hopening G.open_productive G.same_writer).elim
  · have hclosing : reroute < closing := by omega
    have hnew : Echo.ForeignRestorationCrossing
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start)
        prior reroute opening closing :=
      ⟨hpure.1, F,
        ⟨Nat.lt_trans B.prior_lt_second hsecond,
          hopening, hclosing⟩⟩
    exfalso
    apply hmin.excludes_smaller_sparse_foreign_crossing hN hnew
    unfold Echo.crossingOverlap RawBABAInterlacement.overlap
    omega

/-- The physical raw-frame form of the strict descent.  Any raw
last-writer frame opened in the overlap either has a reached direct-lobe
endpoint, or its close lies strictly inside the old overlap. -/
theorem RawBABAOverlapMinimal.inner_raw_frame_lobe_or_strict_descent
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third opening closing : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hpure : Echo.ForeignRestorationCrossing
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start)
      prior reroute second third)
    (F : RawLastWriterFrame w N start opening closing)
    (hsecond : second < opening)
    (hopening : opening < reroute) :
    RawReachedDirectLobeAt w start closing ∨ closing < reroute := by
  rcases F.endpoint_lobe_or_foreign_restoration hN with
    hopen | hclose | hforeign
  · exact Or.inl
      (F.endpoint_lobe_reaches_close hN (Or.inl hopen))
  · exact Or.inl
      (F.endpoint_lobe_reaches_close hN (Or.inr hclose))
  · exact Or.inr
      (hmin.inner_sparse_foreign_strictly_nests
        hN hpure hforeign hsecond hopening)

/-- Exact unconditional order-theoretic closure available for the pure
minimal branch: all sparse foreign frames nest, and every raw interior frame
either reaches a direct lobe or strictly decreases its close time. -/
theorem RawBABAOverlapMinimal.pure_foreign_strict_descent_package
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hpure : Echo.ForeignRestorationCrossing
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start)
      prior reroute second third) :
    (∀ opening closing,
      Echo.ForeignRestorationFrame
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) opening closing →
      second < opening → opening < reroute →
      closing < reroute) ∧
    (∀ opening closing,
      RawLastWriterFrame w N start opening closing →
      second < opening → opening < reroute →
      RawReachedDirectLobeAt w start closing ∨ closing < reroute) := by
  constructor
  · intro opening closing F hsecond hopening
    exact hmin.inner_sparse_foreign_strictly_nests
      hN hpure F hsecond hopening
  · intro opening closing F hsecond hopening
    exact hmin.inner_raw_frame_lobe_or_strict_descent
      hN hpure F hsecond hopening

/-- If any raw frame opens in the overlap, one has a least closing time.
This is the well-founded selector used below; it minimizes an actual natural
time, not a newly assumed certificate. -/
private theorem exists_minimal_close_interior_raw_frame
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {second reroute : Nat}
    (hex : ∃ opening closing,
      second < opening ∧ opening < reroute ∧
      RawLastWriterFrame w N start opening closing) :
    ∃ opening closing,
      second < opening ∧ opening < reroute ∧
      RawLastWriterFrame w N start opening closing ∧
      ∀ opening' closing',
        second < opening' →
        opening' < reroute →
        RawLastWriterFrame w N start opening' closing' →
        closing' < closing → False := by
  obtain ⟨opening0, closing0, hsecond0, hopen0, F0⟩ := hex
  let P : Nat → Prop := fun closing =>
    ∃ opening,
      second < opening ∧ opening < reroute ∧
      RawLastWriterFrame w N start opening closing
  have hsecondClose0 : second < closing0 :=
    Nat.lt_trans hsecond0 F0.order
  have hbounded :
      ∃ closing, second < closing ∧ closing < closing0 + 1 ∧ P closing := by
    exact ⟨closing0, hsecondClose0, by omega,
      ⟨opening0, hsecond0, hopen0, F0⟩⟩
  obtain ⟨closing, hsecondClose, _hbound, hP, hfirst⟩ :=
    exists_first_between_of_exists P second (closing0 + 1) hbounded
  obtain ⟨opening, hsecond, hopen, F⟩ := hP
  refine ⟨opening, closing, hsecond, hopen, F, ?_⟩
  intro opening' closing' hsecond' hopen' F' hclose'
  have hsecondClose' : second < closing' :=
    Nat.lt_trans hsecond' F'.order
  exact hfirst closing' hsecondClose' hclose'
    ⟨opening', hsecond', hopen', F'⟩

/-- **Sharp assumption-free residue of a pure overlap-minimal BABA.**

Either an interior raw frame reaches a physical direct lobe, an interior
productive event is a globally first writer, there is no interior
last-writer frame at all, or there is a least-closing foreign frame wholly
inside the overlap and its open interval is raw-quiet.

The last two alternatives are the exact missing existence/routing lemma.
Order minimality alone cannot manufacture a productive event inside a quiet
physical route.  In particular this theorem does not call the pure crossing
eliminated and does not treat the sparse overwrite sequence as an IsRun. -/
theorem RawBABAOverlapMinimal.pure_foreign_lobe_charge_or_quiet_residual
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hpure : Echo.ForeignRestorationCrossing
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start)
      prior reroute second third) :
    (∃ k, RawReachedDirectLobeAt w start k) ∨
    (∃ k, second < k ∧ k < reroute ∧
      RawFirstWriterAt w N start k) ∨
    ((∀ opening closing,
        second < opening →
        opening < reroute →
        RawLastWriterFrame w N start opening closing →
        False) ∨
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
          ¬ RawProductiveAt w N start k)) := by
  classical
  by_cases hex : ∃ opening closing,
      second < opening ∧ opening < reroute ∧
      RawLastWriterFrame w N start opening closing
  · obtain ⟨opening, closing, hsecond, hopen, F, hminimal⟩ :=
      exists_minimal_close_interior_raw_frame hex
    rcases F.endpoint_lobe_or_foreign_restoration hN with
      hlobeOpen | hlobeClose | hforeign
    · exact Or.inl
        ⟨closing,
          F.endpoint_lobe_reaches_close hN (Or.inl hlobeOpen)⟩
    · exact Or.inl
        ⟨closing,
          F.endpoint_lobe_reaches_close hN (Or.inr hlobeClose)⟩
    · have hclose : closing < reroute :=
        (hmin.pure_foreign_strict_descent_package hN hpure).1
          opening closing hforeign hsecond hopen
      have hinteriorFirst :
          ∀ k, opening < k → k < closing →
            RawProductiveAt w N start k →
            RawFirstWriterAt w N start k := by
        intro k hopenK hkClose hprod
        by_cases hfirst : RawFirstWriterAt w N start k
        · exact hfirst
        · obtain ⟨left, G⟩ :=
            last_writer_frame_of_productive_not_first hprod hfirst
          by_cases hleftLe : left ≤ second
          · have hleftLt : left < second := by
              by_cases hleftEq : left = second
              · subst left
                have hkThird : k < third :=
                  Nat.lt_trans (Nat.lt_trans hkClose hclose) B.reroute_lt_third
                have hne :=
                  B.rightFrame.no_same_writer_between k
                    (by omega) hkThird hprod
                exact (hne
                  (G.same_writer.symm.trans
                    B.rightFrame.same_writer)).elim
              · omega
            have hkThird : k < third :=
              Nat.lt_trans (Nat.lt_trans hkClose hclose) B.reroute_lt_third
            have hdiff :
                rawWriterAt w start k ≠
                  rawWriterAt w start third :=
              B.rightFrame.no_same_writer_between k
                (by omega) hkThird hprod
            let C : RawBABAInterlacement
                w N start left second k third := {
              prior_lt_second := hleftLt
              second_lt_reroute := by omega
              reroute_lt_third := hkThird
              leftFrame := G
              rightFrame := B.rightFrame
              different_writers := hdiff
            }
            have hsmaller : C.overlap < B.overlap := by
              change k - second < reroute - second
              omega
            exact (hmin left second k third C hsmaller).elim
          · have hsecondLeft : second < left := by omega
            have hleftReroute : left < reroute :=
              Nat.lt_trans G.order (Nat.lt_trans hkClose hclose)
            exact (hminimal left k hsecondLeft hleftReroute
              G hkClose).elim
      by_cases hinterior : ∃ k,
          opening < k ∧ k < closing ∧
          RawProductiveAt w N start k
      · obtain ⟨k, hopenK, hkClose, hprod⟩ := hinterior
        exact Or.inr (Or.inl
          ⟨k, by omega, by omega,
            hinteriorFirst k hopenK hkClose hprod⟩)
      · have hquiet : ∀ k, opening < k → k < closing →
            ¬ RawProductiveAt w N start k := by
          intro k hopenK hkClose hprod
          exact hinterior ⟨k, hopenK, hkClose, hprod⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨opening, closing, hsecond, hopen, F.order, hclose,
            hforeign, hminimal, hquiet⟩))
  · exact Or.inr (Or.inr (Or.inl (by
      intro opening closing hsecond hopen F
      exact hex ⟨opening, closing, hsecond, hopen, F⟩)))

end GeneralN
