import ConcreteMachine
import RestorationFrameOrdering
import ThirdWriterTail
import TrackLobe

/-!
# The raw BABA interlacement and its strict overlap descent

The third consecutive productive occurrence of one writer has one exact
unresolved raw shape.  If no globally first productive writer occurs between
the second and third occurrences, another last-writer frame crosses the final
frame:

```
prior < second < reroute < third
   B       A         B         A
```

This file keeps that statement entirely in the public `Wiring`/`stepN`
language.  Its induction measure is the length of the open overlap,
`reroute - second`.  A further last-writer frame opening strictly inside that
overlap and closing after `reroute` forms a new BABA whose overlap is strictly
smaller.  Thus an overlap-minimal BABA has no such crossing frame.

No recurrence or compiled echo execution is assumed.  In particular, the
stronger terminal claim that every BABA is already a loop or a four-vector
dogbone does not follow merely from the two raw last-writer frames.  The
theorems below expose the exact strict descent available before that remaining
physical routing step is established.
-/

namespace GeneralN

/-! ## A sparse raw overwrite trace

Only productive raw events write represented switch cells.  Every quiet raw
event writes a sentinel in cell `N`.  Consequently the register of each
represented cell is exactly its currently selected branch, and last-writer
frames become first-restoration frames without assuming that this sparse
sequence satisfies the echo recurrence.
-/

/-- The direct branch-port register machine used only for restoration-frame
bookkeeping.  Its jump involution is the physical wiring involution. -/
def rawOverwriteMachine (w : Wiring) : Echo.Machine where
  cellOf := fun p => p / 3
  star := mateNat
  bar := wireBar w
  star_invol := mateNat_invol
  star_ne := mateNat_ne
  bar_invol := wireBar_invol w

/-- Initial selected branch of each raw switch. -/
def rawOverwriteInitial (start : Nat × Tongues) (C : Nat) : Nat :=
  selectedBranch start.2 C

/-- Sparse overwrite entries.  Time zero is a sentinel in cell `N`; a
productive raw event records its newly selected branch, while a quiet event
again records the sentinel. -/
noncomputable def rawOverwriteEntry
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (n : Nat) : Nat := by
  classical
  exact if n = 0 then 3 * N
    else if RawProductiveAt w N start (n - 1) then
      selectedBranch (tonguesAt w start n)
        (rawWriterAt w start (n - 1))
    else 3 * N

@[simp] theorem rawOverwriteMachine_cell
    (w : Wiring) (p : Nat) :
    (rawOverwriteMachine w).cellOf p = p / 3 := rfl

@[simp] theorem rawOverwriteInitial_cell
    (w : Wiring) (start : Nat × Tongues) (C : Nat) :
    (rawOverwriteMachine w).cellOf (rawOverwriteInitial start C) = C := by
  exact selectedBranch_switch start.2 C

@[simp] theorem rawOverwriteEntry_cell_of_productive
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    (rawOverwriteMachine w).cellOf
        (rawOverwriteEntry w N start (k + 1)) =
      rawWriterAt w start k := by
  simp [rawOverwriteEntry, hprod, selectedBranch_switch]

@[simp] theorem rawOverwriteEntry_cell_of_quiet
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {k : Nat}
    (hquiet : ¬ RawProductiveAt w N start k) :
    (rawOverwriteMachine w).cellOf
        (rawOverwriteEntry w N start (k + 1)) = N := by
  simp [rawOverwriteEntry, hquiet]

/-- On every live raw prefix, the sparse register of a represented switch is
exactly that switch's selected branch in the raw tongue state. -/
theorem rawOverwrite_reg_eq_selected
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {C : Nat} (hC : C < N) :
    ∀ k, (stepN w k start).isSome →
      Echo.reg (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) k C =
        selectedBranch (tonguesAt w start k) C := by
  intro k
  induction k with
  | zero =>
      intro _hlive
      have hNC : N ≠ C := Nat.ne_of_gt hC
      simp [Echo.reg, rawOverwriteEntry, rawOverwriteMachine,
        rawOverwriteInitial, tonguesAt, stepN, hNC]
  | succ k ih =>
      intro hlive
      obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
        live_successor_configs hlive
      have hprefix : (stepN w k start).isSome := by simp [hcur]
      have hreg := ih hprefix
      by_cases hprod : RawProductiveAt w N start k
      · by_cases hwriter : rawWriterAt w start k = C
        · have hcell :
              (rawOverwriteMachine w).cellOf
                  (rawOverwriteEntry w N start (k + 1)) = C := by
            rw [rawOverwriteEntry_cell_of_productive hprod, hwriter]
          rw [Echo.reg_write _ _ _ hcell]
          simp [rawOverwriteEntry, hprod, hwriter]
        · have hcell :
              (rawOverwriteMachine w).cellOf
                  (rawOverwriteEntry w N start (k + 1)) ≠ C := by
            rw [rawOverwriteEntry_cell_of_productive hprod]
            exact hwriter
          rw [Echo.reg_skip _ _ _ hcell, hreg]
          have hflip := rawProductiveAt_restricted_flip hN hprod
          have hbit := restrict_eq_apply hflip hC
          have hbit' :
              (tonguesAt w start (k + 1)) C =
                (tonguesAt w start k) C := by
            simpa [flipAt, Ne.symm hwriter] using hbit
          simp [selectedBranch, hbit']
      · have hcell :
            (rawOverwriteMachine w).cellOf
                (rawOverwriteEntry w N start (k + 1)) ≠ C := by
          rw [rawOverwriteEntry_cell_of_quiet hprod]
          exact Nat.ne_of_gt hC
        rw [Echo.reg_skip _ _ _ hcell, hreg]
        have hvector :=
          restrictedTonguesAt_succ_eq_of_not_productive hlive hprod
        have hbit := restrict_eq_apply hvector hC
        simp [selectedBranch, hbit]

/-- The old slot overwritten by a productive raw event is precisely the
branch selected immediately before that event. -/
theorem rawOverwrite_oldSlot_eq_selected
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    Echo.oldSlot (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) k =
      selectedBranch (tonguesAt w start k) (rawWriterAt w start k) := by
  have hC : rawWriterAt w start k < N :=
    rawProductiveAt_writer_lt hN hprod
  obtain ⟨cur, _next, hcur, _hnext, _hstep⟩ :=
    live_successor_configs hprod.1
  unfold Echo.oldSlot
  rw [rawOverwriteEntry_cell_of_productive hprod]
  exact rawOverwrite_reg_eq_selected hN hC k (by simp [hcur])

/-- Every productive raw event is productive in the sparse overwrite trace. -/
theorem rawProductiveAt_is_rawOverwriteProductive
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    Echo.ProductiveStep (rawOverwriteMachine w)
      (rawOverwriteEntry w N start) (rawOverwriteInitial start) k := by
  let C := rawWriterAt w start k
  have hC : C < N := rawProductiveAt_writer_lt hN hprod
  have hnew : rawOverwriteEntry w N start (k + 1) =
      selectedBranch (tonguesAt w start (k + 1)) C := by
    simp [rawOverwriteEntry, hprod, C]
  have hold :
      Echo.oldSlot (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) k =
        selectedBranch (tonguesAt w start k) C := by
    simpa [C] using rawOverwrite_oldSlot_eq_selected hN hprod
  have hflip := rawProductiveAt_restricted_flip hN hprod
  have hbit := restrict_eq_apply hflip hC
  have hbit' : (tonguesAt w start (k + 1)) C =
      !((tonguesAt w start k) C) := by
    simpa [C, flipAt] using hbit
  change rawOverwriteEntry w N start (k + 1) ≠
    Echo.oldSlot (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k
  rw [hnew, hold]
  unfold selectedBranch branchPort
  rw [hbit']
  cases (tonguesAt w start k) C <;> simp

/-- The sparse overwrite writer is the raw switch writer at every productive
event. -/
theorem rawOverwrite_writerAt_eq
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    Echo.writerAt (rawOverwriteMachine w) (rawOverwriteEntry w N start) k =
      rawWriterAt w start k := by
  unfold Echo.writerAt
  exact rawOverwriteEntry_cell_of_productive hprod

/-- A represented tongue is stable on a live interval containing no
productive event by that writer. -/
private theorem rawOverwrite_tongue_eq_of_no_writer_interval
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
      rw [harith] at hfinish ⊢
      have hlive : (stepN w (first + n + 1) start).isSome := by
        simp [hfinish]
      obtain ⟨middle, next, hmiddle, hnext, hstep⟩ :=
        live_successor_configs hlive
      have hnextEq : next = finish := by
        exact Option.some.inj (hnext.symm.trans hfinish)
      subst next
      have hprev : (tonguesAt w start (first + n)) C =
          (tonguesAt w start first) C := by
        apply ih hmiddle
        intro j hfirst hj hprod
        exact hno j hfirst (by omega) hprod
      have hbit : finish.2 C = middle.2 C := by
        apply Classical.byContradiction
        intro hchange
        obtain ⟨hprod, hwriter⟩ :=
          raw_tongue_change_is_productive_writer
            hC hmiddle hfinish hstep hchange
        exact hno (first + n) (by omega) (by omega) hprod hwriter
      calc
        (tonguesAt w start (first + n + 1)) C = finish.2 C := by
          simp [tonguesAt, hfinish]
        _ = middle.2 C := hbit
        _ = (tonguesAt w start (first + n)) C := by
          simp [tonguesAt, hmiddle]
        _ = (tonguesAt w start first) C := hprev

/-- The two endpoint pivots of a last-writer frame restore that writer's
selected branch exactly. -/
theorem RawLastWriterFrame.restores_selected_branch
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {left right : Nat}
    (F : RawLastWriterFrame w N start left right) :
    selectedBranch (tonguesAt w start (right + 1))
        (rawWriterAt w start right) =
      selectedBranch (tonguesAt w start left)
        (rawWriterAt w start left) := by
  let C := rawWriterAt w start right
  have hC : C < N := rawProductiveAt_writer_lt hN F.close_productive
  have hopenVector :=
    rawProductiveAt_restricted_flip hN F.open_productive
  have hopenCoord := restrict_eq_apply hopenVector hC
  have hopen : (tonguesAt w start (left + 1)) C =
      !((tonguesAt w start left) C) := by
    simpa [C, flipAt, F.same_writer] using hopenCoord
  have hcloseVector :=
    rawProductiveAt_restricted_flip hN F.close_productive
  have hcloseCoord := restrict_eq_apply hcloseVector hC
  have hclose : (tonguesAt w start (right + 1)) C =
      !((tonguesAt w start right) C) := by
    simpa [C, flipAt] using hcloseCoord
  obtain ⟨rightState, _rightNext, hrightState, _hrightNext, _hrightStep⟩ :=
    live_successor_configs F.close_productive.1
  let span := right - (left + 1)
  have hsum : left + 1 + span = right := by
    dsimp [span]
    have horder := F.order
    omega
  have hstable : (tonguesAt w start right) C =
      (tonguesAt w start (left + 1)) C := by
    have h := rawOverwrite_tongue_eq_of_no_writer_interval
      hC (first := left + 1) (span := span) (finish := rightState)
      (by simpa [hsum] using hrightState) (by
        intro j hjlo hjhi hprod
        have hleftj : left < j := by omega
        have hjright : j < right := by simpa [hsum] using hjhi
        have hne := F.no_same_writer_between j hleftj hjright hprod
        simpa [C] using hne)
    simpa [hsum] using h
  have hbit : (tonguesAt w start (right + 1)) C =
      (tonguesAt w start left) C := by
    calc
      (tonguesAt w start (right + 1)) C =
          !((tonguesAt w start right) C) := hclose
      _ = !((tonguesAt w start (left + 1)) C) := by rw [hstable]
      _ = !(!((tonguesAt w start left) C)) := by rw [hopen]
      _ = (tonguesAt w start left) C := by
        cases (tonguesAt w start left) C <;> rfl
  unfold selectedBranch
  rw [F.same_writer]
  exact congrArg (branchPort C) hbit

/-- A raw last-writer frame is literally a first-restoration frame in the
sparse overwrite trace. -/
theorem RawLastWriterFrame.toFirstRestorationFrame
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {left right : Nat}
    (F : RawLastWriterFrame w N start left right) :
    Echo.FirstRestorationFrame
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) left right := by
  have hopen :=
    rawProductiveAt_is_rawOverwriteProductive hN F.open_productive
  have hclose :=
    rawProductiveAt_is_rawOverwriteProductive hN F.close_productive
  have hwriter :
      Echo.writerAt (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          right =
        Echo.writerAt (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          left := by
    rw [rawOverwrite_writerAt_eq F.close_productive,
      rawOverwrite_writerAt_eq F.open_productive]
    exact F.same_writer.symm
  have hrestore : rawOverwriteEntry w N start (right + 1) =
      Echo.oldSlot (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) left := by
    calc
      rawOverwriteEntry w N start (right + 1) =
          selectedBranch (tonguesAt w start (right + 1))
            (rawWriterAt w start right) := by
              simp [rawOverwriteEntry, F.close_productive]
      _ = selectedBranch (tonguesAt w start left)
            (rawWriterAt w start left) :=
          F.restores_selected_branch hN
      _ = Echo.oldSlot (rawOverwriteMachine w)
            (rawOverwriteEntry w N start) (rawOverwriteInitial start) left :=
          (rawOverwrite_oldSlot_eq_selected hN F.open_productive).symm
  refine ⟨⟨hopen, F.order, hclose, hwriter, hrestore⟩, ?_⟩
  intro v hleft hright
  have hleftWriterLt : rawWriterAt w start left < N :=
    rawProductiveAt_writer_lt hN F.open_productive
  have holdCell :
      (rawOverwriteMachine w).cellOf
          (Echo.oldSlot (rawOverwriteMachine w)
            (rawOverwriteEntry w N start) (rawOverwriteInitial start) left) =
        rawWriterAt w start left := by
    rw [rawOverwrite_oldSlot_eq_selected hN F.open_productive]
    exact selectedBranch_switch _ _
  by_cases hvprod : RawProductiveAt w N start v
  · intro heq
    have hcells := congrArg (rawOverwriteMachine w).cellOf heq
    rw [rawOverwriteEntry_cell_of_productive hvprod, holdCell] at hcells
    have hne := F.no_same_writer_between v hleft hright hvprod
    exact hne (hcells.trans F.same_writer)
  · intro heq
    have hcells := congrArg (rawOverwriteMachine w).cellOf heq
    rw [rawOverwriteEntry_cell_of_quiet hvprod, holdCell] at hcells
    omega

/-- A raw last-writer frame either has a same-edge endpoint, hence an exact
lobe write, or is a foreign first-restoration frame. -/
theorem RawLastWriterFrame.endpoint_lobe_or_foreign_restoration
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {left right : Nat}
    (F : RawLastWriterFrame w N start left right) :
    Echo.ExactLobeWrite
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) left ∨
    Echo.ExactLobeWrite
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) right ∨
    Echo.ForeignRestorationFrame
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) left right := by
  let m := rawOverwriteMachine w
  let e := rawOverwriteEntry w N start
  let r0 := rawOverwriteInitial start
  have hr0 : ∀ C, m.cellOf (r0 C) = C := by
    intro C
    exact rawOverwriteInitial_cell w start C
  have hopen := rawProductiveAt_is_rawOverwriteProductive hN F.open_productive
  have hclose := rawProductiveAt_is_rawOverwriteProductive hN F.close_productive
  by_cases hopenEdge : Echo.SameEdgeWrite m e r0 left
  · exact Or.inl
      (Echo.productive_sameEdgeWrite_exact_lobe m e r0 hr0 hopen hopenEdge)
  · by_cases hcloseEdge : Echo.SameEdgeWrite m e r0 right
    · exact Or.inr (Or.inl
        (Echo.productive_sameEdgeWrite_exact_lobe
          m e r0 hr0 hclose hcloseEdge))
    · exact Or.inr (Or.inr
        ⟨F.toFirstRestorationFrame hN, hopenEdge, hcloseEdge⟩)

/-- Two last-writer frames crossing in the exact `B < A < B < A` order.
The explicit writer inequality records that the two letters really denote
different switches. -/
structure RawBABAInterlacement
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (prior second reroute third : Nat) : Prop where
  prior_lt_second : prior < second
  second_lt_reroute : second < reroute
  reroute_lt_third : reroute < third
  leftFrame : RawLastWriterFrame w N start prior reroute
  rightFrame : RawLastWriterFrame w N start second third
  different_writers :
    rawWriterAt w start reroute ≠ rawWriterAt w start third

/-- The simultaneous-open interval of a raw BABA crossing. -/
def RawBABAInterlacement.overlap
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (_B : RawBABAInterlacement w N start prior second reroute third) : Nat :=
  reroute - second

theorem RawBABAInterlacement.overlap_pos
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement w N start prior second reroute third) :
    0 < B.overlap := by
  unfold overlap
  exact Nat.sub_pos_of_lt B.second_lt_reroute

/-- The BABA overlap is strictly shorter than the left frame. -/
theorem RawBABAInterlacement.overlap_lt_left_span
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement w N start prior second reroute third) :
    B.overlap < reroute - prior := by
  unfold overlap
  have hprior := B.prior_lt_second
  have hsecond := B.second_lt_reroute
  omega

/-- The BABA overlap is strictly shorter than the right frame. -/
theorem RawBABAInterlacement.overlap_lt_right_span
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement w N start prior second reroute third) :
    B.overlap < third - second := by
  unfold overlap
  have hsecond := B.second_lt_reroute
  have hthird := B.reroute_lt_third
  omega

/-- **Exact endpoint classification of BABA.**  Transporting both raw
last-writer frames gives either an exact lobe write at one of the four
endpoints, or a genuine foreign/foreign restoration crossing with the same
`prior < second < reroute < third` ordering. -/
theorem RawBABAInterlacement.endpoint_lobe_or_foreign_crossing
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement w N start prior second reroute third) :
    Echo.ExactLobeWrite
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) prior ∨
    Echo.ExactLobeWrite
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) reroute ∨
    Echo.ExactLobeWrite
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) second ∨
    Echo.ExactLobeWrite
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) third ∨
    Echo.ForeignRestorationCrossing
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) prior reroute second third := by
  rcases B.leftFrame.endpoint_lobe_or_foreign_restoration hN with
    hprior | hreroute | hleftForeign
  · exact Or.inl hprior
  · exact Or.inr (Or.inl hreroute)
  · rcases B.rightFrame.endpoint_lobe_or_foreign_restoration hN with
      hsecond | hthird | hrightForeign
    · exact Or.inr (Or.inr (Or.inl hsecond))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hthird)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hleftForeign, hrightForeign,
          ⟨B.prior_lt_second, B.second_lt_reroute,
            B.reroute_lt_third⟩⟩)))

/-- A frame opening inside a BABA overlap and closing beyond its left close
creates another BABA with strictly smaller overlap.  This is the raw-time
counterpart of restoration-frame overlap descent. -/
theorem RawBABAInterlacement.crossing_descent
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third opening closing : Nat}
    (B : RawBABAInterlacement w N start prior second reroute third)
    (F : RawLastWriterFrame w N start opening closing)
    (hsecond : second < opening)
    (hopening : opening < reroute)
    (hclosing : reroute < closing) :
    ∃ B' : RawBABAInterlacement
        w N start prior opening reroute closing,
      B'.overlap < B.overlap := by
  have hpriorOpening : prior < opening :=
    Nat.lt_trans B.prior_lt_second hsecond
  have hopenDifferent :
      rawWriterAt w start opening ≠ rawWriterAt w start reroute :=
    B.leftFrame.no_same_writer_between opening
      hpriorOpening hopening F.open_productive
  have hcloseDifferent :
      rawWriterAt w start reroute ≠ rawWriterAt w start closing := by
    intro heq
    apply hopenDifferent
    exact F.same_writer.trans heq.symm
  let B' : RawBABAInterlacement
      w N start prior opening reroute closing := {
    prior_lt_second := hpriorOpening
    second_lt_reroute := hopening
    reroute_lt_third := hclosing
    leftFrame := B.leftFrame
    rightFrame := F
    different_writers := hcloseDifferent
  }
  refine ⟨B', ?_⟩
  unfold RawBABAInterlacement.overlap
  omega

/-- A raw BABA is overlap-minimal if no raw BABA in the same trajectory has
strictly smaller simultaneous-open interval. -/
def RawBABAOverlapMinimal
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement w N start prior second reroute third) : Prop :=
  ∀ a b c d,
    ∀ C : RawBABAInterlacement w N start a b c d,
      C.overlap < B.overlap → False

private theorem exists_rawBABA_overlap_minimal_bounded
    {w : Wiring} {N : Nat} {start : Nat × Tongues} :
    ∀ n,
      (∃ prior second reroute third,
        ∃ B : RawBABAInterlacement
            w N start prior second reroute third,
          B.overlap ≤ n) →
      ∃ prior second reroute third,
        ∃ B : RawBABAInterlacement
            w N start prior second reroute third,
          RawBABAOverlapMinimal B := by
  classical
  intro n
  induction n with
  | zero =>
      rintro ⟨prior, second, reroute, third, B, hzero⟩
      refine ⟨prior, second, reroute, third, B, ?_⟩
      intro a b c d C hlt
      omega
  | succ n ih =>
      intro hex
      by_cases hsmaller : ∃ prior second reroute third,
          ∃ B : RawBABAInterlacement
              w N start prior second reroute third,
            B.overlap ≤ n
      · exact ih hsmaller
      · obtain ⟨prior, second, reroute, third, B, hbound⟩ := hex
        refine ⟨prior, second, reroute, third, B, ?_⟩
        intro a b c d C hlt
        apply hsmaller
        exact ⟨a, b, c, d, C, by omega⟩

/-- Every raw BABA trajectory contains an overlap-minimal BABA.  This is
well-founded induction on a natural-number overlap, not a finite-switch
enumeration. -/
theorem RawBABAInterlacement.exists_overlap_minimal
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement w N start prior second reroute third) :
    ∃ a b c d,
      ∃ C : RawBABAInterlacement w N start a b c d,
        RawBABAOverlapMinimal C := by
  exact exists_rawBABA_overlap_minimal_bounded B.overlap
    ⟨prior, second, reroute, third, B, Nat.le_refl _⟩

/-- At an overlap-minimal raw BABA, no further last-writer frame may open in
the overlap and close beyond its left closing endpoint. -/
theorem RawBABAOverlapMinimal.excludes_crossing_frame
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third opening closing : Nat}
    {B : RawBABAInterlacement w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (F : RawLastWriterFrame w N start opening closing)
    (hsecond : second < opening)
    (hopening : opening < reroute)
    (hclosing : reroute < closing) : False := by
  obtain ⟨B', hlt⟩ := B.crossing_descent F hsecond hopening hclosing
  exact hmin prior opening reroute closing B' hlt

/-- **Raw third-writer theorem.**  A novel third consecutive occurrence of
one writer either exposes a globally first productive writer in the final
interval, or produces a BABA interlacement whose overlap is strictly shorter
than that final writer frame. -/
theorem RawThirdWriterNovelAt.first_charge_or_BABA_strict_descent
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    (∃ reroute,
      second < reroute ∧ reroute < third ∧
      RawFirstWriterAt w N start reroute) ∨
    (∃ prior reroute,
      ∃ B : RawBABAInterlacement
          w N start prior second reroute third,
        B.overlap < third - second) := by
  obtain ⟨reroute, hsecond, hthird, _hprod, hdiff, _hfirstInside,
      hfirst | ⟨prior, F, hprior⟩⟩ :=
    T.first_charge_or_interlaced_writer hN
  · exact Or.inl ⟨reroute, hsecond, hthird, hfirst⟩
  · let B : RawBABAInterlacement
        w N start prior second reroute third := {
      prior_lt_second := hprior
      second_lt_reroute := hsecond
      reroute_lt_third := hthird
      leftFrame := F
      rightFrame := T.secondThirdFrame
      different_writers := hdiff
    }
    exact Or.inr ⟨prior, reroute, B, B.overlap_lt_right_span⟩

/-- **Unconditional raw BABA classification.**  A novel third occurrence
either charges a globally first productive writer, reaches an exact physical
lobe endpoint in the sparse branch-port machine, or exposes a genuine
foreign restoration crossing whose overlap is strictly shorter than the
final writer frame. -/
theorem RawThirdWriterNovelAt.first_charge_or_lobe_or_foreign_crossing
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    (∃ reroute,
      second < reroute ∧ reroute < third ∧
      RawFirstWriterAt w N start reroute) ∨
    (∃ k,
      Echo.ExactLobeWrite
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) k) ∨
    (∃ prior reroute,
      Echo.ForeignRestorationCrossing
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) prior reroute second third ∧
      Echo.crossingOverlap prior reroute second third < third - second) := by
  rcases T.first_charge_or_BABA_strict_descent hN with
    hfirst | ⟨prior, reroute, B, hstrict⟩
  · exact Or.inl hfirst
  · rcases B.endpoint_lobe_or_foreign_crossing hN with
      hprior | hreroute | hsecond | hthird | hcross
    · exact Or.inr (Or.inl ⟨prior, hprior⟩)
    · exact Or.inr (Or.inl ⟨reroute, hreroute⟩)
    · exact Or.inr (Or.inl ⟨second, hsecond⟩)
    · exact Or.inr (Or.inl ⟨third, hthird⟩)
    · exact Or.inr (Or.inr ⟨prior, reroute, hcross, by
        simpa [Echo.crossingOverlap, RawBABAInterlacement.overlap]
          using hstrict⟩)

/-- If first-writer charges are absent from the final interval, the exact raw
residue is therefore an endpoint lobe or a strictly smaller foreign
restoration crossing. -/
theorem RawThirdWriterNovelAt.lobe_or_foreign_crossing_of_no_first_charge
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third)
    (hnoCharge : ∀ t, second < t → t < third →
      ¬ RawFirstWriterAt w N start t) :
    (∃ k,
      Echo.ExactLobeWrite
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) k) ∨
    (∃ prior reroute,
      Echo.ForeignRestorationCrossing
        (rawOverwriteMachine w) (rawOverwriteEntry w N start)
        (rawOverwriteInitial start) prior reroute second third ∧
      Echo.crossingOverlap prior reroute second third < third - second) := by
  rcases T.first_charge_or_lobe_or_foreign_crossing hN with
    ⟨reroute, hsecond, hthird, hfirst⟩ | hlobe | hcross
  · exact (hnoCharge reroute hsecond hthird hfirst).elim
  · exact Or.inl hlobe
  · exact Or.inr hcross

/-- With first-writer charges excluded, the third occurrence therefore
selects an overlap-minimal raw BABA and the strict crossing-frame exclusion
holds there. -/
theorem RawThirdWriterNovelAt.overlap_minimal_BABA_of_no_first_charge
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third)
    (hnoCharge : ∀ t, second < t → t < third →
      ¬ RawFirstWriterAt w N start t) :
    ∃ a b c d,
      ∃ B : RawBABAInterlacement w N start a b c d,
        RawBABAOverlapMinimal B := by
  rcases T.first_charge_or_BABA_strict_descent hN with
    ⟨reroute, hsecond, hthird, hfirst⟩ | ⟨prior, reroute, B, _hlt⟩
  · exact (hnoCharge reroute hsecond hthird hfirst).elim
  · exact B.exists_overlap_minimal



/-- A sparse exact-lobe endpoint is a literal branch-to-branch track edge,
and therefore a genuine two-step physical reflector in the raw Wiring
dynamics.  This theorem uses the sparse overwrite trace only to identify
the old and new selected branches; it does not assert Echo.IsRun. -/
theorem exactLobeWrite_to_raw_direct_lobe_reflector
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {start : Prod Nat Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k) :
    exists outside,
      w.link
          (selectedBranch (tonguesAt w start k)
            (rawWriterAt w start k)) =
        some
          (selectedBranch (tonguesAt w start (k + 1))
            (rawWriterAt w start k)) /\
      w.link
          (selectedBranch (tonguesAt w start (k + 1))
            (rawWriterAt w start k)) =
        some
          (selectedBranch (tonguesAt w start k)
            (rawWriterAt w start k)) /\
      w.link (3 * rawWriterAt w start k) = some outside /\
      IsReflector w (3 * rawWriterAt w start k) outside 2
        (fun _ => True)
        (fun state => flipAt state (rawWriterAt w start k)) := by
  let C := rawWriterAt w start k
  let oldBranch := selectedBranch (tonguesAt w start k) C
  let newBranch := selectedBranch (tonguesAt w start (k + 1)) C
  have hold :
      Echo.oldSlot (rawOverwriteMachine w)
          (rawOverwriteEntry w N start) (rawOverwriteInitial start) k =
        oldBranch := by
    simpa [oldBranch, C] using
      rawOverwrite_oldSlot_eq_selected hN hprod
  have hnew :
      rawOverwriteEntry w N start (k + 1) = newBranch := by
    simp [rawOverwriteEntry, hprod, newBranch, C]
  have hwire : wireBar w oldBranch = newBranch := by
    have h := hlobe.1
    rw [hnew, hold] at h
    exact h.symm
  have hnewOld : Not (newBranch = oldBranch) := by
    have hsparse :=
      rawProductiveAt_is_rawOverwriteProductive hN hprod
    change Not
      (rawOverwriteEntry w N start (k + 1) =
        Echo.oldSlot (rawOverwriteMachine w)
          (rawOverwriteEntry w N start) (rawOverwriteInitial start) k)
      at hsparse
    simpa [hnew, hold] using hsparse
  have hlink : w.link oldBranch = some newBranch := by
    cases h : w.link oldBranch with
    | none =>
        have hfixed : wireBar w oldBranch = oldBranch :=
          wireBar_of_unlinked h
        exact (hnewOld (hwire.symm.trans hfixed)).elim
    | some q =>
        have hq : q = newBranch :=
          (wireBar_of_link h).symm.trans hwire
        simpa [hq] using h
  have hback : w.link newBranch = some oldBranch :=
    w.symm oldBranch newBranch hlink
  let hmouthData := rawProductiveAt_fixed_stem_successor hN hprod
  let next : Prod Nat Tongues := Classical.choose hmouthData
  have hmouth : w.link (3 * C) = some next.1 := by
    simpa [C] using
      (Classical.choose_spec hmouthData).2
  have holdBranch : Not (oldBranch % 3 = 0) := by
    simpa [oldBranch, C] using
      selectedBranch_is_branch (tonguesAt w start k) C
  have hnewBranch : Not (newBranch % 3 = 0) := by
    simpa [newBranch, C] using
      selectedBranch_is_branch (tonguesAt w start (k + 1)) C
  have holdSwitch : (3 * C) / 3 = oldBranch / 3 := by
    have hselected :=
      selectedBranch_switch (tonguesAt w start k) C
    calc
      (3 * C) / 3 = C := by omega
      _ = oldBranch / 3 := by simpa [oldBranch] using hselected.symm
  have hnewSwitch : (3 * C) / 3 = newBranch / 3 := by
    have hselected :=
      selectedBranch_switch (tonguesAt w start (k + 1)) C
    calc
      (3 * C) / 3 = C := by omega
      _ = newBranch / 3 := by simpa [newBranch] using hselected.symm
  have hreflector :
      IsReflector w (3 * C) next.1 2
        (fun _ => True) (fun state => flipAt state C) := by
    have hphysical := stem_lobe_isReflector w
      (p := 3 * C) (x := oldBranch) (q := newBranch)
      (outside := next.1) []
      (by omega) holdBranch hnewBranch holdSwitch hnewSwitch
      (Ne.symm hnewOld)
      (by simp [SwitchSimple, passageSwitch])
      (by simp [LinkedPassages])
      (by simpa [lastPassageExit] using hlink)
      hmouth
    simpa [PassagesGrooved] using hphysical
  refine Exists.intro next.1 ?_
  exact And.intro
    (by simpa [oldBranch, newBranch, C] using hlink)
    (And.intro
      (by simpa [oldBranch, newBranch, C] using hback)
      (And.intro
        (by simpa [C] using hmouth)
        (by simpa [C] using hreflector)))
end GeneralN
