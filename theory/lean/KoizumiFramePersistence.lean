import KoizumiRawExtraction

/-!
# Self-pivots are unavoidable inside a repeated-writer frame

After a productive visit to switch `C`, the train's next raw entry is joined
by the fixed external track edge to `C`'s stem.  A quiet step merely reroots
the same selected curve, and a productive non-self pivot contains the whole
old train curve in the new one.  Therefore the stem remains on the train
curve until a self-pivot removes part of that curve.

The main theorem below is a raw, finite-time statement: between any two
productive visits to the same writer, either the closing visit is a
self-pivot or an interior productive visit is.  This is the global bridge
needed to organise repeated novelties into shrink/grow restoration frames.
-/

namespace GeneralN

/-- The productive pivot at raw time `k` is a self-pivot of the train's
currently selected curve.  The definition is meaningful without a liveness
premise because raw accessors use the initial configuration as default; all
theorems below establish liveness explicitly. -/
def RawTrainCurveSelfAt
    (w : Wiring) (start : Nat × Tongues) (k : Nat) : Prop :=
  CurveReach w (tonguesAt w start k) (rawEntryAt w start k)
    (3 * rawWriterAt w start k)

private theorem frame_stepN_prefix_some
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

/-- A live nonproductive raw step changes no tongue, including outside the
represented range. -/
private theorem quiet_step_tongues_eq
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start cur next : Nat × Tongues} {k : Nat}
    (hcur : stepN w k start = some cur)
    (hnext : stepN w (k + 1) start = some next)
    (hstep : step w cur = some next)
    (hquiet : ¬ RawProductiveAt w N start k) :
    next.2 = cur.2 := by
  have hparts := step_some_parts hstep
  have hwriterLt : cur.1 / 3 < N := by
    have hexitLt := (hN _ _ hparts.1).1
    rw [← arrive_exit_switch cur.2 cur.1]
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    simpa [exitPort, Nat.mul_comm] using hexitLt
  have hwriter : next.2 (cur.1 / 3) = cur.2 (cur.1 / 3) := by
    by_cases heq : next.2 (cur.1 / 3) = cur.2 (cur.1 / 3)
    · exact heq
    · exact (hquiet (raw_tongue_change_is_productive_writer
        hwriterLt hcur hnext hstep heq).1).elim
  funext j
  by_cases hj : j = cur.1 / 3
  · simpa [hj] using hwriter
  · have harrived : next.2 = (arrive cur.2 cur.1).2 := by
      simpa [arrivedTongues] using hparts.2
    rw [harrived]
    exact arrive_preserves_other rfl hj

/-- A quiet raw step reroots, but does not change, the selected train curve. -/
private theorem quiet_step_curve_forward
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start cur next : Nat × Tongues} {k p : Nat}
    (hcur : stepN w k start = some cur)
    (hnext : stepN w (k + 1) start = some next)
    (hstep : step w cur = some next)
    (hquiet : ¬ RawProductiveAt w N start k)
    (hp : CurveReach w cur.2 cur.1 p) :
    CurveReach w next.2 next.1 p := by
  have hstate := quiet_step_tongues_eq hN hcur hnext hstep hquiet
  have hparts := step_some_parts hstep
  have hinternal : InternalCurveEdge cur.2 cur.1 (exitPort cur) := by
    unfold InternalCurveEdge
    apply Prod.ext
    · rfl
    · change arrivedTongues cur = cur.2
      rw [← hparts.2, hstate]
  have hrootNext : CurveReach w cur.2 cur.1 next.1 :=
    CurveReach.step
      (curveReach_edge (Or.inr hinternal))
      (Or.inl hparts.1)
  have hnextRoot : CurveReach w cur.2 next.1 cur.1 :=
    curveReach_symm hrootNext
  rw [hstate]
  exact curveReach_trans hnextRoot hp

/-- One live step preserves every point of the old train curve provided a
productive step is not a self-pivot. -/
theorem rawCurveReach_persists_one_step_without_self
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k p : Nat}
    (hlive : (stepN w (k + 1) start).isSome)
    (havoid : RawProductiveAt w N start k →
      ¬ RawTrainCurveSelfAt w start k)
    (hp : CurveReach w (tonguesAt w start k)
      (rawEntryAt w start k) p) :
    CurveReach w (tonguesAt w start (k + 1))
      (rawEntryAt w start (k + 1)) p := by
  obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
    live_successor_configs hlive
  by_cases hprod : RawProductiveAt w N start k
  · obtain ⟨before, after, C, hC, hbefore, hafter, _hphysical,
        _hentry, _hflip, hself | hgrowth⟩ :=
      rawProductiveAt_self_or_strict_curve_growth hN hprod
    · have hbeforeEq : before = cur := by
        have hs : some before = some cur := hbefore.symm.trans hcur
        exact Option.some.inj hs
      subst before
      have hselfRaw : RawTrainCurveSelfAt w start k := by
        unfold RawTrainCurveSelfAt
        simpa [tonguesAt, rawEntryAt, rawWriterAt, hcur, hC] using hself
      exact (havoid hprod hselfRaw).elim
    · have hbeforeEq : before = cur := by
        have hs : some before = some cur := hbefore.symm.trans hcur
        exact Option.some.inj hs
      have hafterEq : after = next := by
        have hs : some after = some next := hafter.symm.trans hnext
        exact Option.some.inj hs
      subst before
      subst after
      have hpOld : CurveReach w cur.2 cur.1 p := by
        simpa [tonguesAt, rawEntryAt, hcur] using hp
      have hpAtOldRoot : CurveReach w next.2 cur.1 p :=
        hgrowth.1 p hpOld
      have hexit : exitPort cur = 3 * C := by
        unfold exitPort
        rw [_hentry, arrive_unmatched_pivots]
      have hlink : w.link (3 * C) = some next.1 := by
        have hparts := step_some_parts _hphysical
        simpa [hexit] using hparts.1
      have hnextStem : CurveReach w next.2 next.1 (3 * C) :=
        curveReach_edge (Or.inl (w.symm _ _ hlink))
      have hstemOld : CurveReach w next.2 (3 * C) cur.1 := by
        apply curveReach_edge
        right
        unfold InternalCurveEdge
        rw [_hflip, _hentry]
        exact arrive_pivot_back cur.2 C
      have hnextOld : CurveReach w next.2 next.1 cur.1 :=
        curveReach_trans hnextStem hstemOld
      have hresult := curveReach_trans hnextOld hpAtOldRoot
      simpa [tonguesAt, rawEntryAt, hnext] using hresult
  · have hforward := quiet_step_curve_forward
      hN hcur hnext hstep hprod
      (p := p) (by simpa [tonguesAt, rawEntryAt, hcur] using hp)
    simpa [tonguesAt, rawEntryAt, hnext] using hforward

/-- Curve membership persists through a finite interval containing no
productive self-pivot.  Quiet moves and non-self growth may be interleaved
arbitrarily. -/
theorem rawCurveReach_persists_interval_without_self
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {first span p : Nat}
    (hlive : (stepN w (first + span) start).isSome)
    (havoid : ∀ j, first ≤ j → j < first + span →
      RawProductiveAt w N start j →
      ¬ RawTrainCurveSelfAt w start j)
    (hp : CurveReach w (tonguesAt w start first)
      (rawEntryAt w start first) p) :
    CurveReach w (tonguesAt w start (first + span))
      (rawEntryAt w start (first + span)) p := by
  induction span with
  | zero => simpa using hp
  | succ n ih =>
      have hprefixSome : (stepN w (first + n) start).isSome := by
        cases hfinish : stepN w (first + (n + 1)) start with
        | none => simp [hfinish] at hlive
        | some finish =>
            obtain ⟨middle, hmiddle⟩ := frame_stepN_prefix_some
              (d := first + n) (K := first + (n + 1))
              (by omega) hfinish
            simp [hmiddle]
      have hprefix := ih hprefixSome
        (fun j hj hbound hprod =>
          havoid j hj (by omega) hprod)
      have hlastLive :
          (stepN w ((first + n) + 1) start).isSome := by
        have harith : (first + n) + 1 = first + (n + 1) := by omega
        simpa [harith] using hlive
      have hlast := rawCurveReach_persists_one_step_without_self
        hN hlastLive
        (fun hprod => havoid (first + n) (by omega) (by omega) hprod)
        hprefix
      simpa [Nat.add_assoc] using hlast

/-- Immediately after a productive write, the fixed external stem edge puts
that writer's stem on the selected train curve. -/
theorem rawProductiveAt_post_writer_stem_reachable
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    CurveReach w (tonguesAt w start (k + 1))
      (rawEntryAt w start (k + 1))
      (3 * rawWriterAt w start k) := by
  obtain ⟨P⟩ := rawProductiveAt_koizumiPivot hN hprod
  have hlink : w.link (3 * P.writer) = some P.after.1 := by
    have hparts := step_some_parts P.physical_step
    simpa [P.exited_stem] using hparts.1
  have hback : w.link P.after.1 = some (3 * P.writer) :=
    w.symm _ _ hlink
  have hreach : CurveReach w P.after.2 P.after.1 (3 * P.writer) :=
    curveReach_edge (Or.inl hback)
  simpa [tonguesAt, rawEntryAt, P.after_at, P.writer_eq] using hreach

/-- **Repeated writers force a self-pivot.**

For any two productive visits to the same switch, either the closing visit
is a self-pivot or some productive self-pivot lies strictly between them.
No novelty, recurrence, or minimality assumption is needed. -/
theorem repeated_writer_close_self_or_interior_self
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {left right : Nat}
    (horder : left < right)
    (hleft : RawProductiveAt w N start left)
    (hright : RawProductiveAt w N start right)
    (hsame : rawWriterAt w start left = rawWriterAt w start right) :
    RawTrainCurveSelfAt w start right ∨
      ∃ j, left < j ∧ j < right ∧
        RawProductiveAt w N start j ∧
        RawTrainCurveSelfAt w start j := by
  by_cases hinterior : ∃ j, left < j ∧ j < right ∧
      RawProductiveAt w N start j ∧
      RawTrainCurveSelfAt w start j
  · exact Or.inr hinterior
  · left
    have hrightConfig : ∃ finish, stepN w right start = some finish := by
      obtain ⟨last, hlast⟩ := Option.isSome_iff_exists.mp hright.1
      exact frame_stepN_prefix_some
        (d := right) (K := right + 1) (by omega) hlast
    obtain ⟨finish, hfinish⟩ := hrightConfig
    let span := right - (left + 1)
    have hsum : left + 1 + span = right := by
      dsimp [span]
      omega
    have hstem := rawProductiveAt_post_writer_stem_reachable hN hleft
    have hpersist := rawCurveReach_persists_interval_without_self
      hN (first := left + 1) (span := span)
      (p := 3 * rawWriterAt w start left)
      (by simp [hsum, hfinish])
      (fun j hjlo hjhi hprod => by
        intro hself
        apply hinterior
        exact ⟨j, by omega, by simpa [hsum] using hjhi, hprod, hself⟩)
      hstem
    unfold RawTrainCurveSelfAt
    rw [← hsame]
    simpa [hsum] using hpersist

end GeneralN
