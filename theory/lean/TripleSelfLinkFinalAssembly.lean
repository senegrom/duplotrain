import TripleSelfLinkSelectedClosure

/-!
# Final quantitative assembly for the selected self-link cycle

This file consumes the selected-state theorem without adding an arm-selection
hypothesis.  It also exposes the exact shift hidden by the earlier Nonempty
rotation theorem, so the resulting two-vector tail can be fed directly to the
literal five-close accounting theorem.
-/

namespace GeneralN

theorem RawTwoVectorTail.rotate_back_to_period_base_exact
    {w : Wiring} {N : Nat} {start cycleStart : Nat × Tongues}
    {base period offset : Nat}
    (P : RawTwoVectorTail w N start)
    (hbase : stepN w base start = some cycleStart)
    (hperiodPositive : 0 < period)
    (hperiod : stepN w period cycleStart = some cycleStart)
    (hoffset : stepN w offset cycleStart = some P.localStart) :
    ∃ Q : RawTwoVectorTail w N start, Q.shift = base := by
  let q := offset / period
  let r := offset % period
  have hrlt : r < period := by
    dsimp [r]
    exact Nat.mod_lt offset hperiodPositive
  have hoffsetEq : offset = q * period + r := by
    dsimp [q, r]
    have hdiv := Nat.div_add_mod offset period
    rw [Nat.mul_comm period (offset / period)] at hdiv
    omega
  have hrepeat : stepN w (q * period) cycleStart = some cycleStart :=
    stepN_mul_period_pair_novelty hperiod q
  have hrreach : stepN w r cycleStart = some P.localStart := by
    have hsame : stepN w offset cycleStart = stepN w r cycleStart := by
      rw [hoffsetEq, stepN_add, hrepeat]
      simp only [Option.bind_some]
    rw [← hsame]
    exact hoffset
  have hcycleLive : ∀ d, ∃ finish,
      stepN w d cycleStart = some finish := by
    intro d
    have hfar := stepN_mul_period_pair_novelty hperiod (d + 1)
    have hp : 1 ≤ period := Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hperiodPositive)
    have hbound : d ≤ (d + 1) * period := by
      calc
        d ≤ d + 1 := Nat.le_succ d
        _ = (d + 1) * 1 := by simp
        _ ≤ (d + 1) * period := Nat.mul_le_mul_left (d + 1) hp
    exact stepN_prefix_some hbound hfar
  let Q : RawTwoVectorTail w N start := {
    shift := base
    localStart := cycleStart
    phase₀ := P.phase₀
    phase₁ := P.phase₁
    reached := hbase
    live := hcycleLive
    two_vectors := by
      intro d
      by_cases hrd : r ≤ d
      · let delta := d - r
        obtain ⟨finish, hfinish⟩ := P.live delta
        have htransport := restrictedTonguesAt_add_of_reach
          (N := N) hrreach hfinish
        have hsum : r + delta = d := by
          dsimp [delta]
          omega
        rw [hsum] at htransport
        rw [htransport]
        exact P.two_vectors delta
      · have hdr : d < r := Nat.lt_of_not_ge hrd
        let delta := (period - r) + d
        have hrle : r ≤ period := Nat.le_of_lt hrlt
        have hleft := stepN_add w r delta cycleStart
        rw [hrreach] at hleft
        simp only [Option.bind_some] at hleft
        have hright := stepN_add w period d cycleStart
        rw [hperiod] at hright
        simp only [Option.bind_some] at hright
        have hsum : r + delta = period + d := by
          dsimp [delta]
          omega
        have hlocalToD : stepN w delta P.localStart =
            stepN w d cycleStart := by
          calc
            stepN w delta P.localStart =
                stepN w (r + delta) cycleStart := hleft.symm
            _ = stepN w (period + d) cycleStart := by rw [hsum]
            _ = stepN w d cycleStart := hright
        obtain ⟨finish, hfinish⟩ := hcycleLive d
        have hlocalFinish : stepN w delta P.localStart = some finish :=
          hlocalToD.trans hfinish
        have hvector : restrictedTonguesAt w N cycleStart d =
            restrictedTonguesAt w N P.localStart delta := by
          simp [restrictedTonguesAt, tonguesAt, hfinish, hlocalFinish]
        rw [hvector]
        exact P.two_vectors delta
  }
  exact ⟨Q, rfl⟩

/-- Exact quantitative closure of the opposite-reflector outcome.  The tail
starts at the raw cycle's recorded close. -/
theorem RawCycleThroughSelfLink.close_tail_of_opposite_reflector_exact
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close)
    {outside : Nat} {atRepeat : Nat × Tongues} {visited : Nat}
    (A : ManufacturedReflector w outside (3 * (R.branch / 3)))
    (state : Tongues) (backSteps : Nat)
    (hmouth : w.link (3 * (R.branch / 3)) = some outside)
    (hvisited : stepN w visited (outside, R.state) = some atRepeat)
    (hA : PathGrooves A.toSupported.paths state)
    (hbase : A.baseState = R.state)
    (hstate : state = A.activatedState)
    (hback : stepN w backSteps atRepeat =
      some (3 * (R.branch / 3), state)) :
    ∃ P : RawTwoVectorTail w N start, P.shift = close := by
  have hselected : state (R.branch / 3) = bval R.branch :=
    R.opposite_reflector_state_selected A state hbase hstate
  obtain ⟨outside', hmouth', houtside'⟩ := R.branch_step
  have houtsideEq : outside = outside' :=
    Option.some.inj (hmouth.symm.trans hmouth')
  subst outside'
  obtain ⟨S, hS, hAS⟩ := compatible_self_link_core A
    R.branch_port R.self_link hmouth hselected
  have hbounce : stepN w 2 (3 * (R.branch / 3), state) =
      some (outside, state) :=
    self_link_exact_two_step_bounce R.branch_port R.self_link
      hmouth hselected
  let outsideOffset := R.offset + 1
  have htoOutside : stepN w outsideOffset R.closeConfig =
      some (outside, R.state) := by
    dsimp [outsideOffset]
    rw [stepN_add, R.self_at]
    exact houtside'
  let repeatOffset := outsideOffset + visited
  have htoRepeat : stepN w repeatOffset R.closeConfig =
      some atRepeat := by
    dsimp [repeatOffset]
    rw [stepN_add, htoOutside]
    exact hvisited
  let stemOffset := repeatOffset + backSteps
  have htoStem : stepN w stemOffset R.closeConfig =
      some (3 * (R.branch / 3), state) := by
    dsimp [stemOffset]
    rw [stepN_add, htoRepeat]
    exact hback
  let pairOffset := stemOffset + 2
  have htoPair : stepN w pairOffset R.closeConfig =
      some (outside, state) := by
    dsimp [pairOffset]
    rw [stepN_add, htoStem]
    exact hbounce
  let shift := close + pairOffset
  have hreach : stepN w shift start = some (outside, state) := by
    dsimp [shift]
    rw [stepN_add, R.close_at]
    exact htoPair
  obtain ⟨P, _hshift, hlocal⟩ := rawTwoVectorTail_of_self_link_pair_exact
    (N := N) A S state shift hreach hA hS hAS
  have htoPair' : stepN w pairOffset R.closeConfig =
      some P.localStart := by
    rw [hlocal]
    exact htoPair
  exact P.rotate_back_to_period_base_exact R.close_at R.period_positive
    R.cycle htoPair'

/-- The exact tail starts early enough for the literal five-close theorem. -/
theorem RawCycleThroughSelfLink.five_close_cover_of_opposite_reflector
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (F : FiveFixedStemNovelFrames w N start)
    (T : FiveFrameTripleCase w N start
      F.z₀ F.z₁ F.z₂ F.z₃ F.z₄)
    (S : SelectedFiveFrameABCABC T)
    (R : RawCycleThroughSelfLink w start
      (T.frames.closingAt S.i0))
    {outside : Nat} {atRepeat : Nat × Tongues} {visited : Nat}
    (A : ManufacturedReflector w outside (3 * (R.branch / 3)))
    (state : Tongues) (backSteps : Nat)
    (hmouth : w.link (3 * (R.branch / 3)) = some outside)
    (hvisited : stepN w visited (outside, R.state) = some atRepeat)
    (hA : PathGrooves A.toSupported.paths state)
    (hbase : A.baseState = R.state)
    (hstate : state = A.activatedState)
    (hback : stepN w backSteps atRepeat =
      some (3 * (R.branch / 3), state)) :
    NoveltyCoverOn w N start F.closePostTimes [] 4 := by
  obtain ⟨P, hshift⟩ :=
    R.close_tail_of_opposite_reflector_exact
      (N := N) A state backSteps hmouth hvisited hA hbase hstate hback
  apply five_close_noveltyCoverOn_four_of_two_vector_tail F T S P
  rw [hshift]
  omega

end GeneralN
