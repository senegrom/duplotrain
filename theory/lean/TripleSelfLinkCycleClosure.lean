import TripleSelfLinkFirstLap

/-!
# Closing the raw-cycle branch through a self-link

The local two-vector tail from `TripleSelfLinkFirstLap` can begin partway
around a raw periodic orbit.  The first theorem below rotates that tail back
to the recorded base of the period.  This is the timing bridge needed by the
literal five-close accounting theorem: once a two-vector trap is reached at
any point of the first lap, the whole periodic suffix from the selected close
already has the same two-vector cover.
-/

namespace GeneralN

/-! ## Rotate a quantitative tail back around a raw period -/

/-- If a two-vector tail is reached somewhere on a positive raw period, then
the period base itself is a two-vector tail with the same two phases.  The
offset need not lie in the first lap: it is reduced modulo the period first.
This is a complete-configuration argument, so no `getD` default is used. -/
theorem RawTwoVectorTail.rotate_back_to_period_base
    {w : Wiring} {N : Nat} {start cycleStart : Nat × Tongues}
    {base period offset : Nat}
    (P : RawTwoVectorTail w N start)
    (hbase : stepN w base start = some cycleStart)
    (hperiodPositive : 0 < period)
    (hperiod : stepN w period cycleStart = some cycleStart)
    (hoffset : stepN w offset cycleStart = some P.localStart) :
    Nonempty (RawTwoVectorTail w N start) := by
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
  refine ⟨{
    shift := base
    localStart := cycleStart
    phase₀ := P.phase₀
    phase₁ := P.phase₁
    reached := hbase
    live := hcycleLive
    two_vectors := ?_
  }⟩
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

/-! ## Install the compatible self-link pair on the raw orbit -/

/-- The explicit empty-runway self-link reflector comes with its support
grooved in the selected state, and every opposite manufactured reflector
automatically avoids that support.  The richer conclusion is needed because
the older `Nonempty` constructor intentionally hid the witness fields. -/
theorem compatible_self_link_core
    {w : Wiring} {outside stem branch : Nat} {state : Tongues}
    (A : ManufacturedReflector w outside stem)
    (hbranch : branch % 3 ≠ 0)
    (hself : w.link branch = some branch)
    (hmouth : w.link (3 * (branch / 3)) = some outside)
    (hselected : state (branch / 3) = bval branch) :
    ∃ R : ManufacturedStayReflector w (3 * (branch / 3)) outside,
      PathGrooves (ManufacturedReflector.stay R).toSupported.paths state ∧
      A.toSupported.action.Avoids
        (ManufacturedReflector.stay R).toSupported.paths := by
  have hstemMod : (3 * (branch / 3)) % 3 = 0 := by omega
  have hstemDiv : (3 * (branch / 3)) / 3 = branch / 3 := by omega
  have hforward : arrive state (3 * (branch / 3)) =
      (branch, state) := by
    simp [arrive, hstemMod, hstemDiv, hselected,
      branchPort_bval hbranch]
  have hback : arrive state branch =
      (3 * (branch / 3), state) := by
    have hpin : pin state branch = state := pin_of_agrees hselected
    simp [arrive, hbranch, hpin]
  have hentry : w.link outside = some (3 * (branch / 3)) :=
    w.symm _ _ hmouth
  let R : ManufacturedStayReflector w
      (3 * (branch / 3)) outside := {
    base := state
    mouthState := state
    returnState := state
    runway := []
    mouth := 3 * (branch / 3)
    arm := branch
    runwayTrace := PhysicalTrace.nil _
    coreTrace := PhysicalTrace.cons hforward hself (PhysicalTrace.nil _)
    simple := by simp [SwitchSimple, passageSwitch]
    stemEndpoint := Or.inl (by omega)
    selfLink := hself
    entryEdge := hentry
  }
  have hgrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths state := by
    change PathGrooves [[], [(3 * (branch / 3), branch)]] state
    apply pathGrooves_pair.mpr
    exact ⟨(by intro passage hmem; cases hmem),
      passagesGrooved_singleton.mpr hback⟩
  have havoids : A.toSupported.action.Avoids
      (ManufacturedReflector.stay R).toSupported.paths := by
    change A.toSupported.action.Avoids
      [[], [(3 * (branch / 3), branch)]]
    exact A.action_avoids_self_link_core hbranch hself
  exact ⟨R, hgrooves, havoids⟩

/-- Field-exposing form of the quantitative pair constructor.  The earlier
checkpoint deliberately returned `Nonempty`; raw-period rotation additionally
needs the exact local start which that existential witness records. -/
theorem rawTwoVectorTail_of_self_link_pair_exact
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {outside stem : Nat}
    (A : ManufacturedReflector w outside stem)
    (R : ManufacturedStayReflector w stem outside)
    (state : Tongues) (shift : Nat)
    (hreach : stepN w shift start = some (outside, state))
    (hA : PathGrooves A.toSupported.paths state)
    (hR : PathGrooves (ManufacturedReflector.stay R).toSupported.paths
      state)
    (hAR : A.toSupported.action.Avoids
      (ManufacturedReflector.stay R).toSupported.paths) :
    ∃ P : RawTwoVectorTail w N start,
      P.shift = shift ∧ P.localStart = (outside, state) := by
  let B : ManufacturedReflector w stem outside := .stay R
  let period := 2 * (A.toSupported.travel + B.toSupported.travel)
  have hBA : B.toSupported.action.Avoids A.toSupported.paths := by
    trivial
  have hperiodPositive : 0 < period := by
    have hApos : 0 < A.toSupported.travel := A.travel_pos
    have hBpos : 0 < B.toSupported.travel := B.travel_pos
    dsimp [period]
    omega
  have hperiod : stepN w period (outside, state) =
      some (outside, state) := by
    dsimp [period]
    exact A.toSupported.paired_period B.toSupported hAR hBA
      state hA hR
  have hlive : ∀ d, ∃ finish,
      stepN w d (outside, state) = some finish := by
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
  let phase₀ := VectorCount.restrict N state
  let phase₁ := VectorCount.restrict N
    (A.toSupported.action.apply state)
  let P : RawTwoVectorTail w N start := {
    shift := shift
    localStart := (outside, state)
    phase₀ := phase₀
    phase₁ := phase₁
    reached := hreach
    live := hlive
    two_vectors := by
      intro d
      have hfour := manufactured_pair_all_time_four_phase_tongues
        A B state hA hR hAR hBA d
      have hBapply : ∀ u, B.toSupported.action.apply u = u := by
        intro u
        simp [B, ManufacturedReflector.toSupported,
          ManufacturedStayReflector.toSupported, LocalAction.apply]
      have hphase : tonguesAt w (outside, state) d = state ∨
          tonguesAt w (outside, state) d =
            A.toSupported.action.apply state := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hfour
        rcases hfour with hzero | hone | hstay | hrestore
        · exact Or.inl hzero
        · exact Or.inr hone
        · exact Or.inr (hstay.trans (hBapply _))
        · apply Or.inl
          calc
            tonguesAt w (outside, state) d =
                A.toSupported.action.apply
                  (B.toSupported.action.apply
                    (A.toSupported.action.apply state)) := hrestore
            _ = A.toSupported.action.apply
                  (A.toSupported.action.apply state) := by rw [hBapply]
            _ = state := A.toSupported.action.involutive state
      rcases hphase with hzero | hone
      · simp [restrictedTonguesAt, phase₀, phase₁, hzero]
      · simp [restrictedTonguesAt, phase₀, phase₁, hone]
  }
  exact ⟨P, rfl, rfl⟩

/-- If the outside-oriented first revisit manufactures an opposite reflector
whose activated state still selects the self-linked arm, then the raw cycle
has a two-vector tail beginning already at its recorded close.  The proof
reaches the opposite reflector, bounces across the self-link, installs the
compatible pair, and rotates the resulting tail backwards around the raw
period. -/
theorem RawCycleThroughSelfLink.close_tail_of_opposite_reflector
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close)
    {outside : Nat} {atRepeat : Nat × Tongues} {visited : Nat}
    (A : ManufacturedReflector w outside (3 * (R.branch / 3)))
    (state : Tongues) (backSteps : Nat)
    (hmouth : w.link (3 * (R.branch / 3)) = some outside)
    (hvisited : stepN w visited (outside, R.state) = some atRepeat)
    (hA : PathGrooves A.toSupported.paths state)
    (hback : stepN w backSteps atRepeat =
      some (3 * (R.branch / 3), state))
    (hselected : state (R.branch / 3) = bval R.branch) :
    Nonempty (RawTwoVectorTail w N start) := by
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
  exact P.rotate_back_to_period_base R.close_at R.period_positive
    R.cycle htoPair'

end GeneralN
