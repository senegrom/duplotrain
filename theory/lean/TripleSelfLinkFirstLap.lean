import TripleSelfLinkRawTail

/-!
# Closing the first lap through the self-link

The outside-oriented first revisit from `TripleSelfLinkRawTail` manufactures
a reflector opposite the self-link stem.  This file turns the compatible
case into an actual `RawTwoVectorTail` and isolates the only incompatible
case as a concrete visit to the self-link switch during the manufactured
exploration.
-/

namespace GeneralN

/-! ## A manufactured action cannot flip the self-linked core -/

/-- A flip reflector whose entry edge is the stem edge of a self-linked
branch cannot have that branch's switch as its action switch.  Otherwise the
self-linked branch is one of the two candy arms.  At the first arm the next
candy passage immediately repeats the mouth switch; at the second arm the
last candy passage does so.  The empty-candy cases contradict `arms_ne`
directly. -/
theorem ManufacturedFlipReflector.actionSwitch_ne_self_link
    {w : Wiring} {outside stem branch : Nat}
    (A : ManufacturedFlipReflector w outside stem)
    (hbranch : branch % 3 ≠ 0)
    (hself : w.link branch = some branch) :
    A.actionSwitch ≠ branch / 3 := by
  intro heq
  have hfirstSwitch : A.firstArm / 3 = branch / 3 := by
    rw [A.firstArm_switch, heq]
  have hsecondSwitch : A.secondArm / 3 = branch / 3 := by
    rw [A.secondArm_switch, heq]
  have hcases : branch = A.firstArm ∨ branch = A.secondArm := by
    have hfirstBranch : A.firstArm % 3 ≠ 0 := A.firstArm_branch
    have hsecondBranch : A.secondArm % 3 ≠ 0 := A.secondArm_branch
    have harms : A.firstArm ≠ A.secondArm := A.arms_ne
    omega
  rcases hcases with hfirst | hsecond
  · subst branch
    cases hcandy : A.candy with
    | nil =>
        have hlast : w.link A.firstArm = some A.secondArm := by
          simpa [hcandy, lastPassageExit] using A.candyTrace.last_link
        rw [hself] at hlast
        exact A.arms_ne (Option.some.inj hlast)
    | cons passage rest =>
        rcases passage with ⟨p, x⟩
        have hlinked : w.link A.firstArm = some p := by
          have h := A.candyTrace.linked
          rw [hcandy] at h
          change w.link A.firstArm = some p ∧
            LinkedPassages w ((p, x) :: rest) at h
          exact h.1
        have hpLink : w.link p = some A.firstArm :=
          w.symm A.firstArm p hlinked
        have hp : p = A.firstArm :=
          w.link_injective hpLink hself
        have hforeign := A.support_foreign A.candy (by simp)
          (p, x) (by simp [hcandy])
        apply hforeign
        simp [passageSwitch, hp, A.firstArm_switch]
  · subst branch
    cases hcandy : A.candy with
    | nil =>
        have hlast : w.link A.firstArm = some A.secondArm := by
          simpa [hcandy, lastPassageExit] using A.candyTrace.last_link
        have heqArms : A.firstArm = A.secondArm :=
          w.link_injective hlast hself
        exact A.arms_ne heqArms
    | cons passage rest =>
        rcases passage with ⟨p, x⟩
        have htrace := A.candyTrace
        rw [hcandy] at htrace
        cases htrace with
        | cons _harrive _hlink tail =>
            have hlastLink :
                w.link (lastPassageExit x rest) = some A.secondArm :=
              tail.last_link
            have hlastExit :
                lastPassageExit x rest = A.secondArm :=
              w.link_injective hlastLink hself
            have hmem : A.actionSwitch ∈
                (((p, x) :: rest).map passageSwitch) := by
              have hm := tail.last_exit_switch_mem
              simpa [hlastExit, A.secondArm_switch] using hm
            obtain ⟨old, hold, holdSwitch⟩ := List.mem_map.mp hmem
            have hforeign := A.support_foreign A.candy (by simp)
              old (by simpa [hcandy] using hold)
            exact hforeign holdSwitch

/-- Consequently the local action of any manufactured reflector opposite a
self-link avoids the self-link stay reflector's two support paths. -/
theorem ManufacturedReflector.action_avoids_self_link_core
    {w : Wiring} {outside stem branch : Nat}
    (A : ManufacturedReflector w outside stem)
    (hbranch : branch % 3 ≠ 0)
    (hself : w.link branch = some branch) :
    A.toSupported.action.Avoids
      [[], [(3 * (branch / 3), branch)]] := by
  cases A with
  | stay R => trivial
  | flip R =>
      have hne := R.actionSwitch_ne_self_link hbranch hself
      simp [ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported,
        LocalAction.Avoids, passageSwitch, Ne.symm hne]

/-! ## Compatible opposite reflector plus self-link -/

/-- The compatible opposite-reflector/self-link pair is live forever and
has only the incoming vector and the opposite reflector's one-action vector
at every raw time. -/
theorem rawTwoVectorTail_of_self_link_pair
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
    Nonempty (RawTwoVectorTail w N start) := by
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
    have hbound : d ≤ (d + 1) * period := by
      have hp : 1 ≤ period := Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hperiodPositive)
      calc
        d ≤ d + 1 := Nat.le_succ d
        _ = (d + 1) * 1 := by simp
        _ ≤ (d + 1) * period := Nat.mul_le_mul_left (d + 1) hp
    exact stepN_prefix_some hbound hfar
  let phase₀ := VectorCount.restrict N state
  let phase₁ := VectorCount.restrict N
    (A.toSupported.action.apply state)
  refine ⟨{
    shift := shift
    localStart := (outside, state)
    phase₀ := phase₀
    phase₁ := phase₁
    reached := hreach
    live := hlive
    two_vectors := ?_
  }⟩
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

end GeneralN
