import StateLawTwoSharp

/-!
# One fresh vector when three Gray corners are historical

The four-corner runway/lobe orbit has only one globally fresh corner once the
entering alternate, the base state and the old-action state have all occurred
in the protected lead.
-/

namespace GeneralN

/-- Shift an all-time four-phase law when its first, third and fourth phases
are already historical. -/
theorem absolute_one_novelty_of_historical_first_third_fourth_four_phase
    {w : Wiring} {N K localPort : Nat}
    {start : Nat × Tongues} {u v₁ v₂ v₃ : Tongues}
    {times : List Nat} {history : List (List Bool)}
    (hreach : stepN w K start = some (localPort, u))
    (hlive : ∀ d, ∃ finish, stepN w d (localPort, u) = some finish)
    (hphase : ∀ d, tonguesAt w (localPort, u) d ∈ [u, v₁, v₂, v₃])
    (hu : VectorCount.restrict N u ∈ history)
    (hv₂ : VectorCount.restrict N v₂ ∈ history)
    (hv₃ : VectorCount.restrict N v₃ ∈ history)
    (hlead : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    NoveltyCoverOn w N start times history 1 := by
  refine ⟨[VectorCount.restrict N v₁], by simp, ?_⟩
  intro j hj
  by_cases hjK : j < K
  · exact List.mem_append_left _ (hlead j hj hjK)
  · let d := j - K
    have hjEq : j = K + d := by
      dsimp [d]
      omega
    have hshift := tonguesAt_add_of_reaches hreach (hlive d)
    rw [← hjEq] at hshift
    have hlocal := hphase d
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlocal
    rcases hlocal with hu' | hv₁' | hv₂' | hv₃'
    · apply List.mem_append_left
      simpa [restrictedTonguesAt, hshift, hu'] using hu
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, hshift, hv₁']
    · apply List.mem_append_left
      simpa [restrictedTonguesAt, hshift, hv₂'] using hv₂
    · apply List.mem_append_left
      simpa [restrictedTonguesAt, hshift, hv₃'] using hv₃

/-- Intersecting runway actions have one fresh Gray corner when the entering,
base and old-action corners are historical. -/
theorem manufactured_flip_arbitrary_lobe_absolute_one_novelty
    {w : Wiring} {outside mouth entry returnPort N : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    (hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
      C.toSupported.paths)
    {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start =
      some (outside, flipAt state (mouth / 3)))
    (times : List Nat) (history : List (List Bool))
    (hentryHistorical : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history)
    (hstateHistorical : VectorCount.restrict N state ∈ history)
    (holdHistorical : VectorCount.restrict N
      (flipAt state C.actionSwitch) ∈ history)
    (hlead : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    NoveltyCoverOn w N start times history 1 := by
  have hcover := manufactured_flip_arbitrary_lobe_all_time_four_phase C state hCpaths
    hNewAvoidsC hentryBranch hentrySwitch hgrooved htrace hcrossed
    hCandyForeign hLobe hmouthLink hcontact
  apply absolute_one_novelty_of_historical_first_third_fourth_four_phase
    (u := flipAt state (mouth / 3))
    (v₁ := flipAt (flipAt state (mouth / 3)) C.actionSwitch)
    (v₂ := state)
    (v₃ := flipAt state C.actionSwitch)
    hreach
  · intro d
    obtain ⟨port, phase, hr, _⟩ := hcover d
    exact ⟨(port, phase), hr⟩
  · intro d
    obtain ⟨port, phase, hr, hs⟩ := hcover d
    simpa [tonguesAt, hr] using hs
  · exact hentryHistorical
  · exact hstateHistorical
  · exact holdHistorical
  · exact hlead

/-- Disjoint runway actions likewise have only the double-flipped corner
fresh when alternate, old-action and base are historical. -/
theorem manufactured_suffix_explicit_lobe_absolute_one_novelty
    {w : Wiring} {outside mouth entry returnPort N : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    (hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
      C.toSupported.paths)
    (hActionsNe : mouth / 3 ≠ C.actionSwitch)
    {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeignNew : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hCandyForeignOld : ∀ passage ∈ candy,
      passageSwitch passage ≠ C.actionSwitch)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start =
      some (outside, flipAt state (mouth / 3)))
    (times : List Nat) (history : List (List Bool))
    (hentryHistorical : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history)
    (hstateHistorical : VectorCount.restrict N state ∈ history)
    (holdHistorical : VectorCount.restrict N
      (flipAt state C.actionSwitch) ∈ history)
    (hlead : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    NoveltyCoverOn w N start times history 1 := by
  have hcover := manufactured_suffix_explicit_lobe_all_time_four_phase
    C state hCpaths hNewAvoidsC hActionsNe hentryBranch hentrySwitch
    hgrooved htrace hcrossed hCandyForeignNew hCandyForeignOld hLobe hmouthLink
  apply absolute_one_novelty_of_historical_first_third_fourth_four_phase
    (u := flipAt state (mouth / 3))
    (v₁ := flipAt (flipAt state (mouth / 3)) C.actionSwitch)
    (v₂ := flipAt state C.actionSwitch)
    (v₃ := state)
    hreach
  · intro d
    obtain ⟨port, phase, hr, _⟩ := hcover d
    exact ⟨(port, phase), hr⟩
  · intro d
    obtain ⟨port, phase, hr, hs⟩ := hcover d
    simpa [tonguesAt, hr] using hs
  · exact hentryHistorical
  · exact holdHistorical
  · exact hstateHistorical
  · exact hlead

end GeneralN
