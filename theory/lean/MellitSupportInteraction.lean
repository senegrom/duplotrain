import MellitSharpTail
import RunwayHistoricalThree

/-!
# Early support interactions in the Mellit sharp-tail route

`MellitSharpTail` reduces a second physical repeat to an oppositely oriented
manufactured pair.  This file handles the non-compatible branch when the
protected repair exposes a changed-forward contact early enough.

The timing threshold is `z1+1`, not `z0+1`.  The no-gap six-event reduction
shows that every earlier vector is in first-writer history or is event zero;
the endpoint `z1+1` contributes at most one further vector.  The established
three-vector changed-forward tail therefore yields the literal forbidden
four-cover.
-/

namespace GeneralN

/-- Eventual periodicity supplies successful raw prefixes of every length. -/
theorem EventuallyPeriodic.stepN_some_all
    {w : Wiring} {start : Nat × Tongues}
    (H : EventuallyPeriodic w start) (d : Nat) :
    ∃ finish, stepN w d start = some finish := by
  obtain ⟨lead, period, settled, hpositive, hsettled, hperiod⟩ := H
  have hcycles :
      stepN w ((d + 1) * period) settled = some settled :=
    stepN_mul_period_pair_novelty hperiod (d + 1)
  have hfar :
      stepN w (lead + (d + 1) * period) start = some settled := by
    rw [stepN_add, hsettled]
    exact hcycles
  have hone : 1 ≤ period := by omega
  have hmul := Nat.mul_le_mul_left (d + 1) hone
  simp only [Nat.mul_one] at hmul
  have hbound : d ≤ lead + (d + 1) * period := by omega
  exact stepN_prefix_some hbound hfar

/-- A changed-forward support interaction reached early in the second-repeat
construction covers the five selected closes with four vectors.  Event one's
post-vector pays for the possible endpoint of the construction lead; the
closed runway/candy theorem contributes at most three further vectors. -/
theorem RawOverlappingFiveWindowReduction.early_changedForward_tail_four_cover_z1
    {w : Wiring} {N g e shift : Nat}
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R))
    (hreach : stepN w shift start =
      some (g, (ManufacturedReflector.flip R).activatedState))
    (hlead : shift + A.toSupported.travel ≤ C.z1 + 1) :
    NoveltyCoverOn w N start
      [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1]
      (rawFirstWriterHistory w N start (C.z5 + 1) ++
        [restrictedTonguesAt w N start (C.z0 + 1)]) 4 := by
  classical
  let localStart : Nat × Tongues :=
    (g, (ManufacturedReflector.flip R).activatedState)
  let history0 := rawFirstWriterHistory w N start (C.z5 + 1) ++
    [restrictedTonguesAt w N start (C.z0 + 1)]
  let paid1 := restrictedTonguesAt w N start (C.z1 + 1)
  let history1 := history0 ++ [paid1]
  let localTimes :=
    [C.z1 + 1 - shift, C.z2 + 1 - shift,
      C.z3 + 1 - shift, C.z4 + 1 - shift,
      C.z5 + 1 - shift]
  change NoveltyCoverOn w N start
    [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1]
    history0 4
  have o12 : C.z1 < C.z2 := C.order12
  have o23 : C.z2 < C.z3 := C.order23
  have o34 : C.z3 < C.z4 := C.order34
  have o45 : C.z4 < C.z5 := C.order45
  have hshift : shift ≤ C.z1 + 1 :=
    Nat.le_trans (Nat.le_add_right shift A.toSupported.travel) hlead
  have hperiodic : EventuallyPeriodic w localStart := by
    simpa [localStart] using hmerge.eventuallyPeriodic
  have hlive : ∀ d, ∃ finish, stepN w d localStart = some finish :=
    hperiodic.stepN_some_all
  have hleadHistorical : ∀ j, j ≤ A.toSupported.travel →
      restrictedTonguesAt w N localStart j ∈ history1 := by
    intro j hj
    obtain ⟨finish, hfinish⟩ := hlive j
    have hshiftVector := restrictedTonguesAt_add_of_reach
      (N := N) (d := j) hreach hfinish
    rw [← hshiftVector]
    apply C.prefix_through_z1_paid
    omega
  have hlocalCover :
      NoveltyCoverOn w N localStart localTimes history1 3 :=
    hmerge.runway_or_candy_absolute_three_novelty
      N history1 hleadHistorical localTimes
  have htransport : ∀ t, shift ≤ t →
      restrictedTonguesAt w N localStart (t - shift) =
        restrictedTonguesAt w N start t := by
    intro t ht
    obtain ⟨finish, hfinish⟩ := hlive (t - shift)
    have hshiftVector := restrictedTonguesAt_add_of_reach
      (N := N) (d := t - shift) hreach hfinish
    rw [← hshiftVector]
    congr 1
    omega
  obtain ⟨fresh, hfreshLength, hlocalMem⟩ := hlocalCover
  have hm1 : restrictedTonguesAt w N start (C.z1 + 1) ∈
      history1 ++ fresh := by
    have hm := hlocalMem (C.z1 + 1 - shift) (by simp [localTimes])
    rw [htransport (C.z1 + 1) hshift] at hm
    exact hm
  have hm2 : restrictedTonguesAt w N start (C.z2 + 1) ∈
      history1 ++ fresh := by
    have hm := hlocalMem (C.z2 + 1 - shift) (by simp [localTimes])
    rw [htransport (C.z2 + 1) (by omega)] at hm
    exact hm
  have hm3 : restrictedTonguesAt w N start (C.z3 + 1) ∈
      history1 ++ fresh := by
    have hm := hlocalMem (C.z3 + 1 - shift) (by simp [localTimes])
    rw [htransport (C.z3 + 1) (by omega)] at hm
    exact hm
  have hm4 : restrictedTonguesAt w N start (C.z4 + 1) ∈
      history1 ++ fresh := by
    have hm := hlocalMem (C.z4 + 1 - shift) (by simp [localTimes])
    rw [htransport (C.z4 + 1) (by omega)] at hm
    exact hm
  have hm5 : restrictedTonguesAt w N start (C.z5 + 1) ∈
      history1 ++ fresh := by
    have hm := hlocalMem (C.z5 + 1 - shift) (by simp [localTimes])
    rw [htransport (C.z5 + 1) (by omega)] at hm
    exact hm
  let fresh4 := paid1 :: fresh
  refine ⟨fresh4, ?_, ?_⟩
  · dsimp [fresh4]
    omega
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · simpa [history1, fresh4, List.append_assoc] using hm1
    · simpa [history1, fresh4, List.append_assoc] using hm2
    · simpa [history1, fresh4, List.append_assoc] using hm3
    · simpa [history1, fresh4, List.append_assoc] using hm4
    · simpa [history1, fresh4, List.append_assoc] using hm5

/-- Consequently the early changed-forward support-interaction branch is
incompatible with the canonical raw six-event obstruction. -/
theorem RawOverlappingFiveWindowReduction.early_changedForward_second_repeat_false
    {w : Wiring} {N g e shift : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R))
    (hreach : stepN w shift start =
      some (g, (ManufacturedReflector.flip R).activatedState))
    (hlead : shift + A.toSupported.travel ≤ C.z1 + 1) : False := by
  let S := C.toSixEventReduction
  exact S.no_tail_four_cover hN
    (C.early_changedForward_tail_four_cover_z1 hmerge hreach hlead)

end GeneralN
