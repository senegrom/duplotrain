import MinimalForeignCrossingClosure

/-!
# The quiet raw BABA is already a four-corner dogbone segment

A raw `B A B A` interlacement need not by itself be a periodic dogbone.
There is, however, a sharp unconditional terminal case: if all three gaps
between its four productive endpoints are raw-quiet, no fifth tongue vector
can occur.  The endpoint flips are `B,A,B,A`; the two writer names are
different, so the flips commute and cancel.  Every intermediate time is
therefore one of the four literal Gray corners.

This file proves that statement directly over `Wiring`, `stepN`, and
`RawProductiveAt`.  It does not run the sparse overwrite sequence as an echo
machine and does not infer an infinite tail from a finite segment.
-/

namespace GeneralN

/-- The four endpoint flips of a BABA with three quiet gaps restore the
represented vector exactly. -/
theorem RawBABAInterlacement.quiet_four_flip_return
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third)
    (hquietPriorSecond : ∀ k, prior < k → k < second →
      ¬ RawProductiveAt w N start k)
    (hquietSecondReroute : ∀ k, second < k → k < reroute →
      ¬ RawProductiveAt w N start k)
    (hquietRerouteThird : ∀ k, reroute < k → k < third →
      ¬ RawProductiveAt w N start k) :
    restrictedTonguesAt w N start (third + 1) =
      restrictedTonguesAt w N start prior := by
  let CB := rawWriterAt w start reroute
  let CA := rawWriterAt w start third
  have hBA : CB ≠ CA := by
    simpa [CB, CA] using B.different_writers
  have hPriorSecond := B.prior_lt_second
  have hSecondReroute := B.second_lt_reroute
  have hRerouteThird := B.reroute_lt_third
  obtain ⟨secondCfg, _secondPost, hsecondAt, _hsecondPost, _⟩ :=
    live_successor_configs B.rightFrame.open_productive.1
  obtain ⟨rerouteCfg, _reroutePost, hrerouteAt, _hreroutePost, _⟩ :=
    live_successor_configs B.leftFrame.close_productive.1
  obtain ⟨thirdCfg, _thirdPost, hthirdAt, _hthirdPost, _⟩ :=
    live_successor_configs B.rightFrame.close_productive.1
  let spanPS := second - (prior + 1)
  have hsumPS : prior + 1 + spanPS = second := by
    dsimp [spanPS]
    omega
  have hquietPS : restrictedTonguesAt w N start second =
      restrictedTonguesAt w N start (prior + 1) := by
    have h := restrictedTonguesAt_eq_of_quiet_interval
      (first := prior + 1) (span := spanPS) (finish := secondCfg)
      (by simpa [hsumPS] using hsecondAt) (by
        intro k hkLeft hkRight
        apply hquietPriorSecond k <;> omega)
    simpa [hsumPS] using h
  let spanSR := reroute - (second + 1)
  have hsumSR : second + 1 + spanSR = reroute := by
    dsimp [spanSR]
    omega
  have hquietSR : restrictedTonguesAt w N start reroute =
      restrictedTonguesAt w N start (second + 1) := by
    have h := restrictedTonguesAt_eq_of_quiet_interval
      (first := second + 1) (span := spanSR) (finish := rerouteCfg)
      (by simpa [hsumSR] using hrerouteAt) (by
        intro k hkLeft hkRight
        apply hquietSecondReroute k <;> omega)
    simpa [hsumSR] using h
  let spanRT := third - (reroute + 1)
  have hsumRT : reroute + 1 + spanRT = third := by
    dsimp [spanRT]
    omega
  have hquietRT : restrictedTonguesAt w N start third =
      restrictedTonguesAt w N start (reroute + 1) := by
    have h := restrictedTonguesAt_eq_of_quiet_interval
      (first := reroute + 1) (span := spanRT) (finish := thirdCfg)
      (by simpa [hsumRT] using hthirdAt) (by
        intro k hkLeft hkRight
        apply hquietRerouteThird k <;> omega)
    simpa [hsumRT] using h
  have hpriorFlip : restrictedTonguesAt w N start (prior + 1) =
      VectorCount.restrict N (flipAt (tonguesAt w start prior) CB) := by
    have h := rawProductiveAt_restricted_flip
      hN B.leftFrame.open_productive
    simpa [CB, B.leftFrame.same_writer] using h
  have hsecondFlip : restrictedTonguesAt w N start (second + 1) =
      VectorCount.restrict N (flipAt (tonguesAt w start second) CA) := by
    have h := rawProductiveAt_restricted_flip
      hN B.rightFrame.open_productive
    simpa [CA, B.rightFrame.same_writer] using h
  have hrerouteFlip : restrictedTonguesAt w N start (reroute + 1) =
      VectorCount.restrict N (flipAt (tonguesAt w start reroute) CB) := by
    simpa [CB] using rawProductiveAt_restricted_flip
      hN B.leftFrame.close_productive
  have hthirdFlip : restrictedTonguesAt w N start (third + 1) =
      VectorCount.restrict N (flipAt (tonguesAt w start third) CA) := by
    simpa [CA] using rawProductiveAt_restricted_flip
      hN B.rightFrame.close_productive
  have hsecondCorner : restrictedTonguesAt w N start (second + 1) =
      VectorCount.restrict N
        (flipAt (flipAt (tonguesAt w start prior) CB) CA) := by
    calc
      restrictedTonguesAt w N start (second + 1) =
          VectorCount.restrict N
            (flipAt (tonguesAt w start second) CA) := hsecondFlip
      _ = VectorCount.restrict N
            (flipAt (tonguesAt w start (prior + 1)) CA) :=
          restrict_flipAt_congr hquietPS
      _ = VectorCount.restrict N
            (flipAt (flipAt (tonguesAt w start prior) CB) CA) :=
          restrict_flipAt_congr hpriorFlip
  have hrerouteCorner : restrictedTonguesAt w N start (reroute + 1) =
      VectorCount.restrict N
        (flipAt
          (flipAt (flipAt (tonguesAt w start prior) CB) CA) CB) := by
    calc
      restrictedTonguesAt w N start (reroute + 1) =
          VectorCount.restrict N
            (flipAt (tonguesAt w start reroute) CB) := hrerouteFlip
      _ = VectorCount.restrict N
            (flipAt (tonguesAt w start (second + 1)) CB) :=
          restrict_flipAt_congr hquietSR
      _ = VectorCount.restrict N
            (flipAt
              (flipAt (flipAt (tonguesAt w start prior) CB) CA) CB) :=
          restrict_flipAt_congr hsecondCorner
  calc
    restrictedTonguesAt w N start (third + 1) =
        VectorCount.restrict N
          (flipAt (tonguesAt w start third) CA) := hthirdFlip
    _ = VectorCount.restrict N
          (flipAt (tonguesAt w start (reroute + 1)) CA) :=
        restrict_flipAt_congr hquietRT
    _ = VectorCount.restrict N
          (flipAt
            (flipAt
              (flipAt (flipAt (tonguesAt w start prior) CB) CA) CB) CA) :=
        restrict_flipAt_congr hrerouteCorner
    _ = restrictedTonguesAt w N start prior := by
      rw [flipAt_comm hBA, flipAt_flipAt, flipAt_flipAt]
      rfl

/-- Every represented vector on the complete quiet BABA segment is one of
the four literal endpoint corners. -/
theorem RawBABAInterlacement.quiet_segment_four_corners
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third)
    (hquietPriorSecond : ∀ k, prior < k → k < second →
      ¬ RawProductiveAt w N start k)
    (hquietSecondReroute : ∀ k, second < k → k < reroute →
      ¬ RawProductiveAt w N start k)
    (hquietRerouteThird : ∀ k, reroute < k → k < third →
      ¬ RawProductiveAt w N start k) :
    ∀ t, prior ≤ t → t ≤ third + 1 →
      restrictedTonguesAt w N start t ∈
        [restrictedTonguesAt w N start prior,
         restrictedTonguesAt w N start (prior + 1),
         restrictedTonguesAt w N start (second + 1),
         restrictedTonguesAt w N start (reroute + 1)] := by
  intro t hpriorT htThird
  obtain ⟨final, hfinal⟩ :=
    Option.isSome_iff_exists.mp B.rightFrame.close_productive.1
  obtain ⟨atT, ht⟩ := stepN_prefix_some
    (d := t) (K := third + 1) htThird hfinal
  by_cases hAtPrior : t = prior
  · subst t
    simp
  by_cases hThroughSecond : t ≤ second
  · let span := t - (prior + 1)
    have hsum : prior + 1 + span = t := by
      dsimp [span]
      omega
    have hquiet : restrictedTonguesAt w N start t =
        restrictedTonguesAt w N start (prior + 1) := by
      have h := restrictedTonguesAt_eq_of_quiet_interval
        (first := prior + 1) (span := span) (finish := atT)
        (by simpa [hsum] using ht) (by
          intro k hkLeft hkRight
          apply hquietPriorSecond k <;> omega)
      simpa [hsum] using h
    simp [hquiet]
  have hAfterSecond : second + 1 ≤ t := by omega
  by_cases hAtSecondPost : t = second + 1
  · subst t
    simp
  by_cases hThroughReroute : t ≤ reroute
  · let span := t - (second + 1)
    have hsum : second + 1 + span = t := by
      dsimp [span]
      omega
    have hquiet : restrictedTonguesAt w N start t =
        restrictedTonguesAt w N start (second + 1) := by
      have h := restrictedTonguesAt_eq_of_quiet_interval
        (first := second + 1) (span := span) (finish := atT)
        (by simpa [hsum] using ht) (by
          intro k hkLeft hkRight
          apply hquietSecondReroute k <;> omega)
      simpa [hsum] using h
    simp [hquiet]
  have hAfterReroute : reroute + 1 ≤ t := by omega
  by_cases hAtReroutePost : t = reroute + 1
  · subst t
    simp
  by_cases hThroughThird : t ≤ third
  · let span := t - (reroute + 1)
    have hsum : reroute + 1 + span = t := by
      dsimp [span]
      omega
    have hquiet : restrictedTonguesAt w N start t =
        restrictedTonguesAt w N start (reroute + 1) := by
      have h := restrictedTonguesAt_eq_of_quiet_interval
        (first := reroute + 1) (span := span) (finish := atT)
        (by simpa [hsum] using ht) (by
          intro k hkLeft hkRight
          apply hquietRerouteThird k <;> omega)
      simpa [hsum] using h
    simp [hquiet]
  have hAtThirdPost : t = third + 1 := by omega
  subst t
  have hreturn := B.quiet_four_flip_return hN
    hquietPriorSecond hquietSecondReroute hquietRerouteThird
  simp [hreturn]

/-- Quantitative form of the quiet BABA terminal case.  Any selected times
inside the segment have a literal novelty cover of budget four, over any
already-paid history. -/
theorem RawBABAInterlacement.quiet_segment_four_novelty_cover
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third)
    (hquietPriorSecond : ∀ k, prior < k → k < second →
      ¬ RawProductiveAt w N start k)
    (hquietSecondReroute : ∀ k, second < k → k < reroute →
      ¬ RawProductiveAt w N start k)
    (hquietRerouteThird : ∀ k, reroute < k → k < third →
      ¬ RawProductiveAt w N start k)
    (times : List Nat) (history : List (List Bool))
    (htimes : ∀ t ∈ times, prior ≤ t ∧ t ≤ third + 1) :
    FourNoveltyCover w N start times history := by
  let corners :=
    [restrictedTonguesAt w N start prior,
     restrictedTonguesAt w N start (prior + 1),
     restrictedTonguesAt w N start (second + 1),
     restrictedTonguesAt w N start (reroute + 1)]
  refine ⟨corners, (by simp [corners]), ?_⟩
  intro t ht
  apply List.mem_append_right history
  have hbounds := htimes t ht
  simpa [corners] using B.quiet_segment_four_corners hN
    hquietPriorSecond hquietSecondReroute hquietRerouteThird
    t hbounds.1 hbounds.2

end GeneralN
