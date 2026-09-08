import ProtectedPairNAddFour
import StateLawBounds
import WiringCompletion

/-!
# Sharp `N+4` state law by completing all free ports

The abstract wiring model permits self-links. Complete every free port on
an existing switch, leaving all original links and the initial tongue
assignment unchanged. Every original live sample is then a sample of a
non-terminating run on the completion, at exactly the same time.

The known-incoming-edge argument therefore needs only total wirings. Both
of its finite probes are live automatically; the former dead-probe branch
and the general periodicity detour used to discharge it are unnecessary.
The remaining cycle, changed-contact and protected-pair bounds are unchanged.

No switch is added, and the headline theorem remains unconditional over
partial wirings. A start outside the first N switches dies after one step
and contributes at most the time-zero vector.
-/

namespace GeneralN

/-- On total wirings both first-revisit probes are live. Close each cycle or
reflector outcome directly with its counting theorem. -/
theorem known_edge_N_add_four
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (htotal : ∀ p, p < 3 * N → ∃ q, w.link p = some q)
    {start : Nat × Tongues} (hentry : w.link e = some start.1)
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 4 := by
  obtain ⟨firstFinish, hfirst⟩ :=
    stepN_live_of_total hN htotal (N + 1) start (hN _ _ hentry).2
  rcases first_revisit_fork hN hfirst hentry with hcycleA | ⟨A, hA, hbaseA⟩
  · obtain ⟨lead, atRepeat, settled, htrace, hsimple, hsettled⟩ := hcycleA
    have hshort := prefix_then_settled_distinct_le htrace.sound
      (htrace.simple_length_le hN hsimple) hsettled times hnd
    omega
  · have hndA : (times.map
        (restrictedTonguesAt w N (start.1, A.baseState))).Nodup := by
      simpa [hbaseA] using hnd
    have hliveA : ∀ k ∈ times, (stepN w k (start.1, A.baseState)).isSome := by
      intro k _
      exact Option.isSome_iff_exists.mpr
        (stepN_live_of_total hN htotal k _ (hN _ _ hentry).2)
    have hchanged {finish : Nat × Tongues} {lead : List Passage}
        (htrace : PhysicalTrace w (e, A.activatedState) lead finish)
        (hsimple : SwitchSimple lead)
        (hbroken : ¬ PathGrooves A.toSupported.paths finish.2) : times.length ≤ N + 4 := by
      obtain ⟨C⟩ := PartialSecondRunSharp.ManufacturedReflector.changedContact_of_broken_simple
        A hA htrace hsimple hbroken
      exact C.all_run_distinct_le_N_add_four hN hA times hliveA hndA
    obtain ⟨secondFinish, hsecond⟩ := stepN_live_of_total hN htotal
      (N + 1) (e, A.activatedState) (hN _ _ hentry).1
    rcases first_revisit_fork hN hsecond (w.symm _ _ hentry) with hcycleB | ⟨B, hB, hbaseB⟩
    · obtain ⟨lead, atRepeat, settled, htrace, hsimple, hsettled⟩ := hcycleB
      by_cases hend : PathGrooves A.toSupported.paths atRepeat.2
      · have hsmall := simple_lead_one_vector_tail_distinct_le_N_add_three
          hN A hA htrace hsimple hend hsettled times hndA
        omega
      · exact hchanged htrace hsimple hend
    · by_cases hpre : PathGrooves A.toSupported.paths B.preReturn.2
      · exact A.preReturn_grooved_protected_pair_all_run_distinct_le_N_add_four
          hN B hbaseB hA hB hpre times hliveA hndA
      · exact hchanged (by simpa [hbaseB] using B.exploration_trace) B.exploration_simple hpre

/-- **Sharp state law.** Transfer original live samples to a total
completion without changing the start, sample times, or switch budget. -/
theorem state_law_N_add_four : StateLawNAddFour := by
  intro w N hN start times hlive hnd
  change (times.map (restrictedTonguesAt w N start)).Nodup at hnd
  by_cases hstart : start.1 < 3 * N
  · let v := w.completed N
    have hvN := w.completed_bounded hN
    have hvtotal : ∀ p, p < 3 * N → ∃ q, v.link p = some q :=
      fun _ hp => w.completed_total hp
    obtain ⟨e, he⟩ := hvtotal start.1 hstart
    have hreach : ∀ k ∈ times, stepN v k start = stepN w k start := by
      intro k hk
      cases hr : stepN w k start with
      | none => have := hlive k hk; simp [hr] at this
      | some finish =>
          exact stepN_preserved_by_wiring_extension
            (fun _ _ hab => Wiring.completed_preserves hab) k start finish hr
    have hvectors : times.map (restrictedTonguesAt v N start) =
        times.map (restrictedTonguesAt w N start) := by
      apply List.map_congr_left
      intro k hk
      simp only [restrictedTonguesAt, tonguesAt, hreach k hk]
    exact known_edge_N_add_four hvN hvtotal (v.symm _ _ he) times (hvectors.symm ▸ hnd)
  · have hdead : stepN w 1 start = none := by
      have hedge : w.link (arrive start.2 start.1).1 = none := by
        cases hw : w.link (arrive start.2 start.1).1 with
        | none => rfl
        | some q =>
            have hbound := (hN _ _ hw).1
            have hsame := arrive_exit_switch start.2 start.1
            omega
      simp [stepN, step, hedge]
    have hlen := dead_horizon_live_distinct_le (N := N)
      hdead times hlive hnd
    omega

end GeneralN
