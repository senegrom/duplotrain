import ProtectedPairNAddFour
import StateLawBounds

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
    have hvlive : ∀ k ∈ times, (stepN v k start).isSome := by
      intro k hk
      rw [hreach k hk]
      exact hlive k hk
    have hvectors : times.map (restrictedTonguesAt v N start) =
        times.map (restrictedTonguesAt w N start) := by
      apply List.map_congr_left
      intro k hk
      simp only [restrictedTonguesAt, tonguesAt, hreach k hk]
    rcases known_edge_N_add_four_or_changed_contact_or_protected_pair
        hvN hvtotal (v.symm _ _ he) times hvlive (hvectors.symm ▸ hnd) with
        hsmall | hchanged | hpair
    · exact hsmall
    · obtain ⟨D⟩ := hchanged
      have hliveA : ∀ k ∈ times,
          (stepN v k (start.1, D.A.baseState)).isSome := by
        simpa [D.base] using hvlive
      have hndA : (times.map
          (restrictedTonguesAt v N (start.1, D.A.baseState))).Nodup := by
        simpa [D.base] using (hvectors.symm ▸ hnd)
      exact D.contact.all_run_distinct_le_N_add_four
        hvN D.grooves times hliveA hndA
    · exact knownEdgeProtectedPairNAddFourLaw hvN (Classical.choice hpair)
        times hvlive (hvectors.symm ▸ hnd)
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
