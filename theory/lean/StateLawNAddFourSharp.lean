import ProtectedPairNAddFour
import StateLawBounds

/-!
# Sharp `N+4` state law by completing the starting port

The known-incoming-edge theorem is uniform over raw finite wirings, which
allow self-links. If the starting port is unwired, cap just that port with
a self-link. Every live step of the original run uses an existing edge, so
it survives unchanged in the extended wiring. The original sample times,
including time zero, therefore satisfy the known-edge theorem directly.

This avoids shifting the run and eliminates the productive-boundary
saturation argument. No switch or initial tongue vector is added. A start
outside the first N switches has no live successor and contributes at most
one vector. The exact theorem statement and the attainment proof are unchanged.
-/

namespace GeneralN

/-- A train whose incoming track edge is known visits at most `N + 4`
pairwise-distinct restricted tongue vectors. -/
theorem knownIncomingEdgeNAddFour
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    KnownIncomingEdgeNAddFour w N := by
  intro e start hentry times hlive hnd
  exact known_edge_all_run_distinct_le_N_add_four_of_protected_pair
    knownEdgeProtectedPairNAddFourLaw hN hentry times hlive hnd

/-- Add a reversing cap only at a port with no existing partner. -/
def Wiring.capFreePort (w : Wiring) (p : Nat)
    (hfree : w.link p = none) : Wiring where
  link a := if a = p then some p else w.link a
  symm := by
    intro a b hab
    change (if a = p then some p else w.link a) = some b at hab
    change (if b = p then some p else w.link b) = some a
    by_cases ha : a = p
    · subst a
      simp at hab
      subst b
      simp
    · rw [if_neg ha] at hab
      have hb : b ≠ p := by
        intro heq
        subst b
        have hback := w.symm a p hab
        simp [hfree] at hback
      simp [hb, w.symm a b hab]

/-- Capping a free port preserves every existing physical edge. -/
theorem Wiring.capFreePort_preserves {w : Wiring} {p : Nat}
    (hfree : w.link p = none) {a b : Nat}
    (hab : w.link a = some b) :
    (w.capFreePort p hfree).link a = some b := by
  have ha : a ≠ p := by
    intro heq
    subst a
    simp [hfree] at hab
  simpa [Wiring.capFreePort, ha] using hab

/-- Extending a wiring cannot change any still-live configuration of a run.
This deliberately makes no assertion about the continuation after death. -/
theorem stepN_preserved_by_wiring_extension {w v : Wiring}
    (hext : ∀ a b, w.link a = some b → v.link a = some b)
    (n : Nat) (start finish : Nat × Tongues)
    (hrun : stepN w n start = some finish) :
    stepN v n start = some finish := by
  induction n generalizing start with
  | zero => simpa only [stepN] using hrun
  | succ n ih =>
      cases hedge : w.link (arrive start.2 start.1).1 with
      | none => simp [stepN, step, hedge] at hrun
      | some q =>
          have hv := hext _ _ hedge
          have htail : stepN w n (q, (arrive start.2 start.1).2) =
              some finish := by
            simpa [stepN, step, hedge] using hrun
          simpa [stepN, step, hv] using ih _ htail

/-- **Sharp state law.** Complete an unwired starting port rather than
shifting the run and paying separately for its time-zero vector. -/
theorem state_law_N_add_four : StateLawNAddFour := by
  intro w N hN start times hlive hnd
  change (times.map (restrictedTonguesAt w N start)).Nodup at hnd
  by_cases hstart : start.1 < 3 * N
  · cases hentry : w.link start.1 with
    | some e =>
        exact knownIncomingEdgeNAddFour hN (w.symm _ _ hentry)
          times hlive hnd
    | none =>
        let v := w.capFreePort start.1 hentry
        have hvN : ∀ a b, v.link a = some b →
            a < 3 * N ∧ b < 3 * N := by
          intro a b hab
          by_cases ha : a = start.1
          · have hb : start.1 = b := by
              simpa [v, Wiring.capFreePort, ha] using hab
            exact ⟨by simpa [ha] using hstart, hb ▸ hstart⟩
          · apply hN a b
            simpa [v, Wiring.capFreePort, ha] using hab
        have hreach : ∀ k ∈ times, stepN v k start = stepN w k start := by
          intro k hk
          cases hr : stepN w k start with
          | none => have := hlive k hk; simp [hr] at this
          | some finish =>
              exact stepN_preserved_by_wiring_extension
                (fun _ _ hab => Wiring.capFreePort_preserves hentry hab)
                k start finish hr
        have hvlive : ∀ k ∈ times, (stepN v k start).isSome := by
          intro k hk
          rw [hreach k hk]
          exact hlive k hk
        have hvectors : times.map (restrictedTonguesAt v N start) =
            times.map (restrictedTonguesAt w N start) := by
          apply List.map_congr_left
          intro k hk
          simp only [restrictedTonguesAt, tonguesAt, hreach k hk]
        exact knownIncomingEdgeNAddFour hvN
          (show v.link start.1 = some start.1 by simp [v, Wiring.capFreePort])
          times hvlive (by simpa only [hvectors] using hnd)
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
