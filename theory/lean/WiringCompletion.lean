import TrackTrace

/-!
# Complete a partial wiring without adding switches

Cap every free port below `3*N` by a self-link. The extended wiring is total
on those ports and preserves every live configuration of the original run.
Consequently an upper bound need only analyse non-terminating runs: all
finite original samples transfer to the completion, with time zero intact.
-/

namespace GeneralN

/-- Keep existing links and cap every free port on the first `N` switches. -/
def Wiring.completed (w : Wiring) (N : Nat) : Wiring where
  link p := match w.link p with
    | some q => some q
    | none => if p < 3 * N then some p else none
  symm := by
    intro a b hab
    cases ha : w.link a <;> cases hb : w.link b <;> grind [w.symm]

/-- No existing connection is changed. -/
theorem Wiring.completed_preserves {w : Wiring} {a b N : Nat}
    (hab : w.link a = some b) : (w.completed N).link a = some b := by grind [Wiring.completed]

/-- Every finite prefix in a bounded total wiring is live. -/
theorem stepN_live_of_total {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b → a < 3 * N ∧ b < 3 * N)
    (htotal : ∀ p, p < 3 * N → ∃ q, w.link p = some q)
    (n : Nat) (start : Nat × Tongues) (hstart : start.1 < 3 * N) :
    ∃ finish, stepN w n start = some finish := by
  induction n generalizing start with
  | zero => exact ⟨start, rfl⟩
  | succ n ih =>
      have hexit : (arrive start.2 start.1).1 < 3 * N := by
        have hsame := arrive_exit_switch start.2 start.1
        omega
      obtain ⟨q, hq⟩ := htotal _ hexit
      obtain ⟨finish, hf⟩ := ih (q, (arrive start.2 start.1).2) (hN _ _ hq).2
      exact ⟨finish, by simpa [stepN, step, hq] using hf⟩

/-- Extending a wiring preserves every live configuration, but need not
preserve termination: the extended run may continue after the original dies. -/
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

end GeneralN
