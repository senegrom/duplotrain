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
    change (match w.link a with
      | some q => some q
      | none => if a < 3 * N then some a else none) = some b at hab
    change (match w.link b with
      | some q => some q
      | none => if b < 3 * N then some b else none) = some a
    cases ha : w.link a with
    | some q =>
        have hq : q = b := by simpa [ha] using hab
        subst q
        simp [w.symm a b ha]
    | none =>
        by_cases hbound : a < 3 * N
        · have heq : a = b := by simpa [ha, hbound] using hab
          subst b
          simp [ha, hbound]
        · simp [ha, hbound] at hab

/-- No existing connection is changed. -/
theorem Wiring.completed_preserves {w : Wiring} {a b N : Nat}
    (hab : w.link a = some b) : (w.completed N).link a = some b := by
  simp [Wiring.completed, hab]

/-- Completion never adds a switch. -/
theorem Wiring.completed_bounded {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b → a < 3 * N ∧ b < 3 * N) :
    ∀ a b, (w.completed N).link a = some b → a < 3 * N ∧ b < 3 * N := by
  intro a b hab
  cases ha : w.link a with
  | some q =>
      have hq : q = b := by simpa [Wiring.completed, ha] using hab
      subst q
      exact hN a b ha
  | none =>
      by_cases hbound : a < 3 * N
      · have heq : a = b := by simpa [Wiring.completed, ha, hbound] using hab
        exact ⟨hbound, heq ▸ hbound⟩
      · simp [Wiring.completed, ha, hbound] at hab

/-- Every in-range port has a partner in the completion. -/
theorem Wiring.completed_total (w : Wiring) {N p : Nat} (hp : p < 3 * N) :
    ∃ q, (w.completed N).link p = some q := by
  cases ha : w.link p with
  | some q => exact ⟨q, w.completed_preserves ha⟩
  | none => exact ⟨p, by simp [Wiring.completed, ha, hp]⟩

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
