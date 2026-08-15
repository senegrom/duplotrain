import TrackQuantitative

/-!
# A switch-simple physical route has length at most N

The complete-repair branch previously bounded the selected oriented route by
the reflector's total two-route travel, `2*N`.  The selected route itself is
switch-simple, and every one of its passages belongs to a switch below `N`.
Thus its length is at most `N`.  Replacing the coarse route estimate tightens
the complete-repair lasso from `22*N` to `21*N`.
-/

namespace GeneralN

/-- Every switch appearing in a physical trace is below the wiring's switch
ceiling. -/
theorem PhysicalTrace.passage_switches_lt
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N) :
    ∀ {start finish : Nat × Tongues} {passages : List Passage},
      PhysicalTrace w start passages finish →
      ∀ s ∈ passages.map passageSwitch, s < N := by
  intro start finish passages htrace
  induction htrace with
  | nil =>
      intro s hs
      cases hs
  | @cons p x q u v rest finish harrive hlink tail ih =>
      intro s hs
      simp only [List.map_cons, List.mem_cons] at hs
      rcases hs with rfl | hs
      · have hx : x < 3 * N := (hN x q hlink).1
        have hswitch := arrive_exit_switch u p
        rw [harrive] at hswitch
        dsimp [passageSwitch]
        omega
      · exact ih s hs

end GeneralN
