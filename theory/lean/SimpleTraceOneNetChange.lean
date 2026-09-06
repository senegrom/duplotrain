import TrackNovelReplay

/-!
# Switch-simple traces with one net changed coordinate have two phases

A switch-simple trace visits every switch at most once. Each prefix coordinate
therefore equals its initial or final value. If the endpoints agree away from
one coordinate, so does every prefix; its value at that coordinate selects
one of the two complete endpoint vectors. No passage-count induction is needed.
-/

namespace GeneralN

/-- **Two-phase simple-trace theorem.**  If every net changed coordinate of a
switch-simple physical trace is `key`, every prefix has the initial or final
tongue vector. -/
theorem PhysicalTrace.two_phase_of_net_changes_only
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage} {key : Nat}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (honly : ∀ j, finish.2 j ≠ start.2 j → j = key) :
    ∀ d, d ≤ passages.length →
      ∃ port phase,
        stepN w d start = some (port, phase) ∧
        (phase = start.2 ∨ phase = finish.2) := by
  intro d hd
  obtain ⟨⟨port, phase⟩, hrun⟩ := stepN_prefix_some hd htrace.sound
  have hcoordinate := htrace.prefix_coordinate_eq_endpoint hsimple hd hrun
  have hagree : ∀ j, j ≠ key → finish.2 j = start.2 j := by
    intro j hj
    exact Classical.byContradiction (fun h => hj (honly j h))
  refine ⟨port, phase, hrun, ?_⟩
  rcases hcoordinate key with hkey | hkey
  · left
    funext j
    by_cases hj : j = key
    · simpa [hj] using hkey
    · rcases hcoordinate j with h | h
      · exact h
      · exact h.trans (hagree j hj)
  · right
    funext j
    by_cases hj : j = key
    · simpa [hj] using hkey
    · rcases hcoordinate j with h | h
      · exact h.trans (hagree j hj).symm
      · exact h

end GeneralN
