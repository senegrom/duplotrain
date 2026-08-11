import TrackNovelReplay

/-!
# Switch-simple traces with one net changed coordinate have two phases

A switch-simple trace visits every switch at most once.  Therefore any local
change survives to the endpoint.  If the endpoint differs from the start at
at most one coordinate, either the trace is entirely quiet or exactly one
passage changes that coordinate.  Every intermediate tongue vector is then
one of the two endpoint vectors.
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
  induction htrace generalizing key with
  | nil c =>
      intro d hd
      have hd0 : d = 0 := by simp at hd; omega
      subst d
      exact ⟨c.1, c.2, by simp [stepN], Or.inl rfl⟩
  | @cons p x q u v rest finish harrive hlink tail ih =>
      unfold SwitchSimple at hsimple
      simp only [List.map_cons, List.nodup_cons] at hsimple
      have htailSimple : SwitchSimple rest := hsimple.2
      have htailForeign : ∀ passage ∈ rest,
          passageSwitch passage ≠ p / 3 := by
        intro passage hp hEq
        apply hsimple.1
        exact List.mem_map.mpr ⟨passage, hp, hEq⟩
      have hone : stepN w 1 (p, u) = some (q, v) := by
        simp [stepN, step, harrive, hlink]
      by_cases hvu : v = u
      · subst v
        have htailOnly : ∀ j, finish.2 j ≠ u j → j = key := by
          intro j hj
          exact honly j hj
        intro d hd
        cases d with
        | zero =>
            exact ⟨p, u, by simp [stepN], Or.inl rfl⟩
        | succ n =>
            have hn : n ≤ rest.length := by
              simp only [List.length_cons] at hd
              omega
            obtain ⟨port, phase, hrun, hphase⟩ :=
              ih htailSimple htailOnly n hn
            refine ⟨port, phase, ?_, hphase⟩
            rw [show n + 1 = 1 + n by omega, stepN_add, hone]
            exact hrun
      · have hlocal : v (p / 3) ≠ u (p / 3) := by
          intro hsame
          apply hvu
          funext j
          by_cases hj : j = p / 3
          · subst j
            exact hsame
          · exact arrive_preserves_other harrive hj
        have hfinishAt : finish.2 (p / 3) = v (p / 3) :=
          tail.preserves (p / 3) htailForeign
        have hnet : finish.2 (p / 3) ≠ u (p / 3) := by
          rw [hfinishAt]
          exact hlocal
        have hkey : p / 3 = key := honly (p / 3) hnet
        have hfinishV : finish.2 = v := by
          funext j
          by_cases hj : j = p / 3
          · subst j
            exact hfinishAt
          · have hvj : v j = u j :=
              arrive_preserves_other harrive hj
            by_cases hfu : finish.2 j = u j
            · exact hfu.trans hvj.symm
            · have hjkey : j = key := honly j hfu
              exact (hj (hjkey.trans hkey.symm)).elim
        have hgrooved : PassagesGrooved v rest := by
          have hg := tail.grooved_of_switchSimple htailSimple
          simpa [hfinishV] using hg
        intro d hd
        cases d with
        | zero =>
            exact ⟨p, u, by simp [stepN], Or.inl rfl⟩
        | succ n =>
            have hn : n ≤ rest.length := by
              simp only [List.length_cons] at hd
              omega
            obtain ⟨port, hrun⟩ :=
              tail.grooved_prefix_tongues v hgrooved hn
            refine ⟨port, v, ?_, Or.inr hfinishV.symm⟩
            rw [show n + 1 = 1 + n by omega, stepN_add, hone]
            exact hrun

end GeneralN
