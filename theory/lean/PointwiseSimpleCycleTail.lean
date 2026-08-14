import TripleSelfLinkSimpleCycleClosure

/-!
# Pointwise tail of the same-exit first-revisit cycle

The stable-cycle endpoint equations alone do not control intermediate tongue
vectors.  The actual same-exit first-revisit construction is stronger: its
first passage performs the only possible change, and the rest of that lap is
already grooved in the settled state.  Consequently every positive local
time has the settled tongue vector, including all later laps.
-/

namespace GeneralN

/-- During the transient same-exit lap, every positive-depth configuration
already has the final settled tongue vector. -/
theorem PhysicalTrace.simple_same_exit_cycle_positive_prefix
    {w : Wiring} {p x q : Nat} {u₀ u v : Tongues}
    {rest : List Passage}
    (htrace : PhysicalTrace w (p, u₀) ((p, x) :: rest) (q, u))
    (hsimple : SwitchSimple ((p, x) :: rest))
    (hnext : arrive u q = (x, v)) :
    ∀ d, 0 < d → d ≤ ((q, x) :: rest).length →
      ∃ port, stepN w d (q, u) = some (port, v) := by
  obtain ⟨htransient, hstable, hsimpleCycle⟩ :=
    htrace.simple_same_exit_cycle_traces_public hsimple hnext
  have htransient' : PhysicalTrace w (q, u)
      ([(q, x)] ++ rest) (q, v) := by
    simpa using htransient
  obtain ⟨middle, hfirst, htail⟩ := htransient'.split_append
  have hone : stepN w 1 (q, u) = some middle := by
    simpa using hfirst.sound
  have honeStep : step w (q, u) = some middle := by
    simpa [stepN] using hone
  have hmiddleTongues : middle.2 = v := by
    have hparts := step_some_parts honeStep
    calc
      middle.2 = arrivedTongues (q, u) := hparts.2
      _ = v := by simp [arrivedTongues, hnext]
  have hmiddle : middle = (middle.1, v) := by
    apply Prod.ext
    · rfl
    · exact hmiddleTongues
  rw [hmiddle] at hone htail
  have hstableGrooved :
      PassagesGrooved v ((q, x) :: rest) :=
    hstable.grooved_of_switchSimple hsimpleCycle
  have htailGrooved : PassagesGrooved v rest := by
    intro passage hp
    exact hstableGrooved passage (List.mem_cons_of_mem _ hp)
  intro d hpositive hd
  cases d with
  | zero => omega
  | succ n =>
      have hn : n ≤ rest.length := by
        simpa using hd
      obtain ⟨port, hrun⟩ :=
        htail.grooved_prefix_tongues v htailGrooved hn
      refine ⟨port, ?_⟩
      rw [show n + 1 = 1 + n by omega, stepN_add, hone]
      exact hrun

/-- A stable switch-simple lap runs forever with its settled tongue vector at
every local time. -/
theorem PhysicalTrace.stable_simple_cycle_all_time
    {w : Wiring} {q : Nat} {v : Tongues}
    {cycle : List Passage}
    (hnonempty : cycle ≠ [])
    (hstable : PhysicalTrace w (q, v) cycle (q, v))
    (hsimple : SwitchSimple cycle) :
    ∀ d, ∃ port, stepN w d (q, v) = some (port, v) := by
  let period := cycle.length
  have hperiodPositive : 0 < period := by
    dsimp [period]
    cases cycle with
    | nil => exact (hnonempty rfl).elim
    | cons head tail => simp
  have hgrooved : PassagesGrooved v cycle :=
    hstable.grooved_of_switchSimple hsimple
  intro d
  let laps := d / period
  let offset := d % period
  have hoffsetLt : offset < period := by
    dsimp [offset]
    exact Nat.mod_lt d hperiodPositive
  have hdecomp : d = laps * period + offset := by
    dsimp [laps, offset]
    have hdiv := Nat.div_add_mod d period
    rw [Nat.mul_comm period (d / period)] at hdiv
    exact hdiv.symm
  have hlaps : stepN w (laps * period) (q, v) = some (q, v) :=
    stepN_mul_period_pair_novelty hstable.sound laps
  obtain ⟨port, hoffset⟩ :=
    hstable.grooved_prefix_tongues v hgrooved
      (Nat.le_of_lt hoffsetLt)
  refine ⟨port, ?_⟩
  rw [hdecomp, stepN_add, hlaps]
  exact hoffset

/-- The same-exit first-revisit orbit has exactly the settled tongue vector at
every positive local time, not merely after one complete transient lap. -/
theorem PhysicalTrace.simple_same_exit_cycle_all_positive
    {w : Wiring} {p x q : Nat} {u₀ u v : Tongues}
    {rest : List Passage}
    (htrace : PhysicalTrace w (p, u₀) ((p, x) :: rest) (q, u))
    (hsimple : SwitchSimple ((p, x) :: rest))
    (hnext : arrive u q = (x, v)) :
    ∀ d, 0 < d → ∃ port, stepN w d (q, u) = some (port, v) := by
  obtain ⟨htransient, hstable, hsimpleCycle⟩ :=
    htrace.simple_same_exit_cycle_traces_public hsimple hnext
  let cycle : List Passage := (q, x) :: rest
  have hnonempty : cycle ≠ [] := by simp [cycle]
  intro d hpositive
  by_cases hfirstLap : d ≤ cycle.length
  · exact htrace.simple_same_exit_cycle_positive_prefix
      hsimple hnext d hpositive (by simpa [cycle] using hfirstLap)
  · let tailTime := d - cycle.length
    have hsum : d = cycle.length + tailTime := by
      dsimp [tailTime]
      omega
    obtain ⟨port, htail⟩ :=
      hstable.stable_simple_cycle_all_time hnonempty hsimpleCycle tailTime
    have hfirstLapRun : stepN w cycle.length (q, u) = some (q, v) := by
      simpa [cycle] using htransient.sound
    refine ⟨port, ?_⟩
    rw [hsum, stepN_add, hfirstLapRun]
    exact htail

end GeneralN
