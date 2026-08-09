import TwoSwitchOneShotObstruction

/-!
# Recursive serial repair cannot create a fresh handoff

`two_switch_first_repeat_cycle_or_input_return` names the edge used by the
returning branch of an isolated two-switch fork: it is the plain-track edge
attached to the fork's original input port.  This file proves that this
property survives arbitrary finite serial composition.

A `RawExactInputReturnFrame` is one repaired local fork.  It reaches its
first-repeat configuration in at most two steps and returns through its
original input edge in at most three more steps.  A
`RawRecursiveRepairChain` stacks any finite number of such frames.  The main
theorem proves directly from `stepN_add` that the whole stack unwinds to its
root, in at most five steps per frame.  Consequently serial repair cannot
turn local `C,D,C` returns into a new forward output.  If the root is instead
on a non-falling trajectory, that trajectory is inherited by the whole
prefix.

The theorem is uniform in the wiring and in the chain depth.  It uses no
bounded enumeration, recurrence assumption, or sharp state-law hypothesis.
-/

namespace GeneralN

/-- One raw local repair which returns over exactly the edge attached to its
entry port.  The two numerical bounds are precisely those exposed by
`two_switch_first_repeat_cycle_or_input_return`. -/
structure RawExactInputReturnFrame
    (w : Wiring) (entry returned : Nat × Tongues) where
  atRepeat : Nat × Tongues
  lead : Nat
  back : Nat
  lead_le_two : lead <= 2
  back_le_three : back <= 3
  reaches_repeat : stepN w lead entry = some atRepeat
  input_link : w.link entry.1 = some returned.1
  returns_through_input :
    stepN w back atRepeat =
      (w.link entry.1).map (fun ell => (ell, returned.2))

/-- A certified local repair really runs from its entry configuration to its
returned configuration. -/
theorem RawExactInputReturnFrame.run
    {w : Wiring} {entry returned : Nat × Tongues}
    (F : RawExactInputReturnFrame w entry returned) :
    stepN w (F.lead + F.back) entry = some returned := by
  rw [stepN_add, F.reaches_repeat]
  simpa [F.input_link] using F.returns_through_input

/-- One repaired two-switch frame costs at most five transitions. -/
theorem RawExactInputReturnFrame.steps_le_five
    {w : Wiring} {entry returned : Nat × Tongues}
    (F : RawExactInputReturnFrame w entry returned) :
    F.lead + F.back <= 5 := by
  have hlead := F.lead_le_two
  have hback := F.back_le_three
  omega

/-- A finite stack of exact input-return repairs.

The final two indices record the number of frames and the exact number of
transitions.  In `cons`, the first frame returns to `returned`; the tail then
continues from that very configuration.  Thus the definition itself does not
allow an unverified forward handoff between serial modules. -/
inductive RawRecursiveRepairChain (w : Wiring) :
    (Nat × Tongues) -> (Nat × Tongues) -> Nat -> Nat -> Prop
  | nil (c : Nat × Tongues) :
      RawRecursiveRepairChain w c c 0 0
  | cons {entry returned root : Nat × Tongues}
      {depth tailSteps : Nat}
      (frame : RawExactInputReturnFrame w entry returned)
      (tail : RawRecursiveRepairChain w returned root depth tailSteps) :
      RawRecursiveRepairChain w entry root (depth + 1)
        (frame.lead + frame.back + tailSteps)

/-- **Recursive serial-return theorem.**

Every finite recursively repaired chain runs back to its root configuration.
This is an equality about the raw `Wiring`/`stepN` dynamics, not a graph-level
analogy. -/
theorem RawRecursiveRepairChain.run
    {w : Wiring} {entry root : Nat × Tongues}
    {depth total : Nat}
    (H : RawRecursiveRepairChain w entry root depth total) :
    stepN w total entry = some root := by
  induction H with
  | nil c => rfl
  | @cons entry returned root depth tailSteps frame tail ih =>
      rw [show frame.lead + frame.back + tailSteps =
          (frame.lead + frame.back) + tailSteps by omega,
        stepN_add, frame.run]
      exact ih

/-- The recursive unwind costs at most five transitions per repaired frame. -/
theorem RawRecursiveRepairChain.steps_le_five_mul_depth
    {w : Wiring} {entry root : Nat × Tongues}
    {depth total : Nat}
    (H : RawRecursiveRepairChain w entry root depth total) :
    total <= 5 * depth := by
  induction H with
  | nil c => omega
  | @cons entry returned root depth tailSteps frame tail ih =>
      have hlocal := frame.steps_le_five
      omega

/-- Package the two unconditional conclusions of recursive serial repair. -/
theorem recursively_repaired_serial_chain
    {w : Wiring} {entry root : Nat × Tongues}
    {depth total : Nat}
    (H : RawRecursiveRepairChain w entry root depth total) :
    And (total <= 5 * depth)
      (stepN w total entry = some root) :=
  And.intro H.steps_le_five_mul_depth H.run

/-- At the end of the certified chain there is only one possible
configuration.  In particular, a purported fresh forward handoff at the same
time is impossible. -/
theorem RawRecursiveRepairChain.no_fresh_handoff
    {w : Wiring} {entry root other : Nat × Tongues}
    {depth total : Nat}
    (H : RawRecursiveRepairChain w entry root depth total)
    (hother : stepN w total entry = some other) :
    other = root := by
  exact Option.some.inj (hother.symm.trans H.run)

/-- If the configuration reached after the repaired prefix never falls, then
the original entry never falls after that prefix either.  This is the other
branch of the local two-switch obstruction propagated through an arbitrary
serial stack. -/
theorem RawRecursiveRepairChain.never_falls_after
    {w : Wiring} {entry root : Nat × Tongues}
    {depth total : Nat}
    (H : RawRecursiveRepairChain w entry root depth total)
    (hroot : forall n, (stepN w n root).isSome) :
    forall n, (stepN w (total + n) entry).isSome := by
  intro n
  simpa [stepN_add, H.run] using hroot n

/-- A complete recursively repaired serial computation.

`some root` records that every encountered fork took its exact input-return
branch and the whole stack unwound to `root`.  `none` records that some fork
instead entered its non-falling branch.  Here `none` is only an outcome tag;
it does *not* mean that `stepN` fell off the track.

The `trap` and `cons` constructors make the recursion explicit: a trap may
occur at any depth, while every enclosing `cons` is a certified exact return
through that module's input edge. -/
inductive RawRecursiveRepairOutcome (w : Wiring) :
    (Nat × Tongues) -> Nat -> Nat -> Option (Nat × Tongues) -> Prop
  | done (c : Nat × Tongues) :
      RawRecursiveRepairOutcome w c 0 0 (some c)
  | trap {entry atRepeat : Nat × Tongues} {lead : Nat}
      (lead_le_two : lead <= 2)
      (reaches_repeat : stepN w lead entry = some atRepeat)
      (never_falls : forall n, (stepN w n atRepeat).isSome) :
      RawRecursiveRepairOutcome w entry 1 lead none
  | cons {entry returned : Nat × Tongues}
      {depth tailSteps : Nat} {result : Option (Nat × Tongues)}
      (frame : RawExactInputReturnFrame w entry returned)
      (tail : RawRecursiveRepairOutcome w returned depth tailSteps result) :
      RawRecursiveRepairOutcome w entry (depth + 1)
        (frame.lead + frame.back + tailSteps) result

/-- The raw operational meaning of either recursive outcome. -/
theorem RawRecursiveRepairOutcome.sound
    {w : Wiring} {entry : Nat × Tongues}
    {depth total : Nat} {result : Option (Nat × Tongues)}
    (H : RawRecursiveRepairOutcome w entry depth total result) :
    match result with
      | some root => stepN w total entry = some root
      | none => forall n, (stepN w (total + n) entry).isSome := by
  induction H with
  | done c => rfl
  | @trap entry atRepeat lead hlead hreach hnever =>
      intro n
      simpa [stepN_add, hreach] using hnever n
  | @cons entry returned depth tailSteps result frame tail ih =>
      cases result with
      | none =>
          simp only at ih ⊢
          intro n
          rw [show frame.lead + frame.back + tailSteps + n =
              (frame.lead + frame.back) + (tailSteps + n) by omega,
            stepN_add, frame.run]
          exact ih n
      | some root =>
          simp only at ih ⊢
          rw [show frame.lead + frame.back + tailSteps =
              (frame.lead + frame.back) + tailSteps by omega,
            stepN_add, frame.run]
          exact ih

/-- If every recursive fork returns, the entire repaired serial chain reaches
the recorded root configuration. -/
theorem RawRecursiveRepairOutcome.returns_to_root
    {w : Wiring} {entry root : Nat × Tongues}
    {depth total : Nat}
    (H : RawRecursiveRepairOutcome w entry depth total (some root)) :
    stepN w total entry = some root :=
  H.sound

/-- If a recursive fork takes the trap branch, then no amount of additional
running after the certified prefix can fall off the track.  Enclosing repaired
frames preserve this fact. -/
theorem RawRecursiveRepairOutcome.trap_never_falls
    {w : Wiring} {entry : Nat × Tongues}
    {depth total : Nat}
    (H : RawRecursiveRepairOutcome w entry depth total none) :
    forall n, (stepN w (total + n) entry).isSome :=
  H.sound

/-- Every recursive serial computation uses at most five transitions per
encountered repaired fork, including the terminal trap frame. -/
theorem RawRecursiveRepairOutcome.steps_le_five_mul_depth
    {w : Wiring} {entry : Nat × Tongues}
    {depth total : Nat} {result : Option (Nat × Tongues)}
    (H : RawRecursiveRepairOutcome w entry depth total result) :
    total <= 5 * depth := by
  induction H with
  | done c => omega
  | @trap entry atRepeat lead hlead hreach hnever => omega
  | @cons entry returned depth tailSteps result frame tail ih =>
      have hlocal := frame.steps_le_five
      omega

/-- **Recursive repaired-serial dichotomy.**

For arbitrary wiring and arbitrary recursion depth, a certified serial repair
has only the two local outcomes: exact return to the root, or a non-falling
trajectory.  Repeated repair cannot manufacture a third, fresh forward exit.
-/
theorem recursively_repaired_serial_dichotomy
    {w : Wiring} {entry : Nat × Tongues}
    {depth total : Nat} {result : Option (Nat × Tongues)}
    (H : RawRecursiveRepairOutcome w entry depth total result) :
    And (total <= 5 * depth)
      (match result with
        | some root => stepN w total entry = some root
        | none => forall n, (stepN w (total + n) entry).isSome) := by
  exact And.intro H.steps_le_five_mul_depth H.sound

/-- The exact two-switch theorem supplies either a non-falling fork or one
`RawExactInputReturnFrame`, provided the original input edge is attached.
This is the interface between the isolated `C,D,C` obstruction and the
recursive composition theorem above. -/
theorem two_switch_fork_trap_or_exact_input_frame
    {w : Wiring}
    (hports : forall p q, w.link p = some q ->
      And (p < 6) (q < 6))
    {start finish : Nat × Tongues} {inputMate : Nat}
    (hinput : w.link start.1 = some inputMate)
    (hlive : stepN w 3 start = some finish) :
    Or
      (exists atRepeat visited,
        And (stepN w visited start = some atRepeat)
          (And (visited <= 2)
            (forall n, (stepN w n atRepeat).isSome)))
      (exists returned,
        Nonempty (RawExactInputReturnFrame w start returned)) := by
  obtain ⟨atRepeat, visited, hat, hvisited, hcycle | hreturn⟩ :=
    two_switch_first_repeat_cycle_or_input_return hports hlive
  · exact Or.inl ⟨atRepeat, visited, hat, hvisited, hcycle⟩
  · obtain ⟨backSteps, settled, hback, hreturn⟩ := hreturn
    let returned : Nat × Tongues := (inputMate, settled)
    refine Or.inr ⟨returned, ⟨{
      atRepeat := atRepeat
      lead := visited
      back := backSteps
      lead_le_two := hvisited
      back_le_three := hback
      reaches_repeat := hat
      input_link := ?_
      returns_through_input := ?_
    }⟩⟩
    · simpa [returned] using hinput
    · simpa [returned] using hreturn

end GeneralN
