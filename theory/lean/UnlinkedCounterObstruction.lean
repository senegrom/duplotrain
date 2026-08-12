import TrackQuantitativeTight
import ManufacturedPairTailNovelty

/-!
# Obstructions to reusable counters made from unlinked lazy points

This file states counter obstructions directly in the raw `Wiring` / `stepN`
language.  A raw lazy point has one private tongue: a trailing traversal may
write that tongue, but there is no operation which changes a second switch at
the same time.  Thus mechanically linked points and sprung/one-way roundabouts
are deliberately absent from this model.

The results below isolate what this means for a reusable subroutine.

* A switch-simple call which returns to the *same entry port* is idempotent:
  after its first return, every further invocation has the same state.
* More generally, the first switch-simple return to the mouth switch either
  settles on a tongue-stable cycle or reverses the complete caller runway.
  If reverse return is forbidden, the call is therefore trapped.
* Once repair has produced the only reusable two-reflector mechanism, its
  entire future has at most four distinct tongue vectors.
* Without any simplicity or repaired-tail premise, the unconditional raw
  linear state law bounds every proposed invocation sequence by `26*N+3`.
  Consequently a claimed `b`-bit unlinked counter visiting all `2^b` states
  is impossible whenever `2^b > 26*N+3`.

These are general-`N` theorems.  They do **not** close the sharper open
`GeneralN.StateLaw` (`N+6`); they rule out the exponential reusable-counter
attack and make the remaining coefficient-one problem explicit.
-/

namespace GeneralN

/-! ## The raw model has no mechanically linked update -/

/-- One raw train step preserves every tongue except possibly the tongue of
the switch whose port the train enters. -/
theorem raw_step_preserves_unentered_tongue
    {w : Wiring} {before after : Nat × Tongues}
    (hstep : step w before = some after) {j : Nat}
    (hforeign : j ≠ before.1 / 3) :
    after.2 j = before.2 j := by
  have hparts := step_some_parts hstep
  have harrive : arrive before.2 before.1 =
      (exitPort before, after.2) := by
    apply Prod.ext
    · rfl
    · exact hparts.2.symm
  exact arrive_preserves_other harrive hforeign

/-- Hence a raw step cannot change two distinct tongue coordinates.  This is
the exact semantic mismatch with a mechanically linked pair of points. -/
theorem raw_step_changes_at_most_one_tongue
    {w : Wiring} {before after : Nat × Tongues}
    (hstep : step w before = some after) {i j : Nat}
    (hi : after.2 i ≠ before.2 i)
    (hj : after.2 j ≠ before.2 j) :
    i = j := by
  have hiEntry : i = before.1 / 3 := by
    by_cases h : i = before.1 / 3
    · exact h
    · exact (hi (raw_step_preserves_unentered_tongue hstep h)).elim
  have hjEntry : j = before.1 / 3 := by
    by_cases h : j = before.1 / 3
    · exact h
    · exact (hj (raw_step_preserves_unentered_tongue hstep h)).elim
  exact hiEntry.trans hjEntry.symm

theorem grooved_same_mouth_call_fixed
    {w : Wiring} {p x : Nat} {u v : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v))
    (hgrooved : PassagesGrooved v ((p, x) :: body)) :
    stepN w ((p, x) :: body).length (p, v) = some (p, v) := by
  exact run_grooved_passages w v p x p body
    htrace.linked hgrooved htrace.last_link

/-- Any non-idempotent same-mouth return has paid a concrete repair cost:
some passage of the preceding call is no longer configured for reverse
traversal in the returned tongue state. -/
theorem changed_same_mouth_call_has_broken_groove
    {w : Wiring} {p x : Nat} {u v : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v))
    (hchanged : stepN w ((p, x) :: body).length (p, v) ≠ some (p, v)) :
    ∃ passage ∈ ((p, x) :: body),
      arrive v passage.2 ≠ (passage.1, v) := by
  by_cases hbad : ∃ passage ∈ ((p, x) :: body),
      arrive v passage.2 ≠ (passage.1, v)
  · exact hbad
  · have hgrooved : PassagesGrooved v ((p, x) :: body) := by
      intro passage hp
      by_cases heq : arrive v passage.2 = (passage.1, v)
      · exact heq
      · exact (hbad ⟨passage, hp, heq⟩).elim
    exact (hchanged (grooved_same_mouth_call_fixed htrace hgrooved)).elim

theorem simple_same_mouth_call_fixed
    {w : Wiring} {p x : Nat} {u v : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v))
    (hsimple : SwitchSimple ((p, x) :: body)) :
    stepN w ((p, x) :: body).length (p, v) = some (p, v) := by
  exact grooved_same_mouth_call_fixed htrace
    (htrace.grooved_of_switchSimple hsimple)

theorem simple_same_mouth_second_call_same_state
    {w : Wiring} {p x : Nat} {u v z : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v))
    (hsimple : SwitchSimple ((p, x) :: body))
    (hsecond : stepN w ((p, x) :: body).length (p, v) = some (p, z)) :
    z = v := by
  have hfixed := simple_same_mouth_call_fixed htrace hsimple
  have hpairs : (p, z) = (p, v) :=
    Option.some.inj (hsecond.symm.trans hfixed)
  exact congrArg Prod.snd hpairs

theorem simple_single_mouth_retrace_or_trap
    {w : Wiring}
    {start : Nat × Tongues} {runway body : List Passage}
    {p x q y : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hbody : PhysicalTrace w (p, u₀) ((p, x) :: body) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: body))
    (hsameMouthSwitch : p / 3 = q / 3)
    (hnext : arrive u q = (y, v)) :
    SettlesOnSimpleCycle w (q, u) ∨
      ∃ settled : Tongues,
        stepN w (runway.length + 1) (q, u) =
          (w.link start.1).map (fun ell => (ell, settled)) := by
  simpa [SettlesOnSimpleCycle] using
    (first_revisit_fork hrunway hbody hsimple hsameMouthSwitch hnext)

theorem unlinked_reusable_counter_linear_capacity
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (invocationTimes : List Nat)
    (hlive : ∀ k ∈ invocationTimes, (stepN w k start).isSome)
    (hnd : (invocationTimes.map
      (restrictedTonguesAt w N start)).Nodup) :
    invocationTimes.length ≤ 26 * N + 3 := by
  change (invocationTimes.map (fun k =>
    VectorCount.restrict N (tonguesAt w start k))).Nodup at hnd
  apply state_law_linear_twenty_six w N hN start invocationTimes hlive
  exact hnd

end GeneralN
