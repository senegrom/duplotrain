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

/-- Equivalently, for two distinct switches at least one tongue is unchanged
by every raw step. -/
theorem no_raw_mechanically_linked_pair_update
    {w : Wiring} {before after : Nat × Tongues}
    (hstep : step w before = some after) {i j : Nat}
    (hij : i ≠ j) :
    after.2 i = before.2 i ∨ after.2 j = before.2 j := by
  by_cases hi : after.2 i = before.2 i
  · exact Or.inl hi
  · right
    by_cases hj : after.2 j = before.2 j
    · exact hj
    · exact (hij (raw_step_changes_at_most_one_tongue
        hstep hi hj)).elim

/-! ## Exact same-mouth idempotence and the repair cost -/

/-- **Semantic same-mouth idempotence.**  Simplicity is not needed: if the
state at return still grooves every passage of the just-completed call, then
running the call again is an exact fixed point. -/
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

/-- **Raw same-mouth subroutine obstruction.**  After any finite call returns
to the very port through which it was invoked, either the returned
configuration is already a fixed point of that whole call, or the return has
invalidated a concrete passage of its own route.  Thus a reusable unlinked
counter cannot both preserve its calling route and retain a fresh carry
transition. -/
theorem unlinked_same_mouth_fixed_or_requires_repair
    {w : Wiring} {p x : Nat} {u v : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v)) :
    stepN w ((p, x) :: body).length (p, v) = some (p, v) ∨
      ∃ passage ∈ ((p, x) :: body),
        arrive v passage.2 ≠ (passage.1, v) := by
  by_cases hfixed :
      stepN w ((p, x) :: body).length (p, v) = some (p, v)
  · exact Or.inl hfixed
  · exact Or.inr (changed_same_mouth_call_has_broken_groove
      htrace hfixed)

/-- If a second same-mouth invocation really produces a different state,
it necessarily destroys at least one reverse groove of the first invocation.
This is the exact raw "carry requires repair" statement. -/
theorem distinct_second_same_mouth_call_has_broken_groove
    {w : Wiring} {p x : Nat} {u v z : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v))
    (hsecond : stepN w ((p, x) :: body).length (p, v) = some (p, z))
    (hnew : z ≠ v) :
    ∃ passage ∈ ((p, x) :: body),
      arrive v passage.2 ≠ (passage.1, v) := by
  apply changed_same_mouth_call_has_broken_groove htrace
  intro hfixed
  have hpairs : (p, z) = (p, v) :=
    Option.some.inj (hsecond.symm.trans hfixed)
  exact hnew (congrArg Prod.snd hpairs)

/-- A switch-simple call which returns to the same entry port has already
reached a fixed point of the whole call transition. -/
theorem simple_same_mouth_call_fixed
    {w : Wiring} {p x : Nat} {u v : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v))
    (hsimple : SwitchSimple ((p, x) :: body)) :
    stepN w ((p, x) :: body).length (p, v) = some (p, v) := by
  exact grooved_same_mouth_call_fixed htrace
    (htrace.grooved_of_switchSimple hsimple)

/-- After the first same-mouth return, every whole-call iterate is the same
configuration.  This is the reusable-subroutine form of idempotence. -/
theorem simple_same_mouth_call_all_iterates_fixed
    {w : Wiring} {p x : Nat} {u v : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v))
    (hsimple : SwitchSimple ((p, x) :: body)) :
    ∀ n, stepN w
      (n * ((p, x) :: body).length) (p, v) = some (p, v) := by
  let period := ((p, x) :: body).length
  have hperiod : stepN w period (p, v) = some (p, v) := by
    dsimp [period]
    exact simple_same_mouth_call_fixed htrace hsimple
  intro n
  induction n with
  | zero => simp [stepN]
  | succ n ih =>
      have hmul : (n + 1) * period = n * period + period := by
        simpa only [Nat.succ_eq_add_one] using Nat.succ_mul n period
      rw [hmul, stepN_add, ih]
      exact hperiod

/-- In particular, a second invocation cannot produce a new counter value. -/
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

/-- A switch-simple same-mouth module cannot implement two successive
distinct increments. -/
theorem no_simple_same_mouth_second_increment
    {w : Wiring} {p x : Nat} {u v z : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v))
    (hsimple : SwitchSimple ((p, x) :: body))
    (hsecond : stepN w ((p, x) :: body).length (p, v) = some (p, z))
    (hnew : z ≠ v) : False := by
  exact hnew (simple_same_mouth_second_call_same_state
    htrace hsimple hsecond)

/-! ## The single-mouth fork: retrace or trap -/

/-- At the first switch-simple return to a module's mouth switch, the raw
track has only two outcomes: a tongue-stable cycle, or exact reversal of the
entire caller runway.  This is the raw reusable-call obstruction; no graph
compiler or planarity assumption occurs in it. -/
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

/-- If the caller rules out reverse return over its runway, the same-mouth
call must settle on a tongue-stable cycle.  It cannot be a reusable forward
carry subroutine. -/
theorem simple_single_mouth_no_retrace_settles
    {w : Wiring}
    {start : Nat × Tongues} {runway body : List Passage}
    {p x q y : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hbody : PhysicalTrace w (p, u₀) ((p, x) :: body) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: body))
    (hsameMouthSwitch : p / 3 = q / 3)
    (hnext : arrive u q = (y, v))
    (hnoReverse : ∀ settled : Tongues,
      stepN w (runway.length + 1) (q, u) ≠
        (w.link start.1).map (fun ell => (ell, settled))) :
    SettlesOnSimpleCycle w (q, u) := by
  rcases simple_single_mouth_retrace_or_trap hrunway hbody hsimple
      hsameMouthSwitch hnext with htrap | ⟨settled, hreverse⟩
  · exact htrap
  · exact (hnoReverse settled hreverse).elim

/-! ## Repaired reusable tails have four states -/

/-- Once a raw run reaches a compatible pair of manufactured reflectors,
all pairwise-distinct tongue vectors sampled in the future number at most
four.  This is the exact Gray-square trap reached by repaired reusable
single-train gadgets. -/
theorem repaired_unlinked_module_distinct_le_four
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some (g, state))
    (times : List Nat)
    (htimes : ∀ j ∈ times, K ≤ j)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 4 := by
  have hcover : FourNoveltyCover w N start times [] :=
    manufactured_pair_absolute_four_novelty_cover
      A B state hA hB hAB hBA hreach times [] htimes
  have hcount := fourNoveltyCover_distinct_count hcover hnd
  simpa using hcount

/-! ## No scalable unlinked binary counter -/

/-- Every proposed sequence of reusable invocations is still a subsequence
of one raw train trajectory, so its pairwise-distinct counter states obey the
unconditional `26*N+3` state capacity.  This uses no simple-path premise. -/
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

/-- A claimed `bits`-bit reusable counter made solely from `N` independent
lazy points cannot visit all `2^bits` states when that exceeds the raw linear
capacity.  This is an exact general-parameter contradiction, not a bounded
search. -/
theorem no_unlinked_binary_counter_above_linear_capacity
    (w : Wiring) (N bits : Nat)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (invocationTimes : List Nat)
    (hlive : ∀ k ∈ invocationTimes, (stepN w k start).isSome)
    (hallStates : invocationTimes.length = 2 ^ bits)
    (hoverCapacity : 26 * N + 3 < 2 ^ bits) :
    ¬ (invocationTimes.map
      (restrictedTonguesAt w N start)).Nodup := by
  intro hnd
  have hcap := unlinked_reusable_counter_linear_capacity
    w N hN start invocationTimes hlive hnd
  omega

end GeneralN
