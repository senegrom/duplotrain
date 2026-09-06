import GeneralN

/-!
# Physical trace lemmas for lazy points

This file starts a direct formalisation of the first-repeated-track argument
of Chalcraft--Greene and Aaronson.  It deliberately works over the raw
`GeneralN.Wiring` dynamics: a physical track edge is the symmetric `link`
pairing, and a visit to a switch is the local passage from its entry port to
its exit port.

The key local fact is `arrive_back`: every passage leaves a lazy point set so
that immediately traversing the same local passage backwards is a no-op.  It
is the exact, one-switch form of the groove/retrace argument.
-/

namespace GeneralN

/-- The port through which a configuration leaves its current switch. -/
def exitPort (c : Nat × Tongues) : Nat :=
  (arrive c.2 c.1).1

/-- The tongues immediately after traversing the current switch. -/
def arrivedTongues (c : Nat × Tongues) : Tongues :=
  (arrive c.2 c.1).2

/-- Entering and leaving a switch use ports of that same switch. -/
theorem arrive_exit_switch (t : Tongues) (p : Nat) :
    (arrive t p).1 / 3 = p / 3 := by
  unfold arrive
  by_cases hp : p % 3 = 0
  · rw [if_pos hp]
    cases ht : t (p / 3) <;> simp [branchPort] <;> omega
  · rw [if_neg hp]
    omega

/-- Every local passage uses the stem and exactly one branch. -/
theorem arrive_stem_endpoint (t : Tongues) (p : Nat) :
    p = 3 * (p / 3) ∨ (arrive t p).1 = 3 * (p / 3) := by
  unfold arrive
  by_cases hp : p % 3 = 0
  · left
    omega
  · right
    simp [hp]

/-- The two local endpoints of a switch passage are distinct. -/
theorem arrive_exit_ne (t : Tongues) (p : Nat) :
    (arrive t p).1 ≠ p := by
  unfold arrive
  by_cases hp : p % 3 = 0
  · rw [if_pos hp]
    cases ht : t (p / 3) <;> simp [branchPort] <;> omega
  · rw [if_neg hp]
    omega

/-- **Degree-three intersection.**  Any two passages through the same lazy
point share a port.  Equivalently, revisiting a switch necessarily reuses one
of the three incident physical track edges either on arrival or immediately
on departure.  This is Observation 1 of the first-repeated-edge proof. -/
theorem same_switch_passages_share_port
    (u v : Tongues) (p q : Nat) (hsw : p / 3 = q / 3) :
    p = q ∨ p = (arrive v q).1 ∨
      (arrive u p).1 = q ∨ (arrive u p).1 = (arrive v q).1 := by grind [
        arrive_stem_endpoint]

/-- **One-switch groove.**  A lazy point is left configured to undo the
passage just made: entering the exit port immediately afterwards returns to
the original entry port and changes no tongue. -/
theorem arrive_back (t : Tongues) (p : Nat) :
    arrive (arrive t p).2 (arrive t p).1 = (p, (arrive t p).2) := by
  by_cases hp : p % 3 = 0
  · have hstem : 3 * (p / 3) = p := by omega
    cases ht : t (p / 3) with
    | false =>
      have hbdiv : (3 * (p / 3) + 1) / 3 = p / 3 := by omega
      have hbval : bval (3 * (p / 3) + 1) = false := by
        unfold bval
        have hm : (3 * (p / 3) + 1) % 3 = 1 := by omega
        rw [hm]
        rfl
      have hpin : pin t (3 * (p / 3) + 1) = t := by
        apply pin_of_agrees
        rw [hbdiv, hbval, ht]
      have hfirst : arrive t p = (3 * (p / 3) + 1, t) := by
        simp [arrive, hp, branchPort, ht]
      rw [hfirst]
      have hsecond :
          arrive t (3 * (p / 3) + 1) = (3 * (p / 3), t) := by
        simp [arrive, hbdiv, hpin]
      rw [hsecond, hstem]
    | true =>
      have hbdiv : (3 * (p / 3) + 2) / 3 = p / 3 := by omega
      have hbval : bval (3 * (p / 3) + 2) = true := by
        unfold bval
        have hm : (3 * (p / 3) + 2) % 3 = 2 := by omega
        rw [hm]
        rfl
      have hpin : pin t (3 * (p / 3) + 2) = t := by
        apply pin_of_agrees
        rw [hbdiv, hbval, ht]
      have hfirst : arrive t p = (3 * (p / 3) + 2, t) := by
        simp [arrive, hp, branchPort, ht]
      rw [hfirst]
      have hsecond :
          arrive t (3 * (p / 3) + 2) = (3 * (p / 3), t) := by
        simp [arrive, hbdiv, hpin]
      rw [hsecond, hstem]
  · have hstemmod : (3 * (p / 3)) % 3 = 0 := by omega
    have hstemdiv : (3 * (p / 3)) / 3 = p / 3 := by omega
    have hpinned : (pin t p) (p / 3) = bval p := by
      simp [pin]
    have hbranch : branchPort (p / 3) ((pin t p) (p / 3)) = p := by
      rw [hpinned]
      exact branchPort_bval hp
    simp [arrive, hp, hstemmod, hstemdiv, hbranch]

/-- Decompose one successful physical step into its switch passage and its
plain-track edge. -/
theorem step_some_parts {w : Wiring} {c d : Nat × Tongues}
    (h : step w c = some d) :
    w.link (exitPort c) = some d.1 ∧ d.2 = arrivedTongues c := by
  unfold step at h
  unfold exitPort arrivedTongues
  cases ha : arrive c.2 c.1 with
  | mk x u =>
    simp only
    cases hl : w.link x with
    | none =>
      rw [ha, hl] at h
      contradiction
    | some q =>
      rw [ha, hl] at h
      simp at h
      cases h
      exact ⟨rfl, rfl⟩

/-- One local switch passage, stored as `(entryPort, exitPort)`. -/
abbrev Passage := Nat × Nat

/-- Every recorded passage is still configured for its exact reverse. -/
def PassagesGrooved (u : Tongues) (passages : List Passage) : Prop :=
  ∀ passage ∈ passages,
    arrive u passage.2 = (passage.1, u)

/-- Consecutive switch passages are joined by physical track edges. -/
def LinkedPassages (w : Wiring) : List Passage → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      w.link a.2 = some b.1 ∧ LinkedPassages w (b :: rest)

/-- Exit port of the last passage in a nonempty list whose first exit is `x`. -/
def lastPassageExit (x : Nat) : List Passage → Nat
  | [] => x
  | passage :: rest => lastPassageExit passage.2 rest

/-- A successful physical run, recorded one switch passage at a time.  The
plain-track edge after a passage is included as the link premise of `cons`.
This is an intentionally thin wrapper around the raw `step` semantics. -/
inductive PhysicalTrace (w : Wiring) :
    (Nat × Tongues) → List Passage → (Nat × Tongues) → Prop
  | nil (c : Nat × Tongues) : PhysicalTrace w c [] c
  | cons {p x q : Nat} {u v : Tongues}
      {passages : List Passage} {finish : Nat × Tongues}
      (harrive : arrive u p = (x, v))
      (hlink : w.link x = some q)
      (tail : PhysicalTrace w (q, v) passages finish) :
      PhysicalTrace w (p, u) ((p, x) :: passages) finish

/-- The switch visited by a recorded passage. -/
def passageSwitch (passage : Passage) : Nat := passage.1 / 3

/-- A trace segment is simple when it visits each switch at most once. -/
def SwitchSimple (passages : List Passage) : Prop :=
  (passages.map passageSwitch).Nodup

/-- A physical trace executes for exactly the number of passages it stores. -/
theorem PhysicalTrace.sound {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (h : PhysicalTrace w start passages finish) :
    stepN w passages.length start = some finish := by
  induction h with
  | nil c => simp [stepN]
  | @cons p x q u v passages finish harrive hlink tail ih =>
      simp [stepN, step, harrive, hlink, ih]

/-- Replay a recorded spatial route in any tongue invariant that each of its
passages preserves. The recorded tongue states are only witnesses for its
track links; they need not satisfy the invariant. -/
theorem PhysicalTrace.replay_preserving
    {w : Wiring} {start finish : Nat × Tongues} {route : List Passage}
    (htrace : PhysicalTrace w start route finish)
    (allowed : Tongues → Prop)
    (hlocal : ∀ passage ∈ route, ∀ u, allowed u →
      ∃ v, arrive u passage.1 = (passage.2, v) ∧ allowed v)
    {u : Tongues} (hu : allowed u) :
    ∃ v, PhysicalTrace w (start.1, u) route (finish.1, v) ∧ allowed v ∧
      ∀ d, d ≤ route.length → ∃ port phase,
        stepN w d (start.1, u) = some (port, phase) ∧ allowed phase := by
  induction htrace generalizing u with
  | nil c =>
      refine ⟨u, PhysicalTrace.nil _, hu, ?_⟩
      intro d hd
      have : d = 0 := by simpa using hd
      subst d
      exact ⟨c.1, u, rfl, hu⟩
  | @cons p x q old next route finish harrive hlink tail ih =>
      obtain ⟨middle, hstep, hm⟩ := hlocal (p, x) List.mem_cons_self u hu
      obtain ⟨v, htail, hv, hcover⟩ := ih
        (fun passage hp => hlocal passage (List.mem_cons_of_mem _ hp)) hm
      refine ⟨v, PhysicalTrace.cons hstep hlink htail, hv, ?_⟩
      intro d hd
      cases d with
      | zero => exact ⟨p, u, rfl, hu⟩
      | succ d =>
          obtain ⟨port, phase, hr, hp⟩ := hcover d (by simpa using hd)
          exact ⟨port, phase, by simpa [stepN, step, hstep, hlink] using hr, hp⟩

/-- Every prefix of a live finite run is itself live. -/
theorem stepN_prefix_some
    {w : Wiring} {start finish : Nat × Tongues} {d K : Nat}
    (hd : d ≤ K) (hfinish : stepN w K start = some finish) :
    ∃ middle, stepN w d start = some middle := by
  let rest := K - d
  have hsplit : K = d + rest := by
    dsimp [rest]
    omega
  rw [hsplit, stepN_add] at hfinish
  cases hprefix : stepN w d start with
  | none => simp [hprefix] at hfinish
  | some middle => exact ⟨middle, rfl⟩

/-- Pointwise covers compose at a reached configuration. -/
theorem stepN_cover_append
    {w : Wiring} {start middle : Nat × Tongues} {left right : Nat}
    {allowed : Tongues → Prop}
    (hreach : stepN w left start = some middle)
    (hleft : ∀ d, d ≤ left → ∃ port phase,
      stepN w d start = some (port, phase) ∧ allowed phase)
    (hright : ∀ d, d ≤ right → ∃ port phase,
      stepN w d middle = some (port, phase) ∧ allowed phase) :
    ∀ d, d ≤ left + right → ∃ port phase,
      stepN w d start = some (port, phase) ∧ allowed phase := by
  intro d hd
  by_cases hpre : d ≤ left
  · exact hleft d hpre
  · obtain ⟨port, phase, hr, hs⟩ := hright (d - left) (by omega)
    refine ⟨port, phase, ?_, hs⟩
    have heq : d = left + (d - left) := by omega
    rw [heq, stepN_add, hreach]
    exact hr

/-- Covered positive-length excursions suffice for an all-time cover.
The invariant is required only at excursion boundaries; intermediate states
need satisfy only `allowed`. Neither periodicity nor finite state is needed. -/
theorem stepN_covered_of_progress
    {w : Wiring} (invariant : Nat × Tongues → Prop) (allowed : Tongues → Prop)
    (progress : ∀ start, invariant start → ∃ travel finish,
      0 < travel ∧ stepN w travel start = some finish ∧ invariant finish ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d start = some (port, phase) ∧ allowed phase)
    {start : Nat × Tongues} (hstart : invariant start) (d : Nat) :
    ∃ port phase, stepN w d start = some (port, phase) ∧ allowed phase := by
  induction d using Nat.strongRecOn generalizing start with
  | ind d ih =>
      obtain ⟨travel, finish, hpos, hreach, hfinish, hcover⟩ := progress start hstart
      by_cases hpre : d ≤ travel
      · exact hcover d hpre
      · obtain ⟨port, phase, hr, hp⟩ := ih (d - travel) (by omega) hfinish
        refine ⟨port, phase, ?_, hp⟩
        have heq : d = travel + (d - travel) := by omega
        rw [heq, stepN_add, hreach]
        exact hr

/-- A closed spatial route whose passages preserve a tongue invariant can be
repeated indefinitely from any state in that invariant. Its recorded initial
and final tongue vectors need not agree: no dynamical period is required. -/
theorem PhysicalTrace.spatial_loop_invariant
    {w : Wiring} {p : Nat} {u v initial : Tongues} {route : List Passage}
    (htrace : PhysicalTrace w (p, u) route (p, v))
    (allowed : Tongues → Prop) (hpositive : 0 < route.length)
    (hlocal : ∀ passage ∈ route, ∀ state, allowed state →
      ∃ next, arrive state passage.1 = (passage.2, next) ∧ allowed next)
    (hinitial : allowed initial) (d : Nat) :
    ∃ port phase, stepN w d (p, initial) = some (port, phase) ∧ allowed phase := by
  apply stepN_covered_of_progress
    (fun c => c.1 = p ∧ allowed c.2) allowed ?_ ⟨rfl, hinitial⟩ d
  intro start hs
  rcases start with ⟨q, state⟩
  rcases hs with ⟨rfl, hstate⟩
  obtain ⟨next, hr, hn, hcover⟩ := htrace.replay_preserving allowed hlocal hstate
  exact ⟨route.length, (q, next), hpositive, hr.sound, ⟨rfl, hn⟩, hcover⟩

/-- The passage list extracted from a physical trace is linked. -/
theorem PhysicalTrace.linked {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (h : PhysicalTrace w start passages finish) :
    LinkedPassages w passages := by
  induction h with
  | nil => trivial
  | @cons p x q u v passages finish harrive hlink tail ih =>
      cases tail with
      | nil => trivial
      | cons harrive' hlink' tail' =>
          exact ⟨hlink, ih⟩

/-- Split a trace at a list append, exposing the intermediate physical
configuration. -/
theorem PhysicalTrace.split_append {w : Wiring}
    {start finish : Nat × Tongues} {left right : List Passage}
    (h : PhysicalTrace w start (left ++ right) finish) :
    ∃ middle, PhysicalTrace w start left middle ∧
      PhysicalTrace w middle right finish := by
  induction left generalizing start with
  | nil =>
      exact ⟨start, PhysicalTrace.nil start, by simpa using h⟩
  | cons passage left ih =>
      rcases passage with ⟨p, x⟩
      cases h with
      | @cons _ _ q u v _ _ harrive hlink tail =>
          obtain ⟨middle, hleft, hright⟩ := ih tail
          exact ⟨middle, PhysicalTrace.cons harrive hlink hleft, hright⟩

/-- A suffix after a named passage retains its original recorded tongue state.
No re-grooving or switch-simplicity assumption is needed to trim a witness. -/
theorem PhysicalTrace.suffix_after_passage {w : Wiring}
    {start finish : Nat × Tongues} {before after : List Passage}
    {p x outside : Nat}
    (h : PhysicalTrace w start (before ++ (p, x) :: after) finish)
    (houtside : w.link x = some outside) :
    ∃ state, PhysicalTrace w (outside, state) after finish := by
  obtain ⟨middle, _, hrest⟩ := h.split_append
  cases hrest with
  | @cons _ _ next _ state _ _ _ hlink tail =>
      have hnext : next = outside := Option.some.inj (hlink.symm.trans houtside)
      subst next
      exact ⟨state, tail⟩

/-- Concatenate two physical traces. -/
theorem PhysicalTrace.append {w : Wiring}
    {start middle finish : Nat × Tongues}
    {left right : List Passage}
    (hleft : PhysicalTrace w start left middle)
    (hright : PhysicalTrace w middle right finish) :
    PhysicalTrace w start (left ++ right) finish := by
  induction hleft with
  | nil => simpa using hright
  | cons harrive hlink tail ih =>
      exact PhysicalTrace.cons harrive hlink (ih hright)

/-- The final exit port stored by a nonempty trace is linked to the entry port
of its finishing configuration. -/
theorem PhysicalTrace.last_link {w : Wiring}
    {p x : Nat} {start finish : Nat × Tongues}
    {rest : List Passage}
    (h : PhysicalTrace w start ((p, x) :: rest) finish) :
    w.link (lastPassageExit x rest) = some finish.1 := by
  induction rest generalizing p x start finish with
  | nil =>
      cases h with
      | @cons _ _ q _ v _ _ harrive hlink tail =>
          cases tail
          simpa [lastPassageExit] using hlink
  | cons passage rest ih =>
      rcases passage with ⟨q, y⟩
      cases h with
      | @cons _ _ r _ v _ _ harrive hlink tail =>
          cases tail with
          | cons harrive' hlink' restTrace =>
              have htail := ih
                (PhysicalTrace.cons harrive' hlink' restTrace)
              simpa [lastPassageExit] using htail

/-- Expose the first local passage of a nonempty trace without destructively
case-splitting the rest of the trace. -/
theorem PhysicalTrace.head_arrive {w : Wiring}
    {p x : Nat} {start finish : Nat × Tongues}
    {rest : List Passage}
    (h : PhysicalTrace w start ((p, x) :: rest) finish) :
    start.1 = p ∧ ∃ v, arrive start.2 p = (x, v) := by
  cases h with
  | @cons _ _ q _ v _ _ harrive hlink tail =>
      exact ⟨rfl, v, harrive⟩

/-- The switch owning the final exit of a nonempty trace occurs in the
trace's passage-switch list. -/
theorem PhysicalTrace.last_exit_switch_mem {w : Wiring}
    {p x : Nat} {start finish : Nat × Tongues}
    {rest : List Passage}
    (h : PhysicalTrace w start ((p, x) :: rest) finish) :
    lastPassageExit x rest / 3 ∈
      (((p, x) :: rest).map passageSwitch) := by
  induction rest generalizing p x start finish with
  | nil =>
      have ha := h.head_arrive
      obtain ⟨v, harrive⟩ := ha.2
      have hs := arrive_exit_switch start.2 p
      rw [harrive] at hs
      simp [lastPassageExit, passageSwitch, hs]
  | cons passage rest ih =>
      rcases passage with ⟨q, y⟩
      cases h with
      | @cons _ _ r _ v _ _ harrive hlink tail =>
          cases tail with
          | cons harrive' hlink' restTrace =>
              have htail := ih
                (PhysicalTrace.cons harrive' hlink' restTrace)
              exact List.mem_cons_of_mem _ (by
                simpa [lastPassageExit] using htail)

/-- A switch-simple nonempty trace cannot have its final exit port equal its
first entry port. -/
theorem PhysicalTrace.simple_last_exit_ne_first_entry {w : Wiring}
    {p x : Nat} {start finish : Nat × Tongues}
    {rest : List Passage}
    (h : PhysicalTrace w start ((p, x) :: rest) finish)
    (hsimple : SwitchSimple ((p, x) :: rest)) :
    lastPassageExit x rest ≠ p := by
  cases rest with
  | nil =>
      intro hEq
      have hxne := arrive_exit_ne start.2 p
      obtain ⟨v, harrive⟩ := h.head_arrive.2
      rw [harrive] at hxne
      exact hxne (by simpa [lastPassageExit] using hEq)
  | cons passage rest =>
      rcases passage with ⟨q, y⟩
      intro hEq
      unfold SwitchSimple at hsimple
      simp only [List.map_cons, List.nodup_cons] at hsimple
      apply hsimple.1
      cases h with
      | @cons _ _ r _ v _ _ harrive hlink tail =>
          cases tail with
          | cons harrive' hlink' restTrace =>
              have htailMem := (PhysicalTrace.cons harrive' hlink'
                restTrace).last_exit_switch_mem
              have hkey : passageSwitch (p, x) =
                  lastPassageExit y rest / 3 := by
                simp [passageSwitch, ← hEq, lastPassageExit]
              rw [hkey]
              exact htailMem

/-- Every successful finite raw run has a physical passage trace. -/
theorem physicalTrace_of_stepN (w : Wiring) :
    ∀ {n : Nat} {start finish : Nat × Tongues},
      stepN w n start = some finish →
      ∃ passages, passages.length = n ∧
        PhysicalTrace w start passages finish := by
  intro n
  induction n with
  | zero =>
      intro start finish h
      simp [stepN] at h
      subst finish
      exact ⟨[], rfl, PhysicalTrace.nil start⟩
  | succ n ih =>
      intro start finish h
      cases hs : step w start with
      | none =>
          simp [stepN, hs] at h
      | some middle =>
          have htail : stepN w n middle = some finish := by
            simpa [stepN, hs] using h
          obtain ⟨passages, hlen, htrace⟩ := ih htail
          cases ha : arrive start.2 start.1 with
          | mk x v =>
              cases hl : w.link x with
              | none =>
                  simp [step, ha, hl] at hs
              | some q =>
                  have hmiddle : middle = (q, v) := by
                    simpa [step, ha, hl] using hs.symm
                  subst middle
                  refine ⟨(start.1, x) :: passages, ?_, ?_⟩
                  · simp [hlen]
                  · exact PhysicalTrace.cons ha hl htrace

/-- A switch passage can modify only its own tongue. -/
theorem arrive_preserves_other {u v : Tongues} {p x j : Nat}
    (harrive : arrive u p = (x, v)) (hne : j ≠ p / 3) :
    v j = u j := by
  unfold arrive at harrive
  by_cases hp : p % 3 = 0
  · rw [if_pos hp] at harrive
    injection harrive with _ hv
    rw [← hv]
  · rw [if_neg hp] at harrive
    injection harrive with _ hv
    rw [← hv]
    simp [pin, hne]

/-- A trace which never visits switch `j` preserves tongue `j`. -/
theorem PhysicalTrace.preserves {w : Wiring}
    {start finish : Nat × Tongues} {passages : List Passage}
    (h : PhysicalTrace w start passages finish) (j : Nat)
    (hforeign : ∀ passage ∈ passages, passageSwitch passage ≠ j) :
    finish.2 j = start.2 j := by
  induction h with
  | nil => rfl
  | @cons p x q u v passages finish harrive hlink tail ih =>
      have hpj : p / 3 ≠ j :=
        hforeign (p, x) List.mem_cons_self
      have hv : v j = u j := arrive_preserves_other harrive hpj.symm
      have htailForeign :
          ∀ passage ∈ passages, passageSwitch passage ≠ j := by
        intro passage hp
        exact hforeign passage (List.mem_cons_of_mem _ hp)
      exact (ih htailForeign).trans hv

/-- Along a switch-simple trace, each intermediate tongue is either its
initial or final value: a switch cannot be visited in both halves of a split.
This needs neither a finite-wiring bound nor a productive-writer argument. -/
theorem PhysicalTrace.prefix_coordinate_eq_endpoint {w : Wiring}
    {start finish middle : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) {k : Nat}
    (hk : k ≤ passages.length) (hrun : stepN w k start = some middle)
    (j : Nat) : middle.2 j = start.2 j ∨ middle.2 j = finish.2 j := by
  have hsplit : PhysicalTrace w start
      (passages.take k ++ passages.drop k) finish := by
    simpa only [List.take_append_drop] using htrace
  obtain ⟨mid, hleft, hright⟩ := hsplit.split_append
  have hmid : mid = middle := by
    have hsound := hleft.sound
    rw [List.length_take_of_le hk, hrun] at hsound
    exact (Option.some.inj hsound).symm
  subst mid
  have hnd : ((passages.take k).map passageSwitch ++
      (passages.drop k).map passageSwitch).Nodup := by
    rw [← List.map_append, List.take_append_drop]
    exact hsimple
  by_cases hprefix : j ∈ (passages.take k).map passageSwitch
  · right
    symm
    apply hright.preserves
    intro passage hp heq
    exact (List.nodup_append.mp hnd).2.2 j hprefix j
      (List.mem_map.mpr ⟨passage, hp, heq⟩) rfl
  · left
    apply hleft.preserves
    intro passage hp heq
    exact hprefix (List.mem_map.mpr ⟨passage, hp, heq⟩)

/-- Every switch in a live trace is one of the `N` switches named by a
finite-wiring bound. -/
theorem PhysicalTrace.switch_lt {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues} {passages : List Passage}
    (h : PhysicalTrace w start passages finish) :
    ∀ passage ∈ passages, passageSwitch passage < N := by
  induction h with
  | nil =>
      intro passage hp
      cases hp
  | @cons p x q u v passages finish harrive hlink tail ih =>
      intro passage hp
      rcases List.mem_cons.mp hp with hhead | htail
      · subst passage
        unfold passageSwitch
        have hx : x < 3 * N := (hN x q hlink).1
        have hsw := arrive_exit_switch u p
        rw [harrive] at hsw
        omega
      · exact ih passage htail

/-- Every recorded passage really uses the stem of its switch. -/
theorem PhysicalTrace.passage_stem_endpoint {w : Wiring}
    {start finish : Nat × Tongues} {passages : List Passage}
    (h : PhysicalTrace w start passages finish) :
    ∀ passage ∈ passages,
      passage.1 = 3 * passageSwitch passage ∨
        passage.2 = 3 * passageSwitch passage := by
  induction h with
  | nil =>
      intro passage hp
      cases hp
  | @cons p x q u v passages finish harrive hlink tail ih =>
      intro passage hp
      rcases List.mem_cons.mp hp with hhead | htail
      · subst passage
        unfold passageSwitch
        have hs := arrive_stem_endpoint u p
        rw [harrive] at hs
        exact hs
      · exact ih passage htail

/-- Two valid recorded passages through the same switch share one endpoint. -/
theorem recorded_passages_share_port {a b : Passage}
    (ha : a.1 = 3 * passageSwitch a ∨
      a.2 = 3 * passageSwitch a)
    (hb : b.1 = 3 * passageSwitch b ∨
      b.2 = 3 * passageSwitch b)
    (hsw : passageSwitch a = passageSwitch b) :
    a.1 = b.1 ∨ a.1 = b.2 ∨ a.2 = b.1 ∨ a.2 = b.2 := by grind

theorem nodup_subset_length_nat {α : Type} [BEq α] [LawfulBEq α]
    {xs pool : List α}
    (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ pool) :
    xs.length ≤ pool.length := by
  induction xs generalizing pool with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ pool := hsub x List.mem_cons_self
      have htail : ∀ y ∈ rest, y ∈ pool.erase x := by
        intro y hy
        have hyU := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hEq => hnd.1 (hEq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyU
      have hle := ih hnd.2 htail
      rw [List.length_erase_of_mem hx] at hle
      simp only [List.length_cons]
      have hpos : 0 < pool.length := by
        cases pool with
        | nil => cases hx
        | cons _ _ => simp
      omega

theorem nodup_nat_lt_length {N : Nat} {xs : List Nat}
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x < N) :
    xs.length ≤ N := by
  have hsub : ∀ x ∈ xs, x ∈ List.range N := by
    intro x hx
    exact List.mem_range.mpr (hlt x hx)
  have hle := nodup_subset_length_nat hnd hsub
  simpa only [List.length_range] using hle

/-- Scan a list from the front until either it ends without repetition under
`key`, or the next element repeats a key in the preceding simple prefix. -/
theorem first_repeat_by {α : Type} (key : α → Nat) :
    ∀ xs : List α,
      (xs.map key).Nodup ∨
        ∃ before repeated after,
          xs = before ++ repeated :: after ∧
          (before.map key).Nodup ∧
          key repeated ∈ before.map key := by
  intro xs
  induction xs with
  | nil => exact Or.inl (by simp)
  | cons x tail ih =>
      rcases ih with htail | ⟨before, repeated, after, hEq, hbefore, hmem⟩
      · by_cases hx : key x ∈ tail.map key
        · obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
          obtain ⟨left, right, hyEq⟩ := List.append_of_mem hy
          subst tail
          have htail' :
              (left.map key ++ (y :: right).map key).Nodup := by
            simpa only [List.map_append] using htail
          have hparts := List.nodup_append.mp htail'
          have hleft : (left.map key).Nodup := by
            simpa only [List.map_append] using hparts.1
          have hxleft : key x ∉ left.map key := by
            intro hxin
            have hcross := hparts.2.2
            have hne := hcross (key x)
              (by simpa only [List.map_append] using hxin)
              (key y)
              (by
                apply List.mem_map.mpr
                exact ⟨y, List.mem_cons_self, rfl⟩)
            exact hne hxy.symm
          right
          refine ⟨x :: left, y, right, ?_, ?_, ?_⟩
          · simp
          · simp only [List.map_cons, List.nodup_cons]
            exact ⟨hxleft, hleft⟩
          · simp only [List.map_cons, List.mem_cons]
            exact Or.inl hxy
        · left
          simp only [List.map_cons, List.nodup_cons]
          exact ⟨hx, htail⟩
      · subst tail
        by_cases hx : key x ∈ before.map key
        · obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
          obtain ⟨left, right, hyEq⟩ := List.append_of_mem hy
          subst before
          have hbefore' :
              (left.map key ++ (y :: right).map key).Nodup := by
            simpa only [List.map_append] using hbefore
          have hparts := List.nodup_append.mp hbefore'
          have hleft : (left.map key).Nodup := by
            simpa only [List.map_append] using hparts.1
          have hxleft : key x ∉ left.map key := by
            intro hxin
            have hcross := hparts.2.2
            have hne := hcross (key x)
              (by simpa only [List.map_append] using hxin)
              (key y)
              (by
                apply List.mem_map.mpr
                exact ⟨y, List.mem_cons_self, rfl⟩)
            exact hne hxy.symm
          right
          refine ⟨x :: left, y, right ++ repeated :: after, ?_, ?_, ?_⟩
          · simp
          · simp only [List.map_cons, List.nodup_cons]
            exact ⟨hxleft, hleft⟩
          · simp only [List.map_cons, List.mem_cons]
            exact Or.inl hxy
        · right
          refine ⟨x :: before, repeated, after, ?_, ?_, ?_⟩
          · simp
          · simp only [List.map_cons, List.nodup_cons]
            exact ⟨hx, hbefore⟩
          · exact List.mem_cons_of_mem _ hmem

/-- Every nonsimple passage list has a unique-in-the-prefix first revisit
decomposition.  The theorem records exactly the data needed by the
first-repeated-edge case split. -/
theorem first_revisit_split {passages : List Passage}
    (hnsimple : ¬ SwitchSimple passages) :
    ∃ before repeated after,
      passages = before ++ repeated :: after ∧
      SwitchSimple before ∧
      passageSwitch repeated ∈ before.map passageSwitch := by
  unfold SwitchSimple at hnsimple
  rcases first_repeat_by passageSwitch passages with hsimple | hrepeat
  · exact absurd hsimple hnsimple
  · exact hrepeat

/-- A switch-simple live trace in an `N`-switch wiring has at most `N`
passages. -/
theorem PhysicalTrace.simple_length_le {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues} {passages : List Passage}
    (h : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    passages.length ≤ N := by
  unfold SwitchSimple at hsimple
  have hlt : ∀ x ∈ passages.map passageSwitch, x < N := by
    intro x hx
    obtain ⟨passage, hp, rfl⟩ := List.mem_map.mp hx
    exact h.switch_lt hN passage hp
  have hle := nodup_nat_lt_length hsimple hlt
  simpa only [List.length_map] using hle

/-- **A first revisit exists after `N+1` live passages.**  The returned
`before` trace is switch-simple, `repeated` is its very next passage, and
`old` is the unique earlier passage through that same switch. -/
theorem first_revisit_of_long_run {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish) :
    ∃ (before : List Passage) (old repeated : Passage)
        (after : List Passage) (middle : Nat × Tongues),
      PhysicalTrace w start before middle ∧
      PhysicalTrace w middle (repeated :: after) finish ∧
      SwitchSimple before ∧ old ∈ before ∧
      passageSwitch old = passageSwitch repeated := by
  obtain ⟨passages, hlen, htrace⟩ :=
    physicalTrace_of_stepN w hlive
  have hnsimple : ¬ SwitchSimple passages := by
    intro hsimple
    have hle := htrace.simple_length_le hN hsimple
    omega
  obtain ⟨before, repeated, after, hEq, hbefore, hrepeat⟩ :=
    first_revisit_split hnsimple
  subst passages
  obtain ⟨middle, hprefix, hsuffix⟩ := htrace.split_append
  obtain ⟨old, hold, hkey⟩ := List.mem_map.mp hrepeat
  exact ⟨before, old, repeated, after, middle,
    hprefix, hsuffix, hbefore, hold, hkey⟩

/-- A local groove remains a groove if only tongues at other switches have
changed. -/
theorem groove_transfer {u v : Tongues} {p x : Nat}
    (hgroove : arrive u x = (p, u))
    (hsame : v (x / 3) = u (x / 3)) :
    arrive v x = (p, v) := by
  by_cases hx : x % 3 = 0
  · unfold arrive at hgroove ⊢
    rw [if_pos hx] at hgroove ⊢
    injection hgroove with hp _
    rw [hsame, hp]
  · unfold arrive at hgroove ⊢
    rw [if_neg hx] at hgroove ⊢
    injection hgroove with hp hpin
    have hu : u (x / 3) = bval x := by
      have := congrFun hpin (x / 3)
      simpa [pin] using this.symm
    have hv : v (x / 3) = bval x := hsame.trans hu
    have hvpin : pin v x = v := pin_of_agrees hv
    rw [hp, hvpin]

/-- A groove is symmetric: if `x` routes back to `p` without changing the
tongue, then `p` routes forward to `x` without changing it either. -/
theorem groove_forward {u : Tongues} {p x : Nat}
    (hgroove : arrive u x = (p, u)) :
    arrive u p = (x, u) := by grind [arrive_back]

/-- The first arrival already installs its stable local groove. Repeating
that arrival from its post-vector has the same successor, so both runs agree
at every positive time, even after leaving the original route. -/
theorem stepN_after_arrival
    {w : Wiring} {p x d : Nat} {u v : Tongues}
    (harrive : arrive u p = (x, v)) (hpos : 0 < d) :
    stepN w d (p, u) = stepN w d (p, v) := by
  have hstable : arrive v p = (x, v) :=
    groove_forward (by simpa only [harrive] using arrive_back u p)
  cases d with
  | zero => omega
  | succ n => simp only [stepN, step, harrive, hstable]

/-- Along a switch-simple trace, every local groove made by the train is
still present at the end of the trace. -/
theorem PhysicalTrace.grooved_of_switchSimple {w : Wiring}
    {start finish : Nat × Tongues} {passages : List Passage}
    (h : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    PassagesGrooved finish.2 passages := by
  induction h with
  | nil =>
      intro passage hp
      cases hp
  | @cons p x q u v passages finish harrive hlink tail ih =>
      unfold SwitchSimple at hsimple
      simp only [List.map_cons] at hsimple
      rw [List.nodup_cons] at hsimple
      have htailSimple : SwitchSimple passages := hsimple.2
      have htailGrooved := ih htailSimple
      have hxsw : x / 3 = p / 3 := by
        have hexit := arrive_exit_switch u p
        rw [harrive] at hexit
        exact hexit
      have htailForeign :
          ∀ passage ∈ passages, passageSwitch passage ≠ p / 3 := by
        intro passage hp hEq
        apply hsimple.1
        apply List.mem_map.mpr
        exact ⟨passage, hp, hEq⟩
      have hpreserve : finish.2 (p / 3) = v (p / 3) :=
        tail.preserves (p / 3) htailForeign
      have hback : arrive v x = (p, v) := by
        have hb := arrive_back u p
        rw [harrive] at hb
        exact hb
      have hhead : arrive finish.2 x = (p, finish.2) := by
        apply groove_transfer hback
        rw [hxsw]
        exact hpreserve
      intro passage hp
      rcases List.mem_cons.mp hp with hheadEq | htailMem
      · simpa [hheadEq] using hhead
      · exact htailGrooved passage htailMem

/-- Traversing a grooved switch backwards and then its symmetric track edge
is one exact reverse step. -/
theorem step_grooved_back {w : Wiring} {u : Tongues} {p x ell : Nat}
    (hgroove : arrive u x = (p, u))
    (hentry : w.link ell = some p) :
    step w (x, u) = some (ell, u) := by
  have hback : w.link p = some ell := w.symm _ _ hentry
  simp [step, hgroove, hback]

/-- Follow a linked list of already-grooved passages in its recorded forward
direction.  The last plain-track edge may lead to any requested port `q`.
No tongue changes during the walk. -/
theorem run_grooved_passages
    (w : Wiring) (u : Tongues) (p x q : Nat) (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hfinal : w.link (lastPassageExit x rest) = some q) :
    stepN w ((p, x) :: rest).length (p, u) = some (q, u) := by
  induction rest generalizing p x with
  | nil =>
      have hg : arrive u x = (p, u) :=
        hgrooved (p, x) (by simp)
      have hfwd := groove_forward hg
      simpa [stepN, step, lastPassageExit, hfwd, hfinal]
  | cons passage rest ih =>
      rcases passage with ⟨r, y⟩
      have hxy : w.link x = some r := hlinked.1
      have hheadGroove : arrive u x = (p, u) :=
        hgrooved (p, x) (by simp)
      have hheadForward := groove_forward hheadGroove
      have hhead : stepN w 1 (p, u) = some (r, u) := by
        simp [stepN, step, hheadForward, hxy]
      have htailLinked : LinkedPassages w ((r, y) :: rest) := hlinked.2
      have htailGrooved : PassagesGrooved u ((r, y) :: rest) := by
        intro passage hp
        exact hgrooved passage (List.mem_cons_of_mem _ hp)
      have htailFinal : w.link (lastPassageExit y rest) = some q := by
        simpa [lastPassageExit] using hfinal
      have htail := ih r y htailLinked htailGrooved htailFinal
      have hlen : ((p, x) :: (r, y) :: rest).length =
          1 + ((r, y) :: rest).length := by
        simp only [List.length_cons]
        omega
      rw [hlen, stepN_add, hhead]
      exact htail

/-- Total version of the retrace engine.  The train walks a grooved path
backwards and then follows the plain-track edge at the path's original entry;
if that edge is absent, the result is exactly `none`. -/
theorem retrace_linked_passages_option
    (w : Wiring) (u : Tongues) (p x : Nat) (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest)) :
    stepN w ((p, x) :: rest).length
      (lastPassageExit x rest, u) =
        (w.link p).map (fun ell => (ell, u)) := by
  induction rest generalizing p x with
  | nil =>
      have hg : arrive u x = (p, u) :=
        hgrooved (p, x) (by simp)
      simp [stepN, step, lastPassageExit, hg]
  | cons passage rest ih =>
      rcases passage with ⟨q, y⟩
      have hxy : w.link x = some q := hlinked.1
      have hqx : w.link q = some x := w.symm _ _ hxy
      have htailLinked : LinkedPassages w ((q, y) :: rest) := hlinked.2
      have htailGrooved : PassagesGrooved u ((q, y) :: rest) := by
        intro passage hp
        exact hgrooved passage (List.mem_cons_of_mem _ hp)
      have htail := ih q y htailLinked htailGrooved
      rw [hqx] at htail
      have htail' :
          stepN w ((q, y) :: rest).length
            (lastPassageExit x ((q, y) :: rest), u) = some (x, u) := by
        simpa [lastPassageExit] using htail
      have hheadGroove : arrive u x = (p, u) :=
        hgrooved (p, x) (by simp)
      have hlen : ((p, x) :: (q, y) :: rest).length =
          ((q, y) :: rest).length + 1 := by simp
      rw [hlen, stepN_add, htail']
      simp [stepN, step, hheadGroove]

/-- **Crossed closure reverses the runway.**  A switch-simple prefix reaches
`p`, a simple excursion leaves by `x` and returns to the same switch at `q`,
and the next local passage exits through the old entry `p`.  The train then
walks the entire prefix backwards without another tongue change.  The final
plain-track edge is represented by the `Option.map`; it may be absent, in
which case the train falls off exactly there. -/
theorem PhysicalTrace.simple_cross_exit_retraces_prefix {w : Wiring}
    {start : Nat × Tongues} {runway loop : List Passage}
    {p x q : Nat} {u₀ u v : Tongues}
    (hprefix : PhysicalTrace w start runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: loop) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: loop))
    (hnext : arrive u q = (p, v)) :
    stepN w (runway.length + 1) (q, u) =
      (w.link start.1).map (fun ell => (ell, v)) := by
  have hfull := hprefix.append hexcursion
  have hfullGrooved := hfull.grooved_of_switchSimple hsimple
  have hqp : p / 3 = q / 3 := by
    have hs := arrive_exit_switch u q
    rw [hnext] at hs
    exact hs
  unfold SwitchSimple at hsimple
  simp only [List.map_append, List.map_cons] at hsimple
  have hparts := List.nodup_append.mp hsimple
  have hpNotPrefix : p / 3 ∉ runway.map passageSwitch := by
    intro hp
    have hne := hparts.2.2 (p / 3) hp
      (p / 3)
      (by simp [passageSwitch])
    apply hne
    rfl
  have hprefixGrooved : PassagesGrooved v runway := by
    intro passage hp
    have hold := hfullGrooved passage
      (List.mem_append_left _ hp)
    have hpassageNe : passageSwitch passage ≠ q / 3 := by
      intro hEq
      apply hpNotPrefix
      apply List.mem_map.mpr
      exact ⟨passage, hp, hEq.trans hqp.symm⟩
    have hexitSwitch : passage.2 / 3 = passageSwitch passage := by
      have hs := arrive_exit_switch u passage.2
      rw [hold] at hs
      exact hs.symm
    have hforeign : passage.2 / 3 ≠ q / 3 := by
      rw [hexitSwitch]
      exact hpassageNe
    exact groove_transfer hold (arrive_preserves_other hnext hforeign)
  cases runway with
  | nil =>
      cases hprefix
      simp [stepN, step, hnext]
  | cons passage rest =>
      rcases passage with ⟨a, b⟩
      have hlast : w.link (lastPassageExit b rest) = some p :=
        hprefix.last_link
      have hpback : w.link p = some (lastPassageExit b rest) :=
        w.symm _ _ hlast
      have hone : stepN w 1 (q, u) =
          some (lastPassageExit b rest, v) := by
        simp [stepN, step, hnext, hpback]
      have hback := retrace_linked_passages_option w v a b rest
        hprefix.linked hprefixGrooved
      have hstart : start.1 = a := by
        cases hprefix
        rfl
      have hlen : ((a, b) :: rest).length + 1 =
          1 + ((a, b) :: rest).length := by omega
      rw [hlen, stepN_add, hone]
      simp only [Option.bind_some]
      rw [hback, hstart]

theorem retrace_linked_passages
    (w : Wiring) (u : Tongues) (p x ell : Nat) (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hentry : w.link ell = some p) :
    stepN w ((p, x) :: rest).length
      (lastPassageExit x rest, u) = some (ell, u) := by
  induction rest generalizing p x ell with
  | nil =>
    have hg : arrive u x = (p, u) :=
      hgrooved (p, x) (by simp)
    have hs := step_grooved_back hg hentry
    simpa [stepN, lastPassageExit] using hs
  | cons passage rest ih =>
    rcases passage with ⟨q, y⟩
    have hxy : w.link x = some q := hlinked.1
    have htailLinked : LinkedPassages w ((q, y) :: rest) := hlinked.2
    have htailGrooved : PassagesGrooved u ((q, y) :: rest) := by
      intro passage hp
      exact hgrooved passage (List.mem_cons_of_mem _ hp)
    have htail := ih q y x htailLinked htailGrooved hxy
    have htail' :
        stepN w ((q, y) :: rest).length
          (lastPassageExit x ((q, y) :: rest), u) = some (x, u) := by
      simpa [lastPassageExit] using htail
    have hheadGroove : arrive u x = (p, u) :=
      hgrooved (p, x) (by simp)
    have hhead := step_grooved_back hheadGroove hentry
    have hlen : ((p, x) :: (q, y) :: rest).length =
        ((q, y) :: rest).length + 1 := by simp
    rw [hlen, stepN_add, htail']
    simpa [stepN] using hhead

end GeneralN
