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
  grind [arrive, branchPort]

/-- Every local passage uses the stem and exactly one branch. -/
theorem arrive_stem_endpoint (t : Tongues) (p : Nat) :
    p = 3 * (p / 3) ∨ (arrive t p).1 = 3 * (p / 3) := by
  grind [arrive, branchPort]

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
  · cases ht : t (p / 3) <;> simp [arrive, hp, branchPort, ht]
    all_goals refine ⟨by omega, pin_of_agrees ?_⟩; grind [bval]
  · simp [arrive, hp, pin, branchPort_bval hp]

/-- Decompose one successful physical step into its switch passage and its
plain-track edge. -/
theorem step_some_parts {w : Wiring} {c d : Nat × Tongues}
    (h : step w c = some d) :
    w.link (exitPort c) = some d.1 ∧ d.2 = arrivedTongues c := by
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨hq, rfl⟩

/-- Any successful successor time exposes the corresponding one-step raw
transition. -/
theorem live_successor_configs
    {w : Wiring} {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k+1) start).isSome) :
    ∃ cur next,
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next := by
  obtain ⟨next, hnext⟩ := Option.isSome_iff_exists.mp hlive
  have h := hnext
  rw [stepN_add] at h
  cases hcur : stepN w k start with
  | none => simp [hcur] at h
  | some cur => exact ⟨cur, next, rfl, hnext, by simpa [hcur, stepN] using h⟩

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

/-- A deterministic prefix fixes the starting configuration of its suffix. -/
theorem PhysicalTrace.after_prefix {w : Wiring}
    {start middle finish : Nat × Tongues} {before after : List Passage}
    (hfull : PhysicalTrace w start (before ++ after) finish)
    (hprefix : PhysicalTrace w start before middle) :
    PhysicalTrace w middle after finish := by
  obtain ⟨mid, hl, hr⟩ := hfull.split_append
  exact Option.some.inj (hl.sound.symm.trans hprefix.sound) ▸ hr

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
  induction rest generalizing p x start with
  | nil =>
      cases h with
      | cons _ hlink tail => cases tail; exact hlink
  | cons passage rest ih =>
      cases h with
      | cons _ _ tail => exact ih tail

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
  induction rest generalizing p x start with
  | nil =>
      obtain ⟨v, harrive⟩ := h.head_arrive.2
      have hs := arrive_exit_switch start.2 p
      simp [harrive, lastPassageExit, passageSwitch] at hs ⊢
      exact hs
  | cons passage rest ih =>
      cases h with
      | cons _ _ tail => exact List.mem_cons_of_mem _ (ih tail)

/-- A switch-simple nonempty trace cannot have its final exit port equal its
first entry port. -/
theorem PhysicalTrace.simple_last_exit_ne_first_entry {w : Wiring}
    {p x : Nat} {start finish : Nat × Tongues}
    {rest : List Passage}
    (h : PhysicalTrace w start ((p, x) :: rest) finish)
    (hsimple : SwitchSimple ((p, x) :: rest)) :
    lastPassageExit x rest ≠ p := by
  intro heq
  cases rest with
  | nil =>
      obtain ⟨v, harrive⟩ := h.head_arrive.2
      have hne : (arrive start.2 p).1 ≠ p := by grind [arrive, branchPort]
      exact hne (by simpa [harrive, lastPassageExit] using heq)
  | cons passage rest =>
      cases h with
      | cons _ _ tail =>
          have hm := tail.last_exit_switch_mem
          have hn : passageSwitch (p, x) ∉ (passage :: rest).map passageSwitch := by
            grind [SwitchSimple]
          apply hn
          simpa only [passageSwitch, lastPassageExit] using heq ▸ hm

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
      obtain ⟨middle, hs, ht⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨passages, hlen, htrace⟩ := ih ht
      have hp := step_some_parts hs
      refine ⟨(start.1, exitPort start) :: passages, by simp [hlen], ?_⟩
      have ha : arrive start.2 start.1 = (exitPort start, middle.2) := Prod.ext rfl hp.2.symm
      exact PhysicalTrace.cons ha hp.1 htrace

/-- A switch passage can modify only its own tongue. -/
theorem arrive_preserves_other {u v : Tongues} {p x j : Nat}
    (harrive : arrive u p = (x, v)) (hne : j ≠ p / 3) :
    v j = u j := by
  unfold arrive at harrive
  split at harrive <;> cases harrive <;> simp [pin, hne]

/-- A trace which never visits switch `j` preserves tongue `j`. -/
theorem PhysicalTrace.preserves {w : Wiring}
    {start finish : Nat × Tongues} {passages : List Passage}
    (h : PhysicalTrace w start passages finish) (j : Nat)
    (hforeign : ∀ passage ∈ passages, passageSwitch passage ≠ j) :
    finish.2 j = start.2 j := by
  induction h with
  | nil => rfl
  | @cons p x q u v passages finish harrive hlink tail ih =>
      exact (ih (fun passage hp => hforeign passage (List.mem_cons_of_mem _ hp))).trans
        (arrive_preserves_other harrive (hforeign (p, x) List.mem_cons_self).symm)

/-- Along a switch-simple trace, each intermediate tongue is either its
initial or final value: a switch cannot be visited in both halves of a split.
This needs neither a finite-wiring bound nor a productive-writer argument. -/
theorem PhysicalTrace.prefix_coordinate_eq_endpoint {w : Wiring}
    {start finish middle : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) {k : Nat}
    (hk : k ≤ passages.length) (hrun : stepN w k start = some middle)
    (j : Nat) : middle.2 j = start.2 j ∨ middle.2 j = finish.2 j := by
  induction htrace generalizing k with
  | nil =>
      have : k = 0 := by simpa using hk
      subst k
      cases hrun
      exact Or.inl rfl
  | @cons p x q u v passages finish harrive hlink tail ih =>
      cases k with
      | zero => cases hrun; exact Or.inl rfl
      | succ k =>
          have hr : stepN w k (q, v) = some middle := by
            simpa [stepN, step, harrive, hlink] using hrun
          rcases ih (List.nodup_cons.mp hsimple).2 (by simpa using hk) hr with hv | hf
          · by_cases hj : j = p / 3
            · exact Or.inr (hv.trans (tail.preserves j (by grind [SwitchSimple, passageSwitch])).symm)
            · exact Or.inl (hv.trans (arrive_preserves_other harrive hj))
          · exact Or.inr hf

/-- Every recorded passage exposes its local arrival and outgoing edge. -/
theorem PhysicalTrace.passage_step
    {w : Wiring} {start finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) :
    ∀ passage ∈ passages, ∃ u v q,
      arrive u passage.1 = (passage.2, v) ∧ w.link passage.2 = some q := by
  induction htrace with
  | nil => simp
  | @cons p x q u v passages finish harrive hlink tail ih =>
      intro passage hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨u, v, q, harrive, hlink⟩
      · exact ih passage hp

/-- Every switch in a live trace is one of the `N` switches named by a
finite-wiring bound. -/
theorem PhysicalTrace.switch_lt {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues} {passages : List Passage}
    (h : PhysicalTrace w start passages finish) :
    ∀ passage ∈ passages, passageSwitch passage < N := by
  intro passage hp
  obtain ⟨u, v, q, harrive, hlink⟩ := h.passage_step passage hp
  have hbound := (hN _ _ hlink).1
  have hsame := arrive_exit_switch u passage.1
  rw [harrive] at hsame
  unfold passageSwitch
  omega

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
  have extend : ∀ rest before : List α, (before.map key).Nodup →
      ((before ++ rest).map key).Nodup ∨ ∃ pre repeated after,
        before ++ rest = pre ++ repeated :: after ∧
        (pre.map key).Nodup ∧ key repeated ∈ pre.map key := by
    intro rest
    induction rest with
    | nil => intro before hnd; exact Or.inl (by simpa using hnd)
    | cons x rest ih =>
        intro before hnd
        by_cases hx : key x ∈ before.map key
        · exact Or.inr ⟨before, x, rest, rfl, hnd, hx⟩
        · simpa only [List.append_assoc, List.singleton_append] using
            ih (before ++ [x]) (by grind)
  simpa using extend xs [] (by simp)

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
    (first_repeat_by passageSwitch passages).resolve_left hnsimple
  subst passages
  obtain ⟨middle, hprefix, hsuffix⟩ := htrace.split_append
  obtain ⟨old, hold, hkey⟩ := List.mem_map.mp hrepeat
  exact ⟨before, old, repeated, after, middle,
    hprefix, hsuffix, hbefore, hold, hkey⟩

/-- Two states which groove the same passage agree on its tongue. -/
theorem grooved_states_agree_on_passage {u v : Tongues} {p x : Nat}
    (hu : arrive u x = (p, u)) (hv : arrive v x = (p, v)) :
    u (x / 3) = v (x / 3) := by
  by_cases hx : x % 3 = 0
  · grind [arrive, branchPort]
  · have hu' := congrArg (fun r : Nat × Tongues => r.2 (x / 3)) hu
    have hv' := congrArg (fun r : Nat × Tongues => r.2 (x / 3)) hv
    simp [arrive, hx, pin] at hu' hv'
    exact hu'.symm.trans hv'

/-- A local groove remains a groove if only tongues at other switches have
changed. -/
theorem groove_transfer {u v : Tongues} {p x : Nat}
    (hgroove : arrive u x = (p, u))
    (hsame : v (x / 3) = u (x / 3)) :
    arrive v x = (p, v) := by
  have hport := congrArg Prod.fst hgroove
  have hbit := congrArg (fun r => r.2 (x / 3)) hgroove
  by_cases hx : x % 3 = 0
  · simpa [arrive, hx, hsame] using hport
  · have hv : v (x / 3) = bval x := by
      simpa [arrive, hx, pin, ← hsame] using hbit.symm
    simpa [arrive, hx, pin_of_agrees hv] using hport

/-- Preserve path grooves by preserving the tongue at each recorded switch. -/
theorem PassagesGrooved.transfer {u v : Tongues} {path : List Passage}
    (hg : PassagesGrooved u path)
    (heq : ∀ passage ∈ path, v (passageSwitch passage) = u (passageSwitch passage)) :
    PassagesGrooved v path := by
  intro passage hp
  have hs := arrive_exit_switch u passage.2
  rw [hg passage hp] at hs
  apply groove_transfer (hg passage hp)
  simpa only [← hs, passageSwitch] using heq passage hp

/-- A groove is symmetric: if `x` routes back to `p` without changing the
tongue, then `p` routes forward to `x` without changing it either. -/
theorem groove_forward {u : Tongues} {p x : Nat}
    (hgroove : arrive u x = (p, u)) :
    arrive u p = (x, u) := by grind [arrive_back]

theorem physicalTrace_grooved_passages
    (w : Wiring) (u : Tongues) (p x q : Nat)
    (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hfinal : w.link (lastPassageExit x rest) = some q) :
    PhysicalTrace w (p, u) ((p, x) :: rest) (q, u) := by
  induction rest generalizing p x with
  | nil =>
      exact PhysicalTrace.cons (groove_forward (hgrooved (p, x) List.mem_cons_self))
        hfinal (PhysicalTrace.nil _)
  | cons a rest ih =>
      exact PhysicalTrace.cons (groove_forward (hgrooved (p, x) List.mem_cons_self))
        hlinked.1 (ih a.1 a.2 hlinked.2
          (fun passage hp => hgrooved passage (List.mem_cons_of_mem _ hp)) hfinal)

/-- Replay any recorded physical trace in a state that grooves all of its
passages.  The replay changes no tongue. -/
theorem PhysicalTrace.replay_grooved
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (state : Tongues)
    (hgrooved : PassagesGrooved state passages) :
    PhysicalTrace w (start.1, state) passages (finish.1, state) := by
  obtain ⟨v, hr, rfl, _⟩ := htrace.replay_preserving (fun u => u = state)
    (by intro passage hp u hu; subst u; exact ⟨state, groove_forward (hgrooved passage hp), rfl⟩) rfl
  exact hr

/-- Split and rebase a trace at a named passage in one step. This works for
empty prefixes and suffixes and requires no switch simplicity. -/
theorem PhysicalTrace.split_grooved_at
    {w : Wiring} {start finish : Nat × Tongues} {before after : List Passage}
    {p x : Nat} {state : Tongues}
    (htrace : PhysicalTrace w start (before ++ (p, x) :: after) finish)
    (hgrooved : PassagesGrooved state (before ++ (p, x) :: after)) :
    ∃ outside, w.link x = some outside ∧
      PhysicalTrace w (start.1, state) before (p, state) ∧
      PhysicalTrace w (outside, state) after (finish.1, state) := by
  obtain ⟨middle, hleft, hright⟩ := htrace.split_append
  cases hright with
  | @cons _ _ outside _ _ _ _ _ hlink tail =>
      exact ⟨outside, hlink,
        hleft.replay_grooved state (fun passage hp => hgrooved passage (by simp [hp])),
        tail.replay_grooved state (fun passage hp => hgrooved passage (by simp [hp]))⟩

/-- Passage list for traversing a stored path in the opposite direction. -/
def reversePassages (passages : List Passage) : List Passage :=
  passages.reverse.map Prod.swap

theorem reversePassages_length (passages : List Passage) :
    (reversePassages passages).length = passages.length := by simp [reversePassages]

theorem reversePassage_mem {passage : Passage}
    {passages : List Passage} (hmem : passage ∈ passages) :
    (passage.2, passage.1) ∈ reversePassages passages :=
  List.mem_map.mpr ⟨passage, List.mem_reverse.mpr hmem, rfl⟩

theorem reversePassages_grooved {state : Tongues} {passages : List Passage}
    (hgrooved : PassagesGrooved state passages) :
    PassagesGrooved state (reversePassages passages) := by
  intro passage hp
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
  exact groove_forward (hgrooved old (List.mem_reverse.mp hold))

/-- Reverse any grooved recorded route between its two boundary edges. -/
theorem PhysicalTrace.reverse_grooved
    {w : Wiring} {start finish : Nat × Tongues} {route : List Passage}
    {entry outside : Nat} {state : Tongues}
    (htrace : PhysicalTrace w start route finish)
    (hgrooved : PassagesGrooved state route)
    (hentry : w.link entry = some start.1)
    (hexit : w.link finish.1 = some outside) :
    PhysicalTrace w (outside, state) (reversePassages route) (entry, state) := by
  induction htrace generalizing entry with
  | nil c =>
      have heq : outside = entry := Option.some.inj (hexit.symm.trans (w.symm _ _ hentry))
      subst outside
      exact PhysicalTrace.nil _
  | @cons p x q u v route finish _ hlink tail ih =>
      have hback := ih (fun passage hp => hgrooved passage (List.mem_cons_of_mem _ hp)) hlink hexit
      have hhead := PhysicalTrace.cons (hgrooved (p, x) List.mem_cons_self)
        (w.symm _ _ hentry) (PhysicalTrace.nil _)
      simpa [reversePassages] using hback.append hhead

/-- A fresh local passage that exits through the entry of a recorded prefix
immediately traverses that prefix backwards and leaves over its incoming
boundary edge. -/
theorem physicalTrace_contact_retraces_prefix
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v)) :
    PhysicalTrace w (p, u)
      ((p, oldEntry) :: reversePassages recorded) (e, v) := by
  cases recorded with
  | nil =>
      cases hrecorded
      exact PhysicalTrace.cons hcontact (w.symm _ _ hentry) (PhysicalTrace.nil _)
  | cons passage rest =>
      have hlink := w.symm _ _ hrecorded.last_link
      exact PhysicalTrace.cons hcontact hlink (hrecorded.reverse_grooved hgrooved hentry hlink)

/-- Every prefix of a grooved physical trace runs with the specified tongue
vector.  The endpoint port is intentionally existential: novelty accounting
cares about the complete tongue vector, not the particular plain-track edge.
-/
theorem PhysicalTrace.grooved_prefix_tongues
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (state : Tongues)
    (hgrooved : PassagesGrooved state passages)
    {d : Nat} (hd : d ≤ passages.length) :
    ∃ port, stepN w d (start.1, state) = some (port, state) := by
  obtain ⟨_, _, _, hcover⟩ := htrace.replay_preserving (fun u => u = state)
    (by intro passage hp u hu; subst u; exact ⟨state, groove_forward (hgrooved passage hp), rfl⟩) rfl
  obtain ⟨port, _, hr, rfl⟩ := hcover d hd
  exact ⟨port, hr⟩

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
  | nil => simp [PassagesGrooved]
  | @cons p x q u v passages finish harrive hlink tail ih =>
      have htail : SwitchSimple passages := by grind [SwitchSimple]
      have hforeign : ∀ passage ∈ passages, passageSwitch passage ≠ p / 3 := by
        grind [SwitchSimple, passageSwitch]
      have hx : x / 3 = p / 3 := by simpa [harrive] using arrive_exit_switch u p
      have hback : arrive v x = (p, v) := by simpa [harrive] using arrive_back u p
      have hhead : arrive finish.2 x = (p, finish.2) :=
        groove_transfer hback (by rw [hx]; exact tail.preserves _ hforeign)
      intro passage hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hhead
      · exact ih htail passage hp

end GeneralN
