import TrackTrace
import ConcreteCascadeFacts

/-!
# First repeated physical track edge

This is the direct Chalcraft--Greene/Aaronson normal form.  A train step
crosses one lazy point and then one plain-track edge.  Because `Wiring.link`
is a symmetric partial matching, the smaller endpoint canonically names that
undirected edge.  Before an edge repeats, those names are pairwise distinct;
in an `N`-switch wiring there are fewer than `3*N` possible names.

The lemmas here are deliberately stated over raw `Wiring`/`stepN`.  They do
not use the echo abstraction, a finite-`N` computation, or a planarity
assumption.
-/

namespace GeneralN

/-- Canonical name of the undirected physical edge incident to `p`. -/
def wireEdgeRep (w : Wiring) (p : Nat) : Nat :=
  min p (wireBar w p)

/-- The plain-track edge crossed immediately after a recorded passage. -/
def passageEdgeRep (w : Wiring) (passage : Passage) : Nat :=
  wireEdgeRep w passage.2

/-- A passage trace has not yet reused a physical track edge. -/
def EdgeSimple (w : Wiring) (passages : List Passage) : Prop :=
  (passages.map (passageEdgeRep w)).Nodup

/-- Edge simplicity including the plain-track edge on which the train starts.
This removes the exceptional start vertex from the first-repeated-edge
argument. -/
def EdgeSimpleFrom (w : Wiring) (entryEdge : Nat)
    (passages : List Passage) : Prop :=
  (wireEdgeRep w entryEdge :: passages.map (passageEdgeRep w)).Nodup

/-- Equality of canonical names means equality of undirected wiring edges.
The second endpoint is either the same oriented exit or its wire partner. -/
theorem wireEdgeRep_eq_iff (w : Wiring) (p q : Nat) :
    wireEdgeRep w p = wireEdgeRep w q ↔
      q = p ∨ q = wireBar w p := by
  constructor
  · intro h
    have hinj : Function.Injective (wireBar w) := by
      intro a b hab
      have hbar := congrArg (wireBar w) hab
      simpa only [wireBar_invol] using hbar
    unfold wireEdgeRep at h
    by_cases hp : p ≤ wireBar w p
    · rw [Nat.min_eq_left hp] at h
      by_cases hq : q ≤ wireBar w q
      · rw [Nat.min_eq_left hq] at h
        exact Or.inl h.symm
      · have hq' : wireBar w q ≤ q := Nat.le_of_not_ge hq
        rw [Nat.min_eq_right hq'] at h
        right
        have hbar := congrArg (wireBar w) h
        rw [wireBar_invol] at hbar
        exact hbar.symm
    · have hp' : wireBar w p ≤ p := Nat.le_of_not_ge hp
      rw [Nat.min_eq_right hp'] at h
      by_cases hq : q ≤ wireBar w q
      · rw [Nat.min_eq_left hq] at h
        exact Or.inr h.symm
      · have hq' : wireBar w q ≤ q := Nat.le_of_not_ge hq
        rw [Nat.min_eq_right hq'] at h
        exact Or.inl (hinj h).symm
  · intro h
    rcases h with rfl | h
    · rfl
    · subst q
      unfold wireEdgeRep
      rw [wireBar_invol, Nat.min_comm]

/-- The two endpoints of a linked physical edge have the same canonical
edge name. -/
theorem wireEdgeRep_eq_of_link {w : Wiring} {p q : Nat}
    (hlink : w.link p = some q) :
    wireEdgeRep w p = wireEdgeRep w q := by
  apply (wireEdgeRep_eq_iff w p q).2
  right
  exact (wireBar_of_link hlink).symm

/-- The final exit of a nonempty passage list is one of that list's recorded
exit ports. -/
theorem lastPassageExit_mem_exits (p x : Nat) (rest : List Passage) :
    lastPassageExit x rest ∈ ((p, x) :: rest).map Prod.snd := by
  induction rest generalizing p x with
  | nil => simp [lastPassageExit]
  | cons passage rest ih =>
      rcases passage with ⟨q, y⟩
      simp only [lastPassageExit, List.map_cons, List.mem_cons]
      apply Or.inr
      simpa only [List.map_cons, List.mem_cons] using ih q y

/-- If the tail is nonempty, the final exit lies among the tail's exits. -/
theorem lastPassageExit_mem_tail_exits
    (_p x q y : Nat) (rest : List Passage) :
    lastPassageExit x ((q, y) :: rest) ∈
      (((q, y) :: rest).map Prod.snd) := by
  simpa only [lastPassageExit] using
    lastPassageExit_mem_exits q y rest

/-- The canonical edge name of the final exit occurs in the passage-edge
name list. -/
theorem lastPassageExit_key_mem (w : Wiring)
    (p x : Nat) (rest : List Passage) :
    wireEdgeRep w (lastPassageExit x rest) ∈
      ((p, x) :: rest).map (passageEdgeRep w) := by
  obtain ⟨passage, hpassage, hexit⟩ := List.mem_map.mp
    (lastPassageExit_mem_exits p x rest)
  apply List.mem_map.mpr
  refine ⟨passage, hpassage, ?_⟩
  unfold passageEdgeRep
  rw [hexit]

/-- Nonempty-tail version of `lastPassageExit_key_mem`. -/
theorem lastPassageExit_key_mem_tail (w : Wiring)
    (p x q y : Nat) (rest : List Passage) :
    wireEdgeRep w (lastPassageExit x ((q, y) :: rest)) ∈
      (((q, y) :: rest).map (passageEdgeRep w)) := by
  obtain ⟨passage, hpassage, hexit⟩ := List.mem_map.mp
    (lastPassageExit_mem_tail_exits p x q y rest)
  apply List.mem_map.mpr
  refine ⟨passage, hpassage, ?_⟩
  unfold passageEdgeRep
  rw [hexit]

/-- **Observation 1, boundary-aware local form.**  While the initial edge and
all subsequently crossed physical edges are distinct, the first switch cannot
occur again later in the trace. -/
theorem PhysicalTrace.head_switch_not_mem_of_edgeSimpleFrom
    {w : Wiring} {e p x : Nat} {u : Tongues}
    {rest : List Passage} {finish : Nat × Tongues}
    (hentry : w.link e = some p)
    (htrace : PhysicalTrace w (p, u) ((p, x) :: rest) finish)
    (hedges : EdgeSimpleFrom w e ((p, x) :: rest)) :
    passageSwitch (p, x) ∉ rest.map passageSwitch := by
  intro hmem
  obtain ⟨target, htarget, hkey⟩ := List.mem_map.mp hmem
  rcases target with ⟨q, y⟩
  have hsw : p / 3 = q / 3 := by
    simpa [passageSwitch] using hkey.symm
  obtain ⟨before, after, hsplit⟩ := List.append_of_mem htarget
  subst rest
  cases htrace with
  | @cons _ _ next _ v _ _ harrive hlink tail =>
      obtain ⟨middle, hbefore, htargetTrace⟩ := tail.split_append
      have hmiddlePort : middle.1 = q := htargetTrace.head_arrive.1
      rcases middle with ⟨middlePort, middleTongues⟩
      simp only at hmiddlePort
      subst middlePort
      obtain ⟨targetTongues, htargetArrive⟩ :=
        htargetTrace.head_arrive.2
      have hshare := same_switch_passages_share_port
        u middleTongues p q hsw
      rw [harrive, htargetArrive] at hshare
      unfold EdgeSimpleFrom at hedges
      simp only [List.map_cons] at hedges
      have heNot := (List.nodup_cons.mp hedges).1
      have hxNodup := (List.nodup_cons.mp hedges).2
      have hxNot := (List.nodup_cons.mp hxNodup).1
      have htargetKey :
          passageEdgeRep w (q, y) ∈
            (before ++ (q, y) :: after).map (passageEdgeRep w) := by
        apply List.mem_map.mpr
        exact ⟨(q, y), by simp, rfl⟩
      change wireEdgeRep w e ∉
        wireEdgeRep w x ::
          (before ++ (q, y) :: after).map (passageEdgeRep w) at heNot
      change wireEdgeRep w x ∉
        (before ++ (q, y) :: after).map (passageEdgeRep w) at hxNot
      change wireEdgeRep w y ∈
        (before ++ (q, y) :: after).map (passageEdgeRep w) at htargetKey
      rcases hshare with hpq | hpy | hxq | hxy
      · subst q
        have hprefix :
            PhysicalTrace w (p, u) ((p, x) :: before)
              (p, middleTongues) :=
          PhysicalTrace.cons harrive hlink hbefore
        have hlast := hprefix.last_link
        have hlastEq : lastPassageExit x before = e :=
          Wiring.link_injective hlast hentry
        have hprefixKey := lastPassageExit_key_mem w p x before
        have hfullKey :
            wireEdgeRep w (lastPassageExit x before) ∈
              ((p, x) :: before ++ (p, y) :: after).map
                (passageEdgeRep w) := by
          rw [show ((p, x) :: before ++ (p, y) :: after) =
              ((p, x) :: before) ++ (p, y) :: after by simp,
            List.map_append]
          exact List.mem_append_left _ hprefixKey
        apply heNot
        rw [← hlastEq]
        exact hfullKey
      · have hpy' : p = y := by simpa using hpy
        subst y
        apply heNot
        have hEq := wireEdgeRep_eq_of_link hentry
        rw [hEq]
        exact List.mem_cons_of_mem _ htargetKey
      · subst q
        cases before with
        | nil =>
            cases hbefore
            have hback := arrive_back u p
            rw [harrive] at hback
            have hy : y = p := by
              rw [hback] at htargetArrive
              have hy' := congrArg Prod.fst htargetArrive
              simpa using hy'.symm
            subst y
            apply heNot
            have hEq := wireEdgeRep_eq_of_link hentry
            rw [hEq]
            exact List.mem_cons_of_mem _ htargetKey
        | cons passage before =>
            rcases passage with ⟨a, b⟩
            have hprefix :
                PhysicalTrace w (p, u)
                  ((p, x) :: (a, b) :: before) (x, middleTongues) :=
              PhysicalTrace.cons harrive hlink hbefore
            have hlast := hprefix.last_link
            have hbackLink : w.link next = some x :=
              w.symm _ _ hlink
            have hlastEq :
                lastPassageExit x ((a, b) :: before) = next :=
              Wiring.link_injective hlast hbackLink
            have hprefixKey :=
              lastPassageExit_key_mem_tail w p x a b before
            have htailKey :
                wireEdgeRep w (lastPassageExit x ((a, b) :: before)) ∈
                  (((a, b) :: before ++ (x, y) :: after).map
                    (passageEdgeRep w)) := by
              rw [show ((a, b) :: before ++ (x, y) :: after) =
                  ((a, b) :: before) ++ (x, y) :: after by simp,
                List.map_append]
              exact List.mem_append_left _ hprefixKey
            apply hxNot
            have hEdge : wireEdgeRep w x = wireEdgeRep w next :=
              wireEdgeRep_eq_of_link hlink
            rw [hEdge, ← hlastEq]
            exact htailKey
      · have hxy' : x = y := by simpa using hxy
        subst y
        apply hxNot
        exact htargetKey

/-- **Observation 1.**  If the starting edge and every crossed edge are
pairwise distinct, then the whole physical trace is switch-simple. -/
theorem PhysicalTrace.switchSimple_of_edgeSimpleFrom
    {w : Wiring} {e : Nat} {start finish : Nat × Tongues}
    {passages : List Passage}
    (hentry : w.link e = some start.1)
    (htrace : PhysicalTrace w start passages finish)
    (hedges : EdgeSimpleFrom w e passages) :
    SwitchSimple passages := by
  induction htrace generalizing e with
  | nil =>
      simp [SwitchSimple]
  | @cons p x q u v passages finish harrive hlink tail ih =>
      unfold SwitchSimple
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · exact (PhysicalTrace.cons harrive hlink tail)
          |>.head_switch_not_mem_of_edgeSimpleFrom hentry hedges
      · apply ih hlink
        unfold EdgeSimpleFrom at hedges ⊢
        simp only [List.map_cons] at hedges ⊢
        exact (List.nodup_cons.mp hedges).2

/-- Every physical edge crossed by a live trace has a representative below
`3*N`. -/
theorem PhysicalTrace.edgeRep_lt
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues} {passages : List Passage}
    (h : PhysicalTrace w start passages finish) :
    ∀ passage ∈ passages, passageEdgeRep w passage < 3 * N := by
  induction h with
  | nil =>
      intro passage hp
      cases hp
  | @cons p x q u v passages finish harrive hlink tail ih =>
      intro passage hp
      rcases List.mem_cons.mp hp with hhead | htail
      · subst passage
        unfold passageEdgeRep wireEdgeRep
        rw [wireBar_of_link hlink]
        exact Nat.lt_of_le_of_lt (Nat.min_le_left x q) (hN x q hlink).1
      · exact ih passage htail

/-- The representative of a known incoming edge also lies below the port
bound. -/
theorem entryEdgeRep_lt
    {w : Wiring} {N e p : Nat}
    (hN : ∀ a b, w.link a = some b → a < 3 * N ∧ b < 3 * N)
    (hentry : w.link e = some p) :
    wireEdgeRep w e < 3 * N := by
  unfold wireEdgeRep
  exact Nat.lt_of_le_of_lt (Nat.min_le_left e (wireBar w e))
    (hN e p hentry).1

/-- A boundary-aware edge-simple live trace has strictly fewer than `3*N`
passages: its incoming edge consumes one of the available canonical edge
names. -/
theorem PhysicalTrace.edgeSimpleFrom_length_lt
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues} {passages : List Passage}
    (hentry : w.link e = some start.1)
    (h : PhysicalTrace w start passages finish)
    (hsimple : EdgeSimpleFrom w e passages) :
    passages.length < 3 * N := by
  unfold EdgeSimpleFrom at hsimple
  have hlt : ∀ key ∈
      wireEdgeRep w e :: passages.map (passageEdgeRep w),
      key < 3 * N := by
    intro key hkey
    rcases List.mem_cons.mp hkey with hhead | htail
    · subst key
      exact entryEdgeRep_lt hN hentry
    · obtain ⟨passage, hp, rfl⟩ := List.mem_map.mp htail
      exact h.edgeRep_lt hN passage hp
  have hle := nodup_nat_lt_length hsimple hlt
  simp only [List.length_cons, List.length_map] at hle
  omega

/-- **Linear first-edge cutoff.**  If `3*N` steps remain live, the initial
edge together with the crossed edges cannot all be distinct.  This is the
quantitative entry point of the Chalcraft--Greene/Aaronson classification. -/
theorem physical_edge_repeats_of_long_run
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (hlive : stepN w (3 * N) start = some finish) :
    ∃ passages,
      passages.length = 3 * N ∧
      PhysicalTrace w start passages finish ∧
      ¬ EdgeSimpleFrom w e passages := by
  obtain ⟨passages, hlen, htrace⟩ :=
    physicalTrace_of_stepN w hlive
  refine ⟨passages, hlen, htrace, ?_⟩
  intro hsimple
  have hlt := htrace.edgeSimpleFrom_length_lt hN hentry hsimple
  omega

/-- An edge-simple live trace has at most `3*N` passages.  This deliberately
uses the easy port bound rather than spending proof complexity on the sharper
matching bound `3*N/2`. -/
theorem PhysicalTrace.edgeSimple_length_le
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues} {passages : List Passage}
    (h : PhysicalTrace w start passages finish)
    (hsimple : EdgeSimple w passages) :
    passages.length ≤ 3 * N := by
  unfold EdgeSimple at hsimple
  have hlt : ∀ x ∈ passages.map (passageEdgeRep w), x < 3 * N := by
    intro x hx
    obtain ⟨passage, hp, rfl⟩ := List.mem_map.mp hx
    exact h.edgeRep_lt hN passage hp
  have hle := nodup_nat_lt_length hsimple hlt
  simpa only [List.length_map] using hle

/-- Split a nonsimple edge trace at its first repeated physical edge. -/
theorem first_edge_revisit_split {w : Wiring} {passages : List Passage}
    (hnsimple : ¬ EdgeSimple w passages) :
    ∃ before repeated after,
      passages = before ++ repeated :: after ∧
      EdgeSimple w before ∧
      passageEdgeRep w repeated ∈ before.map (passageEdgeRep w) := by
  unfold EdgeSimple at hnsimple
  rcases first_repeat_by (passageEdgeRep w) passages with
      hsimple | hrepeat
  · exact absurd hsimple hnsimple
  · exact hrepeat

/-- **First repeated-track theorem.**  Any live `3*N+1`-step run in an
`N`-switch wiring contains a first repeated undirected physical edge.  The
prefix before the repeated crossing is edge-simple, and `old` records an
earlier crossing of exactly that edge. -/
theorem first_edge_revisit_of_long_run
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (3 * N + 1) start = some finish) :
    ∃ (before : List Passage) (old repeated : Passage)
        (after : List Passage) (middle : Nat × Tongues),
      PhysicalTrace w start before middle ∧
      PhysicalTrace w middle (repeated :: after) finish ∧
      EdgeSimple w before ∧ old ∈ before ∧
      passageEdgeRep w old = passageEdgeRep w repeated := by
  obtain ⟨passages, hlen, htrace⟩ :=
    physicalTrace_of_stepN w hlive
  have hnsimple : ¬ EdgeSimple w passages := by
    intro hsimple
    have hle := htrace.edgeSimple_length_le hN hsimple
    omega
  obtain ⟨before, repeated, after, hEq, hbefore, hrepeat⟩ :=
    first_edge_revisit_split hnsimple
  subst passages
  obtain ⟨middle, hprefix, hsuffix⟩ := htrace.split_append
  obtain ⟨old, hold, hkey⟩ := List.mem_map.mp hrepeat
  exact ⟨before, old, repeated, after, middle,
    hprefix, hsuffix, hbefore, hold, hkey⟩

end GeneralN
