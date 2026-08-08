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

/-- Add the incoming edge as a distinguished event before all passage edges.
Using `Option` keeps enough information to turn a first-repeat split back into
a split of the original passage list. -/
def edgeEvents (passages : List Passage) : List (Option Passage) :=
  none :: passages.map some

def edgeEventRep (w : Wiring) (entryEdge : Nat) :
    Option Passage → Nat
  | none => wireEdgeRep w entryEdge
  | some passage => passageEdgeRep w passage

private theorem map_some_injective {α : Type} :
    Function.Injective (List.map (fun x : α => some x)) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => cases h
  | cons x xs ih =>
      cases ys with
      | nil => cases h
      | cons y ys =>
          simp only [List.map_cons] at h
          injection h with hxy htail
          have hhead : x = y := Option.some.inj hxy
          subst y
          rw [ih htail]

private theorem exists_map_some_of_all_some {α : Type}
    (events : List (Option α))
    (h : ∀ event ∈ events, ∃ x, event = some x) :
    ∃ (xs : List α), events = xs.map (fun x => some x) := by
  induction events with
  | nil => exact ⟨[], rfl⟩
  | cons event events ih =>
      obtain ⟨x, hx⟩ := h event List.mem_cons_self
      obtain ⟨xs, hxs⟩ := ih (by
        intro later hlater
        exact h later (List.mem_cons_of_mem _ hlater))
      subst event
      subst events
      exact ⟨x :: xs, rfl⟩

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

/-- Boundary-aware first-repeat decomposition.  `repeated` is the first
passage whose outgoing physical edge was already crossed: either it repeats
the incoming edge, or it repeats one of `before`'s outgoing edges. -/
theorem first_edge_revisit_split_from
    {w : Wiring} {entryEdge : Nat} {passages : List Passage}
    (hnsimple : ¬ EdgeSimpleFrom w entryEdge passages) :
    ∃ before repeated after,
      passages = before ++ repeated :: after ∧
      EdgeSimpleFrom w entryEdge before ∧
      (passageEdgeRep w repeated = wireEdgeRep w entryEdge ∨
        passageEdgeRep w repeated ∈
          before.map (passageEdgeRep w)) := by
  have hnot : ¬ ((edgeEvents passages).map
      (edgeEventRep w entryEdge)).Nodup := by
    simpa [EdgeSimpleFrom, edgeEvents, edgeEventRep, List.map_map,
      Function.comp_def]
      using hnsimple
  rcases first_repeat_by (edgeEventRep w entryEdge)
      (edgeEvents passages) with hsimple | hrepeat
  · exact absurd hsimple hnot
  · obtain ⟨eventsBefore, repeatedEvent, eventsAfter,
        hEq, hbefore, hmem⟩ := hrepeat
    cases eventsBefore with
    | nil =>
        simp at hmem
    | cons first priorEvents =>
        unfold edgeEvents at hEq
        simp only [List.cons_append] at hEq
        injection hEq with hfirst htail
        subst first
        have hrepeatedMem :
            repeatedEvent ∈ passages.map (fun passage => some passage) := by
          rw [htail]
          exact List.mem_append_right _ List.mem_cons_self
        obtain ⟨repeated, _hrepeated, hrepeatedEq⟩ :=
          List.mem_map.mp hrepeatedMem
        have hrepeatedEq' : repeatedEvent = some repeated :=
          hrepeatedEq.symm
        subst repeatedEvent
        have hpriorAll : ∀ event ∈ priorEvents,
            ∃ passage, event = some passage := by
          intro event hevent
          have heventFull :
              event ∈ passages.map (fun passage => some passage) := by
            rw [htail]
            exact List.mem_append_left _ hevent
          obtain ⟨passage, _hpassage, hp⟩ :=
            List.mem_map.mp heventFull
          exact ⟨passage, hp.symm⟩
        obtain ⟨before, hprior⟩ :=
          exists_map_some_of_all_some priorEvents hpriorAll
        have hafterAll : ∀ event ∈ eventsAfter,
            ∃ passage, event = some passage := by
          intro event hevent
          have heventFull :
              event ∈ passages.map (fun passage => some passage) := by
            rw [htail]
            exact List.mem_append_right _
              (List.mem_cons_of_mem _ hevent)
          obtain ⟨passage, _hpassage, hp⟩ :=
            List.mem_map.mp heventFull
          exact ⟨passage, hp.symm⟩
        obtain ⟨after, hafter⟩ :=
          exists_map_some_of_all_some eventsAfter hafterAll
        subst priorEvents
        subst eventsAfter
        have hpassages : passages = before ++ repeated :: after := by
          apply map_some_injective
          simpa only [List.map_append, List.map_cons] using htail
        have hbefore' : EdgeSimpleFrom w entryEdge before := by
          unfold EdgeSimpleFrom
          simpa [edgeEventRep, List.map_map, Function.comp_def]
            using hbefore
        have hmem' :
            passageEdgeRep w repeated ∈
              wireEdgeRep w entryEdge ::
                before.map (passageEdgeRep w) := by
          simpa [edgeEventRep, List.map_map, Function.comp_def]
            using hmem
        exact ⟨before, repeated, after, hpassages, hbefore',
          List.mem_cons.mp hmem'⟩

/-- Equality of passage-edge names has exactly the two expected orientations:
the repeated passage exits through the old exit, or through its wire partner. -/
theorem passageEdgeRep_eq_iff (w : Wiring) (old repeated : Passage) :
    passageEdgeRep w old = passageEdgeRep w repeated ↔
      repeated.2 = old.2 ∨ repeated.2 = wireBar w old.2 := by
  exact wireEdgeRep_eq_iff w old.2 repeated.2

/-- Orientation split when the repeated edge is the incoming boundary edge. -/
theorem passageEdgeRep_eq_entry_iff
    (w : Wiring) (entryEdge : Nat) (repeated : Passage) :
    passageEdgeRep w repeated = wireEdgeRep w entryEdge ↔
      repeated.2 = entryEdge ∨
        repeated.2 = wireBar w entryEdge := by
  rw [eq_comm]
  exact wireEdgeRep_eq_iff w entryEdge repeated.2

/-- **First repeated physical edge, fully split.**  A live `3*N`-step run
from a known incoming edge reaches, after an edge-simple prefix, the first
passage whose outgoing edge is either the incoming edge or an earlier
passage edge. -/
theorem first_edge_revisit_from_long_run
    {w : Wiring} {N entryEdge : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hentry : w.link entryEdge = some start.1)
    (hlive : stepN w (3 * N) start = some finish) :
    ∃ (before : List Passage) (repeated : Passage)
        (after : List Passage) (middle : Nat × Tongues),
      PhysicalTrace w start before middle ∧
      PhysicalTrace w middle (repeated :: after) finish ∧
      EdgeSimpleFrom w entryEdge before ∧
      (passageEdgeRep w repeated = wireEdgeRep w entryEdge ∨
        passageEdgeRep w repeated ∈
          before.map (passageEdgeRep w)) := by
  obtain ⟨passages, _hlen, htrace, hrepeat⟩ :=
    physical_edge_repeats_of_long_run hN hentry hlive
  obtain ⟨before, repeated, after, hEq, hbefore, hkey⟩ :=
    first_edge_revisit_split_from hrepeat
  subst passages
  obtain ⟨middle, hprefix, hsuffix⟩ := htrace.split_append
  exact ⟨before, repeated, after, middle,
    hprefix, hsuffix, hbefore, hkey⟩

/-- **Observation 2 / Case 1.**  If the first repeated passage edge is crossed
in the same orientation as its earlier occurrence, the train is already
entering an absorbing tongue-stable simple cycle. -/
theorem same_oriented_first_edge_settles
    {w : Wiring} {entryEdge : Nat}
    {start middle finish : Nat × Tongues}
    {before after : List Passage} {old repeated : Passage}
    (hentry : w.link entryEdge = some start.1)
    (hbefore : PhysicalTrace w start before middle)
    (hsuffix : PhysicalTrace w middle (repeated :: after) finish)
    (hedges : EdgeSimpleFrom w entryEdge before)
    (hold : old ∈ before)
    (hsame : repeated.2 = old.2) :
    SettlesOnSimpleCycle w middle := by
  obtain ⟨runway, loop, hsplit⟩ := List.append_of_mem hold
  rcases old with ⟨p, x⟩
  rcases repeated with ⟨q, y⟩
  have hsame' : y = x := by simpa using hsame
  subst y
  subst before
  obtain ⟨atOld, hrunway, hexcursion⟩ := hbefore.split_append
  have hatOldPort : atOld.1 = p := hexcursion.head_arrive.1
  rcases atOld with ⟨atOldPort, oldTongues⟩
  simp only at hatOldPort
  subst atOldPort
  have hmiddlePort : middle.1 = q := hsuffix.head_arrive.1
  rcases middle with ⟨middlePort, middleTongues⟩
  simp only at hmiddlePort
  subst middlePort
  obtain ⟨nextTongues, hnext⟩ := hsuffix.head_arrive.2
  have hsimpleBefore :
      SwitchSimple (runway ++ (p, x) :: loop) :=
    hbefore.switchSimple_of_edgeSimpleFrom hentry hedges
  have hsimpleExcursion : SwitchSimple ((p, x) :: loop) := by
    unfold SwitchSimple at hsimpleBefore ⊢
    simp only [List.map_append] at hsimpleBefore
    exact (List.nodup_append.mp hsimpleBefore).2.1
  have hcycle := hexcursion.simple_same_exit_enters_period
    hsimpleExcursion hnext
  exact ⟨((q, x) :: loop).length, nextTongues,
    by simp, hcycle.1, hcycle.2⟩

/-- **Reverse-oriented first-edge case.**  When the first repeated passage
edge is crossed backwards, the part after its old occurrence is a simple
lollipop candy.  Closing that candy sends the train back over the entire
earlier runway, with no further tongue change. -/
theorem reverse_oriented_first_edge_retraces
    {w : Wiring} {entryEdge : Nat}
    {start middle finish : Nat × Tongues}
    {before after : List Passage} {old repeated : Passage}
    (hentry : w.link entryEdge = some start.1)
    (hbefore : PhysicalTrace w start before middle)
    (hsuffix : PhysicalTrace w middle (repeated :: after) finish)
    (hedges : EdgeSimpleFrom w entryEdge before)
    (hold : old ∈ before)
    (hreverse : repeated.2 = wireBar w old.2) :
    ∃ backSteps settled,
      backSteps ≤ before.length + 1 ∧
      stepN w backSteps middle =
        (w.link start.1).map (fun ell => (ell, settled)) := by
  obtain ⟨runway, loop, hsplit⟩ := List.append_of_mem hold
  rcases old with ⟨p, x⟩
  rcases repeated with ⟨q, y⟩
  subst before
  obtain ⟨atOld, hrunway, hexcursion⟩ := hbefore.split_append
  have hatOldPort : atOld.1 = p := hexcursion.head_arrive.1
  rcases atOld with ⟨atOldPort, oldTongues⟩
  simp only at hatOldPort
  subst atOldPort
  have hmiddlePort : middle.1 = q := hsuffix.head_arrive.1
  rcases middle with ⟨middlePort, middleTongues⟩
  simp only at hmiddlePort
  subst middlePort
  obtain ⟨nextTongues, hnext⟩ := hsuffix.head_arrive.2
  have hsimpleBefore :
      SwitchSimple (runway ++ (p, x) :: loop) :=
    hbefore.switchSimple_of_edgeSimpleFrom hentry hedges
  cases loop with
  | nil =>
      have hlast : w.link x = some q := by
        simpa [lastPassageExit] using hexcursion.last_link
      have hbar : wireBar w x = q := wireBar_of_link hlast
      have hy : y = q := hreverse.trans hbar
      have hne := arrive_exit_ne middleTongues q
      rw [hnext] at hne
      exact (hne hy).elim
  | cons passage rest =>
      rcases passage with ⟨r, z⟩
      cases hexcursion with
      | @cons _ _ next _ afterOld _ _ harriveOld hlinkOld hloopTrace =>
          have hnextPort : next = r := hloopTrace.head_arrive.1
          subst next
          have hbar : wireBar w x = r :=
            wireBar_of_link hlinkOld
          have hyr : y = r := hreverse.trans hbar
          subst y
          have hsingle :
              PhysicalTrace w (p, oldTongues) [(p, x)]
                (r, afterOld) :=
            PhysicalTrace.cons harriveOld hlinkOld
              (PhysicalTrace.nil (r, afterOld))
          have hprefix :
              PhysicalTrace w start (runway ++ [(p, x)])
                (r, afterOld) :=
            hrunway.append hsingle
          have hsimple :
              SwitchSimple
                ((runway ++ [(p, x)]) ++ (r, z) :: rest) := by
            simpa only [List.append_assoc, List.singleton_append]
              using hsimpleBefore
          have hback := hprefix.simple_cross_exit_retraces_prefix
            hloopTrace hsimple hnext
          refine ⟨(runway ++ [(p, x)]).length + 1,
            nextTongues, ?_, hback⟩
          simp

/-- Complete outcome when the first repeated edge is one of the prefix's
passage edges: same orientation is an absorbing cycle; reverse orientation
is an exact retrace to the far side of the starting edge. -/
theorem internal_first_edge_outcome
    {w : Wiring} {entryEdge : Nat}
    {start middle finish : Nat × Tongues}
    {before after : List Passage} {repeated : Passage}
    (hentry : w.link entryEdge = some start.1)
    (hbefore : PhysicalTrace w start before middle)
    (hsuffix : PhysicalTrace w middle (repeated :: after) finish)
    (hedges : EdgeSimpleFrom w entryEdge before)
    (hkey : passageEdgeRep w repeated ∈
      before.map (passageEdgeRep w)) :
    SettlesOnSimpleCycle w middle ∨
      ∃ backSteps settled,
        backSteps ≤ before.length + 1 ∧
        stepN w backSteps middle =
          (w.link start.1).map (fun ell => (ell, settled)) := by
  obtain ⟨old, hold, hedge⟩ := List.mem_map.mp hkey
  rcases (passageEdgeRep_eq_iff w old repeated).1 hedge with
      hsame | hreverse
  · exact Or.inl (same_oriented_first_edge_settles
      hentry hbefore hsuffix hedges hold hsame)
  · exact Or.inr (reverse_oriented_first_edge_retraces
      hentry hbefore hsuffix hedges hold hreverse)

/-- Repeating the incoming edge in its original orientation returns to the
original start port in one raw step. -/
theorem boundary_same_orientation_returns
    {w : Wiring} {entryEdge : Nat}
    {start middle finish : Nat × Tongues}
    {repeated : Passage} {after : List Passage}
    (hentry : w.link entryEdge = some start.1)
    (hsuffix : PhysicalTrace w middle (repeated :: after) finish)
    (hsame : repeated.2 = entryEdge) :
    ∃ settled,
      stepN w 1 middle = some (start.1, settled) := by
  rcases repeated with ⟨q, y⟩
  have hmiddlePort : middle.1 = q := hsuffix.head_arrive.1
  rcases middle with ⟨middlePort, middleTongues⟩
  simp only at hmiddlePort
  subst middlePort
  obtain ⟨settled, harrive⟩ := hsuffix.head_arrive.2
  have hy : y = entryEdge := by simpa using hsame
  subst y
  refine ⟨settled, ?_⟩
  simp [stepN, step, harrive, hentry]

/-- Repeating the incoming edge in reverse leaves through the far side of
the start in one raw step. -/
theorem boundary_reverse_orientation_exits
    {w : Wiring} {entryEdge : Nat}
    {start middle finish : Nat × Tongues}
    {repeated : Passage} {after : List Passage}
    (hentry : w.link entryEdge = some start.1)
    (hsuffix : PhysicalTrace w middle (repeated :: after) finish)
    (hreverse : repeated.2 = wireBar w entryEdge) :
    ∃ settled,
      stepN w 1 middle =
        (w.link start.1).map (fun ell => (ell, settled)) := by
  rcases repeated with ⟨q, y⟩
  have hmiddlePort : middle.1 = q := hsuffix.head_arrive.1
  rcases middle with ⟨middlePort, middleTongues⟩
  simp only at hmiddlePort
  subst middlePort
  obtain ⟨settled, harrive⟩ := hsuffix.head_arrive.2
  have hbar : wireBar w entryEdge = start.1 :=
    wireBar_of_link hentry
  have hreverse' : y = wireBar w entryEdge := by
    simpa using hreverse
  have hy : y = start.1 := hreverse'.trans hbar
  subst y
  refine ⟨settled, ?_⟩
  simp [stepN, step, harrive, hbar]

/-- **Complete first-edge outcome theorem.**  Within a linear prefix, the
first repeated physical edge has one of four exact raw-track outcomes:

* an absorbing simple cycle;
* a reverse closure that retraces to the far side of the start;
* a same-oriented repeat of the boundary edge, returning to the start port;
* a reverse repeat of the boundary edge, exiting past the start.

No topology, compiler, or finite-state enumeration is assumed. -/
theorem first_edge_outcome_of_long_run
    {w : Wiring} {N entryEdge : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hentry : w.link entryEdge = some start.1)
    (hlive : stepN w (3 * N) start = some finish) :
    ∃ (before : List Passage) (repeated : Passage)
        (after : List Passage) (middle : Nat × Tongues),
      PhysicalTrace w start before middle ∧
      PhysicalTrace w middle (repeated :: after) finish ∧
      before.length < 3 * N ∧
      (SettlesOnSimpleCycle w middle ∨
        (∃ backSteps settled,
          backSteps ≤ before.length + 1 ∧
          stepN w backSteps middle =
            (w.link start.1).map (fun ell => (ell, settled))) ∨
        (∃ settled,
          stepN w 1 middle = some (start.1, settled)) ∨
        (∃ settled,
          stepN w 1 middle =
            (w.link start.1).map (fun ell => (ell, settled)))) := by
  obtain ⟨before, repeated, after, middle,
      hbefore, hsuffix, hedges, hkey⟩ :=
    first_edge_revisit_from_long_run hN hentry hlive
  have hlength :=
    hbefore.edgeSimpleFrom_length_lt hN hentry hedges
  refine ⟨before, repeated, after, middle,
    hbefore, hsuffix, hlength, ?_⟩
  rcases hkey with hboundary | hinternal
  · rcases (passageEdgeRep_eq_entry_iff
      w entryEdge repeated).1 hboundary with hsame | hreverse
    · exact Or.inr (Or.inr (Or.inl
        (boundary_same_orientation_returns hentry hsuffix hsame)))
    · exact Or.inr (Or.inr (Or.inr
        (boundary_reverse_orientation_exits hentry hsuffix hreverse)))
  · rcases internal_first_edge_outcome
      hentry hbefore hsuffix hedges hinternal with hcycle | hretrace
    · exact Or.inl hcycle
    · exact Or.inr (Or.inl hretrace)

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
