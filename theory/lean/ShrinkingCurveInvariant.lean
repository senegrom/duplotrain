import KoizumiCurveInvariant
import SelfEpochAmortization
import SharpCertificateClosure

/-!
# The combinatorial shrinking-curve invariant

This module isolates the list-theoretic core of Jun Koizumi's shrinking
empty-curve argument directly over `Passage`, `PhysicalTrace`, and `stepN`.

After a turnaround, let `oldExploration` be the switch-simple old curve and
let `newPrefix` be the fresh switch-simple prefix followed by the train.  At
the first passage whose switch belongs to the union of those two lists there
are exactly two useful cases.

* If the switch already occurs in `newPrefix`, the extended physical trace is
  nonsimple.  The existing exact first-revisit theorem therefore produces a
  simple cycle or a manufactured reflector.
* If the switch occurs in `oldExploration`, its ordered occurrence splits the
  old curve into two strict tracked subcurves.  Keeping both sides makes the
  statement independent of the orientation chosen for the next open curve.

The final section records the exact consequence once repeated strict nesting
has reached a permanent self-only tail: at most two switches can be
recurrently productive, and at most four visible vectors occur after the
tail starts.  This file deliberately does *not* assert that every raw run has
already reached such a tail; extracting that tail from successive first
contacts is the remaining global step.
-/

namespace GeneralN

/-! ## Earliest contact with the old exploration or the fresh prefix -/

/-- Concrete data saying that `contact` is the first post-turnaround passage
whose switch has already been seen.  `newPrefix` itself is switch-simple and
disjoint from `oldExploration`; thus all earlier passages are genuinely fresh.
The old exploration is range-certified so either residual side can be turned
into a `TrackedEndpointCurve`. -/
structure FirstPostTurnaroundContact (N : Nat)
    (oldExploration newPrefix : List Passage) (contact : Passage) : Prop where
  oldSimple : SwitchSimple oldExploration
  newSimple : SwitchSimple newPrefix
  oldInRange : forall passage, passage ∈ oldExploration ->
    passageSwitch passage < N
  prefixFresh : forall fresh, fresh ∈ newPrefix ->
    passageSwitch fresh ∉ oldExploration.map passageSwitch
  contactSeen : passageSwitch contact ∈
    (oldExploration ++ newPrefix).map passageSwitch

/-- Proof-relevant strict nesting data produced by contact with the old
exploration.  Both residual orientations are retained. -/
structure StrictOldExplorationNest (N : Nat)
    (oldExploration : List Passage) (contact : Passage) : Type where
  hit : Passage
  before after : List Passage
  outer left right : TrackedEndpointCurve N
  split : oldExploration = before ++ hit :: after
  sameSwitch : passageSwitch hit = passageSwitch contact
  outer_switches : outer.switches = oldExploration.map passageSwitch
  left_switches : left.switches = before.map passageSwitch
  right_switches : right.switches = after.map passageSwitch
  left_strict : StrictTrackedSubcurve left outer
  right_strict : StrictTrackedSubcurve right outer

/-- The dynamic result already supplied by the exact first-revisit theorem. -/
def ActivatedFirstRevisitOutcome (w : Wiring)
    (start : Nat × Tongues) (entryEdge : Nat) : Prop :=
  exists atRepeat visited,
    stepN w visited start = some atRepeat /\
      (SettlesOnSimpleCycle w atRepeat \/
        exists (A : ManufacturedReflector w start.1 entryEdge)
            (state : Tongues) (backSteps : Nat),
          PathGrooves A.toSupported.paths state /\
          A.baseState = start.2 /\
          state = A.activatedState /\
          stepN w backSteps atRepeat = some (entryEdge, state) /\
          (forall j, j ∉ A.exploration.map passageSwitch ->
            state j = start.2 j))

theorem FirstPostTurnaroundContact.contact_cases
    (H : FirstPostTurnaroundContact N oldExploration newPrefix contact) :
    passageSwitch contact ∈ oldExploration.map passageSwitch \/
      passageSwitch contact ∈ newPrefix.map passageSwitch := by
  simpa only [List.map_append, List.mem_append] using H.contactSeen

/-- Repetition inside the fresh prefix makes the extended prefix nonsimple. -/
theorem append_contact_not_simple_of_seen
    {newPrefix : List Passage} {contact : Passage}
    (hseen : passageSwitch contact ∈ newPrefix.map passageSwitch) :
    not (SwitchSimple (newPrefix ++ [contact])) := by
  intro hsimple
  unfold SwitchSimple at hsimple
  simp only [List.map_append, List.map_singleton] at hsimple
  have hdisjoint := (List.nodup_append.mp hsimple).2.2
    (passageSwitch contact) hseen
    (passageSwitch contact) (by simp)
  exact hdisjoint rfl

/-- Contact with the old exploration gives a strict ordered nest.  Both the
prefix and suffix around the old occurrence are strict subcurves of the old
switch-simple carrier, so no orientation convention is hidden in the result.
-/
theorem FirstPostTurnaroundContact.old_contact_strict_nest
    (H : FirstPostTurnaroundContact N oldExploration newPrefix contact)
    (hold : passageSwitch contact ∈
      oldExploration.map passageSwitch) :
    Nonempty (StrictOldExplorationNest N oldExploration contact) := by
  obtain ⟨hit, hhit, hsame⟩ := List.mem_map.mp hold
  obtain ⟨before, after, hsplit⟩ := List.append_of_mem hhit
  have houterNodup : (oldExploration.map passageSwitch).Nodup := by
    simpa only [SwitchSimple] using H.oldSimple
  have hsplitNodup :
      (before.map passageSwitch ++
        passageSwitch hit :: after.map passageSwitch).Nodup := by
    simpa only [hsplit, List.map_append, List.map_cons] using houterNodup
  have hbeforeNodup : (before.map passageSwitch).Nodup :=
    (List.nodup_append.mp hsplitNodup).1
  have hhitAfterNodup :
      (passageSwitch hit :: after.map passageSwitch).Nodup :=
    (List.nodup_append.mp hsplitNodup).2.1
  have hafterNodup : (after.map passageSwitch).Nodup :=
    (List.nodup_cons.mp hhitAfterNodup).2
  have houterRange : forall C,
      C ∈ oldExploration.map passageSwitch -> C < N := by
    intro C hC
    obtain ⟨passage, hp, rfl⟩ := List.mem_map.mp hC
    exact H.oldInRange passage hp
  have hbeforeRange : forall C,
      C ∈ before.map passageSwitch -> C < N := by
    intro C hC
    apply houterRange C
    rw [hsplit]
    simp only [List.map_append, List.map_cons, List.mem_append,
      List.mem_cons]
    exact Or.inl hC
  have hafterRange : forall C,
      C ∈ after.map passageSwitch -> C < N := by
    intro C hC
    apply houterRange C
    rw [hsplit]
    simp only [List.map_append, List.map_cons, List.mem_append,
      List.mem_cons]
    exact Or.inr (Or.inr hC)
  let outer : TrackedEndpointCurve N := {
    switches := oldExploration.map passageSwitch
    simple := houterNodup
    inRange := houterRange
  }
  let left : TrackedEndpointCurve N := {
    switches := before.map passageSwitch
    simple := hbeforeNodup
    inRange := hbeforeRange
  }
  let right : TrackedEndpointCurve N := {
    switches := after.map passageSwitch
    simple := hafterNodup
    inRange := hafterRange
  }
  have hleftStrict : StrictTrackedSubcurve left outer := by
    constructor
    · intro C hC
      change C ∈ before.map passageSwitch at hC
      change C ∈ oldExploration.map passageSwitch
      rw [hsplit]
      simp only [List.map_append, List.map_cons, List.mem_append,
        List.mem_cons]
      exact Or.inl hC
    · change (before.map passageSwitch).length <
        (oldExploration.map passageSwitch).length
      rw [hsplit]
      simp only [List.map_append, List.map_cons, List.length_append,
        List.length_map, List.length_cons]
      omega
  have hrightStrict : StrictTrackedSubcurve right outer := by
    constructor
    · intro C hC
      change C ∈ after.map passageSwitch at hC
      change C ∈ oldExploration.map passageSwitch
      rw [hsplit]
      simp only [List.map_append, List.map_cons, List.mem_append,
        List.mem_cons]
      exact Or.inr (Or.inr hC)
    · change (after.map passageSwitch).length <
        (oldExploration.map passageSwitch).length
      rw [hsplit]
      simp only [List.map_append, List.map_cons, List.length_append,
        List.length_map, List.length_cons]
      omega
  exact ⟨{
    hit := hit
    before := before
    after := after
    outer := outer
    left := left
    right := right
    split := hsplit
    sameSwitch := hsame.symm
    outer_switches := rfl
    left_switches := rfl
    right_switches := rfl
    left_strict := hleftStrict
    right_strict := hrightStrict
  }⟩

/-- Pure combinatorial first-contact dichotomy. -/
theorem FirstPostTurnaroundContact.repeat_or_strict_nest
    (H : FirstPostTurnaroundContact N oldExploration newPrefix contact) :
    (passageSwitch contact ∈ newPrefix.map passageSwitch /\
      not (SwitchSimple (newPrefix ++ [contact]))) \/
      Nonempty (StrictOldExplorationNest N oldExploration contact) := by
  rcases H.contact_cases with hold | hnew
  · exact Or.inr (H.old_contact_strict_nest hold)
  · exact Or.inl ⟨hnew, append_contact_not_simple_of_seen hnew⟩

/-- Dynamic first-contact dichotomy over a concrete physical trace.  A repeat
inside the new prefix is discharged by the repository's exact first-revisit
theorem; contact with the old exploration returns a strict nesting witness. -/
theorem FirstPostTurnaroundContact.activated_or_strict_nest
    {w : Wiring} {start finish : Nat × Tongues} {entryEdge : Nat}
    (H : FirstPostTurnaroundContact N oldExploration newPrefix contact)
    (htrace : PhysicalTrace w start (newPrefix ++ [contact]) finish)
    (hentry : w.link entryEdge = some start.1) :
    ActivatedFirstRevisitOutcome w start entryEdge \/
      Nonempty (StrictOldExplorationNest N oldExploration contact) := by
  rcases H.repeat_or_strict_nest with hrepeat | hnest
  · left
    exact htrace.first_revisit_activated_outcome hrepeat.2 hentry
  · exact Or.inr hnest

/-! ## Consequences of reaching the self-only tail -/

/-- A switch is recurrently productive when it writes again after every raw
time bound.  This definition is stated only in the public track language. -/
def RawRecurrentlyProductiveWriter (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (C : Nat) : Prop :=
  forall K, exists k, K ≤ k /\
    RawProductiveAt w N start k /\ rawWriterAt w start k = C

private theorem exists_stepN_of_isSome
    {w : Wiring} {start : Nat × Tongues} {k : Nat}
    (h : (stepN w k start).isSome) :
    exists finish, stepN w k start = some finish := by
  cases hstep : stepN w k start with
  | none => simp [hstep] at h
  | some finish => exact ⟨finish, hstep⟩

/-- Once a run has reached a permanent self-only tail, every globally
recurrent productive writer belongs to the tail's initial endpoint carrier.
That carrier has cardinality at most two. -/
theorem recurrent_productive_writers_le_two_of_reached_self_tail
    {w : Wiring} {N shift : Nat}
    {start middle : Nat × Tongues}
    (hN : forall p q, w.link p = some q -> p < 3 * N /\ q < 3 * N)
    (hreach : stepN w shift start = some middle)
    (T : RawPermanentSelfTail w N middle)
    (writers : List Nat)
    (hrecurrent : forall C, C ∈ writers ->
      RawRecurrentlyProductiveWriter w N start C)
    (hnd : writers.Nodup) :
    writers.length ≤ 2 := by
  have hsubset : forall C, C ∈ writers ->
      C ∈ rawFiniteCurveEndpointWritersAt w N middle 0 := by
    intro C hC
    obtain ⟨k, hk, hprod, hwriter⟩ := hrecurrent C hC shift
    let d := k - shift
    have hkEq : shift + d = k := by
      dsimp [d]
      omega
    have hdLive := exists_stepN_of_isSome (T.live d)
    have hdNextLive := exists_stepN_of_isSome (T.live (d+1))
    have hlocalProd : RawProductiveAt w N middle d := by
      apply (RawProductiveAt.shift_iff hreach hdNextLive).mpr
      simpa only [hkEq] using hprod
    have hlocalWriter : rawWriterAt w middle d = C := by
      have hshift := rawWriterAt_shift_eq hreach hdLive
      rw [hkEq] at hshift
      exact hshift.trans hwriter
    have hmem := rawSelfOnlyEpoch_productive_writer_mem_initial
      hN middle (d+1)
      (fun j _hj => T.live j)
      (fun j _hj hjProd => T.self j hjProd)
      (k := d) (by omega) hlocalProd
    rwa [hlocalWriter] at hmem
  have hle := nodup_subset_length_curve hnd hsubset
  have hcap := rawFiniteCurveEndpointWritersAt_length_le_two
    w N middle 0
  omega

/-- The corresponding vector bound after the tail has been reached, stated at
the original run's absolute times. -/
theorem distinct_tail_snapshots_le_four_of_reached_self_tail
    {w : Wiring} {N shift : Nat}
    {start middle : Nat × Tongues}
    (hN : forall p q, w.link p = some q -> p < 3 * N /\ q < 3 * N)
    (hreach : stepN w shift start = some middle)
    (T : RawPermanentSelfTail w N middle)
    (times : List Nat)
    (hnd : (times.map (fun d =>
      restrictedTonguesAt w N start (shift + d))).Nodup) :
    times.length ≤ 4 := by
  have hshift : forall d,
      restrictedTonguesAt w N middle d =
        restrictedTonguesAt w N start (shift + d) := by
    intro d
    exact restrictedTonguesAt_shift_eq hreach
      (exists_stepN_of_isSome (T.live d))
  have hlocalNodup :
      (times.map (restrictedTonguesAt w N middle)).Nodup := by
    have hmap : times.map (restrictedTonguesAt w N middle) =
        times.map (fun d =>
          restrictedTonguesAt w N start (shift + d)) := by
      apply List.map_congr_left
      intro d _hd
      exact hshift d
    rw [hmap]
    exact hnd
  exact T.distinct_snapshots_le_four hN times hlocalNodup

end GeneralN
