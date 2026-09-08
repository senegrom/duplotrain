import TrackTheta

/-!
# Contact splices and retained reflector suffixes

A changed forward contact joins a reversed old prefix to the fresh approach.
The resulting lobe and the untouched reflector suffix supply the pointwise
orbit arguments. Switch simplicity excludes premature merges and keeps each
splice action away from the retained completion.
-/

namespace GeneralN

/-- Split a list at its first element satisfying `P`.  The retained negative
prefix is what lets a damaged route be replayed up to its *first* facing
obstruction, rather than merely naming some obstruction somewhere on the
route. -/
theorem exists_first_satisfying_split
    {α : Type} (P : α → Prop) :
    ∀ xs : List α, (∃ x ∈ xs, P x) →
      ∃ before x after,
        xs = before ++ x :: after ∧
        (∀ y ∈ before, ¬ P y) ∧ P x := by
  intro xs hexists
  induction xs with
  | nil => simp at hexists
  | cons head tail ih =>
      by_cases hp : P head
      · exact ⟨[], head, tail, rfl, by simp, hp⟩
      · obtain ⟨before, x, after, hs, hb, hx⟩ := ih (by simpa [hp] using hexists)
        exact ⟨head :: before, x, after, by simp [hs], by simpa [hp] using hb, hx⟩

/-- A split at an element absent from the prefix must occur in the suffix.
This list fact needs no uniqueness or switch-count argument. -/
theorem split_after_prefix_of_not_mem {α : Type}
    {lead rest before after : List α} {x : α}
    (hsplit : lead ++ rest = before ++ x :: after)
    (habsent : x ∉ lead) :
    ∃ middle, rest = middle ++ x :: after := by
  induction lead generalizing before with
  | nil => exact ⟨before, hsplit⟩
  | cons a lead ih =>
      cases before with
      | nil =>
          have heq : a = x := (List.cons.inj hsplit).1
          exact (habsent (heq ▸ List.mem_cons_self)).elim
      | cons b before =>
          exact ih (List.cons.inj hsplit).2
            (fun h => habsent (List.mem_cons_of_mem _ h))

/-- Two members of a switch-simple route that use the same switch are the
same recorded passage. -/
theorem SwitchSimple.passage_eq_of_mem
    {route : List Passage} (hsimple : SwitchSimple route)
    {left right : Passage}
    (hleft : left ∈ route) (hright : right ∈ route)
    (hswitch : passageSwitch left = passageSwitch right) :
    left = right := by
  induction route generalizing left right with
  | nil => cases hleft
  | cons head tail ih =>
      simp only [SwitchSimple, List.map_cons, List.nodup_cons] at hsimple
      grind [SwitchSimple]

/-- Two deterministic traces which first arrive at the same avoided switch
must arrive through the same port.  Prefix comparability leaves an unmatched
suffix only if its first passage visits that switch, contradicting avoidance.
This is the endpoint form of "merge until the first named switch". -/
theorem physicalTrace_endpoints_eq_before_avoided_switch
    {w : Wiring} {start finishA finishB : Nat × Tongues}
    {left right : List Passage} {k : Nat}
    (hleft : PhysicalTrace w start left finishA)
    (hright : PhysicalTrace w start right finishB)
    (hfinishA : finishA.1 / 3 = k)
    (hfinishB : finishB.1 / 3 = k)
    (hleftForeign : ∀ passage ∈ left,
      passageSwitch passage ≠ k)
    (hrightForeign : ∀ passage ∈ right,
      passageSwitch passage ≠ k) :
    finishA = finishB := by
  rcases physicalTrace_prefix_comparable_with_endpoints hleft hright with
      ⟨suffix, heq, htail⟩ | ⟨suffix, heq, htail⟩
  all_goals
    cases suffix with
    | nil => cases htail; rfl
    | cons passage rest =>
        have := htail.head_arrive.1
        have hm : passage ∈ left ∨ passage ∈ right := by simp [heq]
        grind [passageSwitch]

theorem source_of_mem_reversePassages
    {passage : Passage} {passages : List Passage}
    (hmem : passage ∈ reversePassages passages) :
    ∃ old ∈ passages, passage = (old.2, old.1) := by
  obtain ⟨old, hold, heq⟩ := List.mem_map.mp hmem
  exact ⟨old, List.mem_reverse.mp hold, heq.symm⟩

/-- The completed-reflector forward-splice construction only used the
second reflector to supply a switch-simple route.  This is the same lemma
with that route supplied directly, so it applies to a partial second run. -/
theorem partial_first_forward_contact_active_lead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {route approach : List Passage} {p x : Nat}
    {suffix : List Passage} {startState u v : Tongues}
    {oriented : Passage}
    (hsplit : route = approach ++ (p, x) :: suffix)
    (hfullSimple : SwitchSimple route)
    (happroach :
      PhysicalTrace w (e, startState) approach (p, u))
    (hpaths : PathGrooves A.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3))
    (horiented : oriented ∈ A.orientedRoute u)
    (horientedGroove : arrive u oriented.2 = (oriented.1, u))
    (hforward : x = oriented.2) :
    ∃ (entry mouth returnPort outside : Nat)
        (oldPrefix oldTail candy : List Passage),
      (entry, mouth) ∈ A.orientedRoute u ∧
      A.orientedRoute u = oldPrefix ++ (entry, mouth) :: oldTail ∧
      PhysicalTrace w (outside, u) oldTail (A.orientedFinish u, u) ∧
      PhysicalTrace w (e, u) approach (returnPort, u) ∧
      PassagesGrooved u approach ∧
      (∀ passage ∈ approach, passageSwitch passage ≠ mouth / 3) ∧
      entry % 3 ≠ 0 ∧ entry / 3 = mouth / 3 ∧
      w.link mouth = some outside ∧
      entry ≠ returnPort ∧
      PassagesGrooved u ((mouth, entry) :: candy) ∧
      PhysicalTrace w (mouth, u) ((mouth, entry) :: candy)
        (returnPort, u) ∧
      arrive u returnPort = (mouth, flipAt u (mouth / 3)) ∧
      PassagesGrooved u candy ∧
      (∀ passage ∈ candy, passageSwitch passage ≠ mouth / 3) ∧
      IsReflector w mouth outside (candy.length + 2)
        (fun state => PassagesGrooved state candy)
        (fun state => flipAt state (mouth / 3)) ∧
      stepN w (approach.length + 1) (e, startState) =
        some (outside, flipAt u (mouth / 3)) := by
  rcases oriented with ⟨a, s⟩
  subst x
  have hap : a ≠ p := by
    intro heq
    subst p
    have hforwardOld := groove_forward horientedGroove
    have hvu := congrArg Prod.snd (harrive.symm.trans hforwardOld)
    exact hchanged (congrFun hvu (a / 3))
  obtain ⟨hsStem, haBranch, hpBranch, hsa, hsp⟩ :=
    crossed_arrivals_geometry horientedGroove harrive hap
  obtain ⟨oldPrefix, oldTail, hrouteSplit⟩ := List.append_of_mem horiented
  have hroute := A.orientedRoute_trace u hpaths
  have hrouteSimple := A.orientedRoute_simple u
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  obtain ⟨outside, hmouth, hOldPrefix, hOldRest⟩ :=
    (hrouteSplit ▸ hroute).split_grooved_at (hrouteSplit ▸ hrouteGrooved)
  have hOldGrooved : PassagesGrooved u oldPrefix := by
    intro passage hp
    exact hrouteGrooved passage (by rw [hrouteSplit]; simp [hp])
  have hOldForeign : ∀ passage ∈ oldPrefix, passageSwitch passage ≠ s / 3 := by
    rw [hrouteSplit] at hrouteSimple
    grind [SwitchSimple, passageSwitch]
  have hApproachGrooved : PassagesGrooved u approach :=
    happroach.grooved_of_switchSimple (by grind [SwitchSimple])
  have hApproachForeign : ∀ passage ∈ approach, passageSwitch passage ≠ s / 3 := by
    grind [SwitchSimple, passageSwitch]
  let candy := reversePassages oldPrefix ++ approach
  have hCandyGrooved : PassagesGrooved u candy := by
    intro passage hp
    rcases List.mem_append.mp hp with hp | hp
    · exact reversePassages_grooved hOldGrooved passage hp
    · exact hApproachGrooved passage hp
  have hCandyForeign : ∀ passage ∈ candy, passageSwitch passage ≠ s / 3 := by
    intro passage hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨old, hold, rfl⟩ := source_of_mem_reversePassages hp
      exact fun heq => hOldForeign old hold
        ((hOldPrefix.passage_exit_switch old hold).symm.trans heq)
    · exact hApproachForeign passage hp
  have hforward := happroach.replay_grooved u hApproachGrooved
  have hsplice : PhysicalTrace w (s, u) ((s, a) :: candy) (p, u) := by
    simpa [candy] using (physicalTrace_contact_retraces_prefix
      hOldPrefix hOldGrooved A.entryEdge horientedGroove).append hforward
  have hSpliceGrooved : PassagesGrooved u ((s, a) :: candy) := by
    intro passage hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact groove_forward horientedGroove
    · exact hCandyGrooved passage hp
  have hflip : v = flipAt u (s / 3) := by
    simpa only [hsp] using changed_arrival_eq_flipAt harrive hchanged
  have hcrossed : arrive u p = (s, flipAt u (s / 3)) := by rw [harrive, hflip]
  refine ⟨a, s, p, outside, oldPrefix, oldTail, candy, horiented, hrouteSplit,
    hOldRest, hforward, hApproachGrooved, hApproachForeign, haBranch, hsa.symm,
    hmouth, hap, hSpliceGrooved, hsplice, hcrossed, hCandyGrooved,
    hCandyForeign, ?_, ?_⟩
  · exact stem_lobe_isReflector_foreign w candy hsStem haBranch hpBranch hsa hsp hap
      hCandyForeign hsplice.linked hsplice.last_link hmouth
  · rw [stepN_add, happroach.sound]
    simp [stepN, step, hcrossed, hmouth]

/-- Trimming a manufactured witness does not require rebasing it to the
current tongue vector. Keep the original terminal states and core trace;
only the runway's initial state and incoming edge change. -/
theorem ManufacturedStayReflector.suffix_after_runway_passage
    {w : Wiring} {g e : Nat}
    (R : ManufacturedStayReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {before : List Passage} {p x : Nat} {after : List Passage}
    {outside : Nat}
    (hsplit : R.runway = before ++ (p, x) :: after)
    (houtside : w.link x = some outside) :
    ∃ C : ManufacturedStayReflector w outside x,
      PathGrooves C.toSupported.paths state ∧
      (LocalAction.flip (p / 3)).Avoids C.toSupported.paths := by
  obtain ⟨base, htail⟩ :=
    (hsplit ▸ R.runwayTrace).suffix_after_passage houtside
  have hs : SwitchSimple (before ++ (p, x) :: (after ++ [(R.mouth, R.arm)])) := by
    simpa [hsplit, List.append_assoc] using R.simple
  let C : ManufacturedStayReflector w outside x := {
    base := base, mouthState := R.mouthState, returnState := R.returnState
    runway := after, mouth := R.mouth, arm := R.arm
    runwayTrace := htail, coreTrace := R.coreTrace, simple := by grind [SwitchSimple]
    stemEndpoint := R.stemEndpoint, selfLink := R.selfLink, entryEdge := houtside
  }
  have hgrooves := pathGrooves_pair.mp hpaths
  refine ⟨C, pathGrooves_pair.mpr ⟨?_, hgrooves.2⟩, ?_⟩
  · intro passage hp
    apply hgrooves.1 passage
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  · intro path hp passage hpassage
    change path ∈ [after, [(R.mouth, R.arm)]] at hp
    grind [SwitchSimple, passageSwitch]

/-- A flip reflector's runway suffix uses the original candy orientation.
Its stored construction state need not equal the later state in which its
support is grooved; the ordinary reflector law already handles that. -/
theorem ManufacturedFlipReflector.suffix_after_runway_passage
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {before : List Passage} {p x : Nat} {after : List Passage}
    {outside : Nat}
    (hsplit : R.runway = before ++ (p, x) :: after)
    (houtside : w.link x = some outside) :
    ∃ C : ManufacturedFlipReflector w outside x,
      C.actionSwitch = R.actionSwitch ∧
      p / 3 ≠ C.actionSwitch ∧
      PathGrooves C.toSupported.paths state ∧
      (LocalAction.flip (p / 3)).Avoids C.toSupported.paths := by
  obtain ⟨base, htail⟩ :=
    (hsplit ▸ R.runwayTrace).suffix_after_passage houtside
  have hs : SwitchSimple (before ++ (p, x) :: (after ++ (R.mouth, R.firstArm) :: R.candy)) := by
    simpa [hsplit, List.append_assoc] using R.simple
  let C : ManufacturedFlipReflector w outside x := {
    base := base, mouthState := R.mouthState, returnState := R.returnState
    afterReturn := R.afterReturn, runway := after, candy := R.candy
    mouth := R.mouth, firstArm := R.firstArm, secondArm := R.secondArm
    runwayTrace := htail, candyTrace := R.candyTrace, simple := by grind [SwitchSimple]
    crossed := R.crossed, arms_ne := R.arms_ne, entryEdge := houtside
  }
  have hgrooves := pathGrooves_pair.mp hpaths
  refine ⟨C, rfl, ?_, pathGrooves_pair.mpr ⟨?_, hgrooves.2⟩, ?_⟩
  · exact R.support_foreign R.runway (by simp) (p, x)
      (by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self)
  · intro passage hp
    apply hgrooves.1 passage
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  · intro path hp passage hpassage
    change path ∈ [after, R.candy] at hp
    grind [SwitchSimple, passageSwitch]

theorem ManufacturedFlipReflector.nonrunway_oriented_branch_entry_is_candy
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues) {entry mouth : Nat}
    (horiented : (entry, mouth) ∈
      (ManufacturedReflector.flip R).orientedRoute state)
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (hentryBranch : entry % 3 ≠ 0) :
    ∃ old ∈ R.candy,
      (entry, mouth) = old ∨
        (entry, mouth) = (old.2, old.1) := by
  by_cases hselected :
      state R.actionSwitch = bval R.firstArm
  · simp only [ManufacturedReflector.orientedRoute, hselected,
      if_pos] at horiented
    rcases List.mem_append.mp horiented with hrunway | hcore
    · exact (hnotRunway hrunway).elim
    · rcases List.mem_cons.mp hcore with hhead | hcandy
      · have hentryEq : entry = R.mouth :=
          congrArg Prod.fst hhead
        apply (hentryBranch (by
          rw [hentryEq]
          exact R.mouth_is_stem)).elim
      · exact ⟨(entry, mouth), hcandy, Or.inl rfl⟩
  · simp only [ManufacturedReflector.orientedRoute, hselected,
      if_false] at horiented
    rcases List.mem_append.mp horiented with hrunway | hcore
    · exact (hnotRunway hrunway).elim
    · rcases List.mem_cons.mp hcore with hhead | hreverse
      · have hentryEq : entry = R.mouth :=
          congrArg Prod.fst hhead
        apply (hentryBranch (by
          rw [hentryEq]
          exact R.mouth_is_stem)).elim
      · obtain ⟨old, hold, hEq⟩ :=
          source_of_mem_reversePassages hreverse
        exact ⟨old, hold, Or.inr hEq⟩

/-- Either orientation of a recorded candy passage is disjoint from the
old reflector's private mouth switch.  This packages the endpoint-switch
transport needed when a later splice cuts the selected candy route. -/
theorem ManufacturedFlipReflector.candy_entry_foreign_action
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    {entry mouth : Nat} {old : Passage}
    (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨
      (entry, mouth) = (old.2, old.1)) :
    entry / 3 ≠ R.actionSwitch := by
  have holdForeign : passageSwitch old ≠ R.actionSwitch :=
    R.support_foreign R.candy (by simp) old hold
  have holdExitSwitch : old.2 / 3 = passageSwitch old :=
    R.candyTrace.passage_exit_switch old
      (List.mem_cons_of_mem _ hold)
  rcases horientation with hforward | hreverse
  · have hentryEq : entry = old.1 :=
      congrArg Prod.fst hforward
    simpa [passageSwitch, hentryEq] using holdForeign
  · have hentryEq : entry = old.2 :=
      congrArg Prod.fst hreverse
    intro hEq
    apply holdForeign
    rw [← holdExitSwitch, ← hentryEq]
    exact hEq

/-- A fresh approach to a strict candy splice cannot meet the old reflector
mouth facing-first.  From that mouth, determinism makes the fresh route and
the old selected candy route coincide until their first visit to the splice
switch.  Both avoid that switch internally, so the avoided-switch endpoint
lemma forces the two arrival arms to be equal, contradicting the splice. -/
theorem ManufacturedFlipReflector.facing_approach_to_candy_splice_impossible
    {w : Wiring} {g e entry mouth returnPort : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {oldPrefix oldTail approach : List Passage}
    (hrouteSplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (_hentryBranch : entry % 3 ≠ 0)
    (happroach : PhysicalTrace w (g, state) approach
      (returnPort, state))
    (happroachGrooved : PassagesGrooved state approach)
    (happroachForeignNew : ∀ passage ∈ approach,
      passageSwitch passage ≠ mouth / 3)
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (harms : entry ≠ returnPort)
    {target : Passage}
    (htargetMem : target ∈ approach)
    (htargetSwitch : passageSwitch target = R.actionSwitch)
    (htargetStem : target.1 % 3 = 0) : False := by
  have htargetRoute : (entry, mouth) ∈
      (ManufacturedReflector.flip R).orientedRoute state := by
    rw [hrouteSplit]
    exact List.mem_append_right oldPrefix List.mem_cons_self
  have hroute :=
    (ManufacturedReflector.flip R).orientedRoute_trace state hpaths
  have hrouteSimple :=
    (ManufacturedReflector.flip R).orientedRoute_simple state
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  have hentryGrooved : arrive state entry = (mouth, state) :=
    groove_forward (hrouteGrooved (entry, mouth) htargetRoute)
  have hentryNew : entry / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state entry
    rw [hentryGrooved] at hs
    exact hs.symm
  have hreturnNew : returnPort / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state returnPort
    rw [hcrossed] at hs
    exact hs.symm

  obtain ⟨freshBefore, freshAfter, hfreshSplit⟩ :=
    List.append_of_mem htargetMem
  obtain ⟨outside, hlink, _, htail⟩ :=
    (hfreshSplit ▸ happroach).split_grooved_at (hfreshSplit ▸ happroachGrooved)
  have hfreshRest := PhysicalTrace.cons
    (groove_forward (happroachGrooved target htargetMem)) hlink htail
  rcases target with ⟨p, x⟩
  simp only [passageSwitch] at htargetSwitch
  have hpMouth : p = R.mouth := by
    have hm := R.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch at htargetSwitch
    omega
  subst p
  have hfreshForeign : ∀ passage ∈
      (R.mouth, x) :: freshAfter,
      passageSwitch passage ≠ mouth / 3 := by
    intro passage hpassage
    apply happroachForeignNew passage
    rw [hfreshSplit]
    exact List.mem_append_right freshBefore hpassage

  have hOldSegment : ∃ segment,
      PhysicalTrace w (R.mouth, state) segment (entry, state) ∧
      (∀ passage ∈ segment, passageSwitch passage ≠ mouth / 3) := by
    have hcore : ∃ core, (ManufacturedReflector.flip R).orientedRoute state =
        R.runway ++ core := by
      simp only [ManufacturedReflector.orientedRoute]
      split <;> exact ⟨_, rfl⟩
    obtain ⟨core, hcore⟩ := hcore
    have htail := (hcore ▸ hroute).after_prefix
      (R.runway_trace state (pathGrooves_pair.mp hpaths).1)
    have hsimple : SwitchSimple core := by
      have hs := hrouteSimple
      rw [hcore] at hs
      exact (List.nodup_append.mp (by simpa [SwitchSimple] using hs)).2.1
    obtain ⟨before, hsplit⟩ :=
      split_after_prefix_of_not_mem (hcore.symm.trans hrouteSplit) hnotRunway
    obtain ⟨_, _, hprefix, _⟩ := (hsplit ▸ htail).split_grooved_at
      (hsplit ▸ htail.grooved_of_switchSimple hsimple)
    refine ⟨before, hprefix, ?_⟩
    rw [hsplit] at hsimple
    grind [SwitchSimple, passageSwitch]
  obtain ⟨oldSegment, holdSegment, holdForeign⟩ := hOldSegment
  have hendpoints :=
    physicalTrace_endpoints_eq_before_avoided_switch
      holdSegment hfreshRest hentryNew hreturnNew
      holdForeign hfreshForeign
  apply harms
  exact congrArg Prod.fst hendpoints

/-- Once a selected-route split occurs strictly inside the candy, every
later selected passage is foreign to the old reflector's mouth action. -/
theorem ManufacturedFlipReflector.candy_tail_foreign_action
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    {oldPrefix oldTail : List Passage} {entry mouth : Nat}
    (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (hentryBranch : entry % 3 ≠ 0) :
    ∀ passage ∈ oldTail,
      passageSwitch passage ≠ R.actionSwitch := by
  have hcore : ∃ arm candy,
      (ManufacturedReflector.flip R).orientedRoute state =
        (R.runway ++ [(R.mouth, arm)]) ++ candy ∧
      (∀ passage ∈ candy, passageSwitch passage ≠ R.actionSwitch) := by
    by_cases hselected : state R.actionSwitch = bval R.firstArm
    · exact ⟨R.firstArm, R.candy,
        by simp [ManufacturedReflector.orientedRoute, hselected, List.append_assoc],
        R.support_foreign R.candy (by simp)⟩
    · refine ⟨R.secondArm, reversePassages R.candy,
        by simp [ManufacturedReflector.orientedRoute, hselected, List.append_assoc], ?_⟩
      intro passage hp
      obtain ⟨old, hold, rfl⟩ := source_of_mem_reversePassages hp
      rw [show passageSwitch (old.2, old.1) = passageSwitch old from
        R.candyTrace.passage_exit_switch old (List.mem_cons_of_mem _ hold)]
      exact R.support_foreign R.candy (by simp) old hold
  obtain ⟨arm, candy, hcore, hforeign⟩ := hcore
  have habsent : (entry, mouth) ∉ R.runway ++ [(R.mouth, arm)] := by
    intro hm
    rcases List.mem_append.mp hm with hrunway | hhead
    · exact hnotRunway hrunway
    · have heq : entry = R.mouth := congrArg Prod.fst (List.mem_singleton.mp hhead)
      exact hentryBranch (heq.symm ▸ R.mouth_is_stem)
  obtain ⟨middle, hcandy⟩ :=
    split_after_prefix_of_not_mem (hcore.symm.trans hsplit) habsent
  intro passage hp
  apply hforeign passage
  rw [hcandy]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)

/-- After the selected one-way route of a flip reflector reaches its far
candy arm, one trailing passage applies the reflector's action and the train
retraces the runway to the far boundary.  The exact reverse-runway trace is
retained for later disjointness arguments. -/
theorem ManufacturedFlipReflector.oriented_return_trace
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state) :
    PhysicalTrace w
      ((ManufacturedReflector.flip R).orientedFinish state, state)
      (((ManufacturedReflector.flip R).orientedFinish state,
          R.mouth) :: reversePassages R.runway)
      (g, flipAt state R.actionSwitch) := by
  exact physicalTrace_contact_retraces_prefix R.runwayTrace
    (grooved_after_flip_other (pathGrooves_pair.mp hpaths).1
      (R.support_foreign R.runway (by simp)))
    R.entryEdge (R.oriented_finish_arrive state)


section
variable {w : Wiring} {g e outside : Nat}
  (R : ManufacturedFlipReflector w e g)
  (state : Tongues)
  (hpaths : PathGrooves R.toSupported.paths state)
  {oldPrefix oldTail : List Passage} {entry mouth : Nat}
  (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
    oldPrefix ++ (entry, mouth) :: oldTail)
  (htail : PhysicalTrace w (outside, state) oldTail
    ((ManufacturedReflector.flip R).orientedFinish state, state))
  (hnotRunway : (entry, mouth) ∉ R.runway)
include w g e outside R state hpaths oldPrefix oldTail entry mouth hsplit htail hnotRunway

/-- In the candy residual, the untouched selected-route tail followed by the
trailing old-mouth return and reverse runway completes from the splice's
outside endpoint to the old boundary.  The entire completion is disjoint
from the splice switch. -/
theorem ManufacturedFlipReflector.candy_completion_foreign
    {old : Passage} (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨
      (entry, mouth) = (old.2, old.1)) :
    let completion := oldTail ++
      (((ManufacturedReflector.flip R).orientedFinish state,
        R.mouth) :: reversePassages R.runway)
    PhysicalTrace w (outside, state) completion
        (g, flipAt state R.actionSwitch) ∧
      (∀ passage ∈ completion,
        passageSwitch passage ≠ entry / 3) := by
  have hsimple := (ManufacturedReflector.flip R).orientedRoute_simple state
  have htarget : (entry, mouth) ∈ (ManufacturedReflector.flip R).orientedRoute state := by
    rw [hsplit]; simp
  have htailForeign : ∀ passage ∈ oldTail, passageSwitch passage ≠ entry / 3 := by
    rw [hsplit] at hsimple
    grind [SwitchSimple, passageSwitch]
  have hnewOld := R.candy_entry_foreign_action hold horientation
  have hfinish := arrive_exit_switch state ((ManufacturedReflector.flip R).orientedFinish state)
  rw [R.oriented_finish_arrive state] at hfinish
  change R.actionSwitch = (ManufacturedReflector.flip R).orientedFinish state / 3 at hfinish
  refine ⟨htail.append (R.oriented_return_trace state hpaths), ?_⟩
  intro passage hp
  rcases List.mem_append.mp hp with hp | hp
  · exact htailForeign passage hp
  · rcases List.mem_cons.mp hp with rfl | hp
    · simpa only [passageSwitch, ← hfinish] using Ne.symm hnewOld
    · obtain ⟨old, holdRunway, rfl⟩ := source_of_mem_reversePassages hp
      intro heq
      have holdRoute : old ∈ (ManufacturedReflector.flip R).orientedRoute state := by
        simp only [ManufacturedReflector.orientedRoute]
        split <;> exact List.mem_append_left _ holdRunway
      have hequal := hsimple.passage_eq_of_mem holdRoute htarget
        ((R.runwayTrace.passage_exit_switch old holdRunway).symm.trans heq)
      exact hnotRunway (hequal ▸ holdRunway)


end

end GeneralN
