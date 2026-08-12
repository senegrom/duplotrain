import ProductiveBoundaryNAddFour
import ChangedContactNAddFour
import OldContactContinuation
import KnownEdgeNAddFourChangedClosed

/-!
# The productive-boundary support contact

This file resolves the physical content of `SecondFirstWriterLeadContact`.
The old lead is a switch-simple tongue-stable trace from `g` to `e`; the
returned prefix is switch-simple from `e` back to `g`.  If the two traces
name a common switch, choose their first such contact on the returned
prefix.  Before it, every old-lead groove is still valid.

A backward contact closes a grooved cycle and gives an immediate one-vector
tail.  A forward contact makes the two remaining deterministic tails prefix
comparable.  Since their endpoints are opposite, a strict unmatched tail
would make one of the switch-simple traces return to its own start port
before it ends.  The only equality case has `g = e`, when the nonempty old
lead itself is already a grooved cycle.

Everything is over the raw `Wiring` / `stepN` dynamics and is symbolic in
`N`; there is no enumeration.
-/

namespace GeneralN

/-- A raw run reaches a configuration from which every future tongue vector
is one fixed vector.  Ports may continue to move. -/
structure RawOneVectorTail (w : Wiring) (start : Nat × Tongues) : Type where
  shift : Nat
  port : Nat
  phase : Tongues
  reached : stepN w shift start = some (port, phase)
  all_time : ∀ d, ∃ q, stepN w d (port, phase) = some (q, phase)

/-- A one-vector tail reached within an explicitly bounded physical prefix. -/
structure BoundedRawOneVectorTail
    (w : Wiring) (start : Nat × Tongues) (limit : Nat) : Type where
  tail : RawOneVectorTail w start
  within : tail.shift ≤ limit

/-- A nonempty grooved closed trace has its fixed tongue vector at every
future time.  No switch-simplicity is needed: groove preservation is the
actual dynamic hypothesis. -/
theorem PhysicalTrace.stable_grooved_cycle_all_time
    {w : Wiring} {q : Nat} {u : Tongues} {cycle : List Passage}
    (hnonempty : cycle ≠ [])
    (hcycle : PhysicalTrace w (q, u) cycle (q, u))
    (hgrooved : PassagesGrooved u cycle) :
    ∀ d, ∃ port, stepN w d (q, u) = some (port, u) := by
  let period := cycle.length
  have hperiodPositive : 0 < period := by
    dsimp [period]
    cases cycle with
    | nil => exact (hnonempty rfl).elim
    | cons _ _ => simp
  intro d
  let laps := d / period
  let offset := d % period
  have hoffsetLt : offset < period := Nat.mod_lt d hperiodPositive
  have hdecomp : d = laps * period + offset := by
    dsimp [laps, offset]
    have hdiv := Nat.div_add_mod d period
    rw [Nat.mul_comm period (d / period)] at hdiv
    exact hdiv.symm
  have hlaps : stepN w (laps * period) (q, u) = some (q, u) :=
    stepN_mul_period_pair_novelty hcycle.sound laps
  obtain ⟨port, hoffset⟩ :=
    hcycle.grooved_prefix_tongues u hgrooved (Nat.le_of_lt hoffsetLt)
  exact ⟨port, by rw [hdecomp, stepN_add, hlaps]; exact hoffset⟩

/-- A switch-simple physical trace cannot revisit its literal start port at
a positive strict prefix, independently of the tongue vector there. -/
theorem PhysicalTrace.no_strict_return_to_start_port_public
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    {k : Nat} {returned : Tongues}
    (hpositive : 0 < k)
    (hinside : k < passages.length)
    (hreturn : stepN w k start = some (start.1, returned)) : False := by
  have hzero := htrace.rawWriterAt_eq_passageSwitch_getElem
    (k := 0) (by omega)
  have hreturned := htrace.rawWriterAt_eq_passageSwitch_getElem
    (k := k) hinside
  have hwriters : rawWriterAt w start 0 = rawWriterAt w start k := by
    simp [rawWriterAt, rawEntryAt, stepN, hreturn]
  have hpair := List.pairwise_iff_getElem.mp hsimple
  have hne := hpair 0 k (by simpa using (show 0 < passages.length by omega))
    (by simpa using hinside) hpositive
  apply hne
  simpa [hzero, hreturned] using hwriters

def TouchesLead (lead : List Passage) (fresh : Passage) : Prop :=
  ∃ old ∈ lead, passageSwitch old = passageSwitch fresh

private theorem first_touches_lead_split
    (lead fresh : List Passage)
    (hcontact : ∃ new ∈ fresh, TouchesLead lead new) :
    ∃ before new after,
      fresh = before ++ new :: after ∧
      (∀ prior ∈ before, ¬ TouchesLead lead prior) ∧
      TouchesLead lead new := by
  classical
  induction fresh with
  | nil =>
      obtain ⟨new, hnew, _⟩ := hcontact
      cases hnew
  | cons head tail ih =>
      by_cases hhead : TouchesLead lead head
      · exact ⟨[], head, tail, rfl, (by intro p hp; cases hp), hhead⟩
      · have htail : ∃ new ∈ tail, TouchesLead lead new := by
          obtain ⟨new, hnew, htouch⟩ := hcontact
          rcases List.mem_cons.mp hnew with rfl | hnew
          · exact (hhead htouch).elim
          · exact ⟨new, hnew, htouch⟩
        obtain ⟨before, new, after, hsplit, hbefore, hnew⟩ := ih htail
        exact ⟨head :: before, new, after, by simp [hsplit],
          (by
            intro prior hprior
            rcases List.mem_cons.mp hprior with rfl | hprior
            · exact hhead
            · exact hbefore prior hprior), hnew⟩

/-- Canonical first common-switch decomposition of the old lead and returned
prefix. -/
structure LeadReturnFirstContact
    (lead fresh : List Passage) : Type where
  oldBefore : List Passage
  old : Passage
  oldAfter : List Passage
  newBefore : List Passage
  new : Passage
  newAfter : List Passage
  lead_split : lead = oldBefore ++ old :: oldAfter
  fresh_split : fresh = newBefore ++ new :: newAfter
  same_switch : passageSwitch old = passageSwitch new
  prior_avoids : ∀ prior ∈ newBefore, ∀ oldPassage ∈ lead,
    passageSwitch prior ≠ passageSwitch oldPassage

theorem leadReturnFirstContact_of_common_switch
    {lead fresh : List Passage}
    (hcontact : ∃ old ∈ lead, ∃ new ∈ fresh,
      passageSwitch old = passageSwitch new) :
    Nonempty (LeadReturnFirstContact lead fresh) := by
  classical
  have hexists : ∃ new ∈ fresh, TouchesLead lead new := by
    obtain ⟨old, hold, new, hnew, hsame⟩ := hcontact
    exact ⟨new, hnew, old, hold, hsame⟩
  obtain ⟨newBefore, new, newAfter, hfresh, havoid, htouch⟩ :=
    first_touches_lead_split lead fresh hexists
  obtain ⟨old, hold, hsame⟩ := htouch
  obtain ⟨oldBefore, oldAfter, hlead⟩ := List.append_of_mem hold
  exact ⟨{
    oldBefore := oldBefore
    old := old
    oldAfter := oldAfter
    newBefore := newBefore
    new := new
    newAfter := newAfter
    lead_split := hlead
    fresh_split := hfresh
    same_switch := hsame
    prior_avoids := by
      intro prior hprior oldPassage holdPassage hEq
      exact havoid prior hprior ⟨oldPassage, holdPassage, hEq.symm⟩
  }⟩

/-- A backward first contact already gives a one-vector tail immediately
after the contacting passage. -/
theorem LeadReturnFirstContact.backward_one_vector_tail
    {w : Wiring} {g e : Nat} {base after : Tongues}
    {lead fresh : List Passage}
    (C : LeadReturnFirstContact lead fresh)
    (hlead : PhysicalTrace w (g, base) lead (e, base))
    (hleadSimple : SwitchSimple lead)
    (hreturn : PhysicalTrace w (e, base) fresh (g, after))
    (hreturnSimple : SwitchSimple fresh)
    (hentry : w.link e = some g)
    (hbackward : C.new.2 = C.old.1) :
    ∃ T : RawOneVectorTail w (e, base), T.shift ≤ fresh.length := by
  have hleadGroovedBase : PassagesGrooved base lead :=
    hlead.grooved_of_switchSimple hleadSimple
  have hreturn' := hreturn
  rw [C.fresh_split] at hreturn'
  obtain ⟨newMiddle, hnewBeforeRaw, hnewConsRaw⟩ :=
    hreturn'.split_append
  have hnewPort : newMiddle.1 = C.new.1 :=
    hnewConsRaw.head_arrive.1
  rcases newMiddle with ⟨newPort, u⟩
  simp only at hnewPort
  subst newPort
  have hnewBefore : PhysicalTrace w (e, base) C.newBefore
      (C.new.1, u) := hnewBeforeRaw
  have hnewCons : PhysicalTrace w (C.new.1, u)
      (C.new :: C.newAfter) (g, after) := hnewConsRaw
  obtain ⟨v, harrive⟩ := hnewCons.head_arrive.2

  have hleadGroovedU : PassagesGrooved u lead := by
    intro passage hpassage
    have hgroove := hleadGroovedBase passage hpassage
    have hexit : passage.2 / 3 = passageSwitch passage := by
      have hs := arrive_exit_switch base passage.2
      rw [hgroove] at hs
      exact hs.symm
    apply groove_transfer hgroove
    rw [hexit]
    exact hnewBefore.preserves (passageSwitch passage) (by
      intro prior hprior
      exact C.prior_avoids prior hprior passage hpassage)

  have holdPrefix := simple_grooved_trace_prefix_to_occurrence
    hlead C.lead_split hleadGroovedBase hleadSimple
  have hrecordedGroovedV : PassagesGrooved v C.oldBefore := by
    intro passage hpassage
    have hgroove := hleadGroovedBase passage (by
      rw [C.lead_split]
      exact List.mem_append_left _ hpassage)
    have hexit : passage.2 / 3 = passageSwitch passage := by
      have hs := arrive_exit_switch base passage.2
      rw [hgroove] at hs
      exact hs.symm
    apply groove_transfer hgroove
    rw [hexit]
    calc
      v (passageSwitch passage) = u (passageSwitch passage) := by
        apply arrive_preserves_other harrive
        intro hEq
        apply holdPrefix.2 passage hpassage
        calc
          passageSwitch passage = C.new.1 / 3 := hEq
          _ = passageSwitch C.new := rfl
          _ = passageSwitch C.old := C.same_switch.symm
      _ = base (passageSwitch passage) :=
        hnewBefore.preserves (passageSwitch passage) (by
          intro prior hprior
          exact C.prior_avoids prior hprior passage (by
            rw [C.lead_split]
            exact List.mem_append_left _ hpassage))

  have hnewBeforeSimple : SwitchSimple C.newBefore := by
    have hs := hreturnSimple
    unfold SwitchSimple at hs ⊢
    rw [C.fresh_split] at hs
    simp only [List.map_append, List.map_cons] at hs
    exact (List.nodup_append.mp hs).1

  have happroachGroovedU : PassagesGrooved u C.newBefore := by
    exact hnewBefore.grooved_of_switchSimple hnewBeforeSimple
  have hOldMem : C.old ∈ lead := by
    have hm : C.old ∈ C.oldBefore ++ C.old :: C.oldAfter :=
      List.mem_append_right _ List.mem_cons_self
    exact Eq.mp (congrArg (fun xs => C.old ∈ xs) C.lead_split.symm) hm
  have happroachGroovedV : PassagesGrooved v C.newBefore := by
    intro passage hpassage
    have hgroove := happroachGroovedU passage hpassage
    have hexit : passage.2 / 3 = passageSwitch passage := by
      have hs := arrive_exit_switch u passage.2
      rw [hgroove] at hs
      exact hs.symm
    apply groove_transfer hgroove
    rw [hexit]
    apply arrive_preserves_other harrive
    intro hEq
    exact C.prior_avoids passage hpassage C.old hOldMem (by
        calc
          passageSwitch passage = C.new.1 / 3 := hEq
          _ = passageSwitch C.new := rfl
          _ = passageSwitch C.old := C.same_switch.symm)

  have hcontact : arrive u C.new.1 = (C.old.1, v) := by
    simpa [hbackward] using harrive
  have hback := physicalTrace_contact_retraces_prefix
    holdPrefix.1 hrecordedGroovedV hentry hcontact
  have hforward := hnewBefore.replay_grooved v happroachGroovedV
  let rest := reversePassages C.oldBefore ++ C.newBefore
  let cycle := (C.new.1, C.old.1) :: rest
  have htransient : PhysicalTrace w (C.new.1, u) cycle
      (C.new.1, v) := by
    dsimp [cycle, rest]
    simpa [List.append_assoc] using hback.append hforward
  have htransient' : PhysicalTrace w (C.new.1, u)
      ([(C.new.1, C.old.1)] ++ rest) (C.new.1, v) := by
    simpa [cycle] using htransient
  obtain ⟨middle, hhead, htail⟩ := htransient'.split_append
  have hheadStep : step w (C.new.1, u) = some middle := by
    simpa [stepN] using hhead.sound
  have hmiddlePhase : middle.2 = v := by
    have hparts := step_some_parts hheadStep
    calc
      middle.2 = arrivedTongues (C.new.1, u) := hparts.2
      _ = v := by simp [arrivedTongues, harrive]
  let q := middle.1
  have hmiddle : middle = (q, v) := Prod.ext rfl hmiddlePhase
  rw [hmiddle] at hhead htail
  have hcontactBack := arrive_back u C.new.1
  rw [hcontact] at hcontactBack
  have hcontactGroove : arrive v C.new.1 = (C.old.1, v) :=
    groove_forward hcontactBack
  have hcontactLink : w.link C.old.1 = some q := by
    simpa [q, lastPassageExit] using hhead.last_link
  have hstableHead : PhysicalTrace w (C.new.1, v)
      [(C.new.1, C.old.1)] (q, v) :=
    PhysicalTrace.cons hcontactGroove hcontactLink (PhysicalTrace.nil _)
  let rotated := rest ++ [(C.new.1, C.old.1)]
  have hstable : PhysicalTrace w (q, v) rotated (q, v) := by
    dsimp [rotated]
    exact htail.append hstableHead
  have hrotatedGrooved : PassagesGrooved v rotated := by
    intro passage hpassage
    dsimp [rotated, rest] at hpassage
    rcases List.mem_append.mp hpassage with hrest | hcontactMem
    · rcases List.mem_append.mp hrest with hold | hnew
      · exact reversePassages_grooved hrecordedGroovedV passage hold
      · exact happroachGroovedV passage hnew
    · simp only [List.mem_singleton] at hcontactMem
      simpa [hcontactMem] using hcontactBack
  have hrotatedNonempty : rotated ≠ [] := by
    intro hempty
    have : (C.new.1, C.old.1) ∈ rotated := by
      dsimp [rotated]
      exact List.mem_append_right _ List.mem_cons_self
    rw [hempty] at this
    cases this
  have hreached : stepN w (C.newBefore.length + 1) (e, base) =
      some (q, v) := by
    have hp := hnewBefore.append hhead
    simpa [q] using hp.sound
  refine ⟨{
    shift := C.newBefore.length + 1
    port := q
    phase := v
    reached := hreached
    all_time := hstable.stable_grooved_cycle_all_time
      hrotatedNonempty hrotatedGrooved
  }, ?_⟩
  have hlen := congrArg List.length C.fresh_split
  simp only [List.length_append, List.length_cons] at hlen
  dsimp
  omega


/-- The exact state and trace data at the canonical first common switch.
Every old-lead groove is still valid immediately before the contact. -/
theorem LeadReturnFirstContact.contact_data
    {w : Wiring} {g e : Nat} {base after : Tongues}
    {lead fresh : List Passage}
    (C : LeadReturnFirstContact lead fresh)
    (hlead : PhysicalTrace w (g, base) lead (e, base))
    (hleadSimple : SwitchSimple lead)
    (hreturn : PhysicalTrace w (e, base) fresh (g, after)) :
    ∃ u v,
      PhysicalTrace w (e, base) C.newBefore (C.new.1, u) ∧
      PhysicalTrace w (C.new.1, u)
        (C.new :: C.newAfter) (g, after) ∧
      arrive u C.new.1 = (C.new.2, v) ∧
      PassagesGrooved u lead := by
  have hleadGroovedBase : PassagesGrooved base lead :=
    hlead.grooved_of_switchSimple hleadSimple
  have hreturn' := hreturn
  rw [C.fresh_split] at hreturn'
  obtain ⟨middle, hbeforeRaw, hconsRaw⟩ :=
    hreturn'.split_append
  have hport : middle.1 = C.new.1 :=
    hconsRaw.head_arrive.1
  rcases middle with ⟨port, u⟩
  simp only at hport
  subst port
  have hbefore : PhysicalTrace w (e, base) C.newBefore
      (C.new.1, u) := hbeforeRaw
  have hcons : PhysicalTrace w (C.new.1, u)
      (C.new :: C.newAfter) (g, after) := hconsRaw
  obtain ⟨v, harrive⟩ := hcons.head_arrive.2
  have hleadGroovedU : PassagesGrooved u lead := by
    intro passage hpassage
    have hgroove := hleadGroovedBase passage hpassage
    have hexit : passage.2 / 3 = passageSwitch passage := by
      have hs := arrive_exit_switch base passage.2
      rw [hgroove] at hs
      exact hs.symm
    apply groove_transfer hgroove
    rw [hexit]
    exact hbefore.preserves (passageSwitch passage) (by
      intro prior hprior
      exact C.prior_avoids prior hprior passage hpassage)
  exact ⟨u, v, hbefore, hcons, harrive, hleadGroovedU⟩

/-- At the first common switch the returned passage exits through one of
the two ports of the still-grooved old passage. -/
theorem LeadReturnFirstContact.exit_dichotomy
    {w : Wiring} {g e : Nat} {base after : Tongues}
    {lead fresh : List Passage}
    (C : LeadReturnFirstContact lead fresh)
    (hlead : PhysicalTrace w (g, base) lead (e, base))
    (hleadSimple : SwitchSimple lead)
    (hreturn : PhysicalTrace w (e, base) fresh (g, after)) :
    C.new.2 = C.old.1 ∨ C.new.2 = C.old.2 := by
  obtain ⟨u, v, _hbefore, _hcons, harrive, hgrooved⟩ :=
    C.contact_data hlead hleadSimple hreturn
  have holdMem : C.old ∈ lead := by
    have hm : C.old ∈ C.oldBefore ++ C.old :: C.oldAfter :=
      List.mem_append_right _ List.mem_cons_self
    exact Eq.mp
      (congrArg (fun xs => C.old ∈ xs) C.lead_split.symm) hm
  have hold := hgrooved C.old holdMem
  have hswitch : C.old.1 / 3 = C.new.1 / 3 := by
    simpa [passageSwitch] using C.same_switch
  exact grooved_contact_exits_on_old_passage hold harrive hswitch

/-- At a productive forward first contact, the old and returned suffixes are
prefix-comparable, and the unmatched suffix carries the exact endpoint trace.
This is the physical, endpoint-valued form needed for the no-return argument. -/
theorem LeadReturnFirstContact.forward_changed_suffix_comparison
    {w : Wiring} {g e : Nat} {base after : Tongues}
    {lead fresh : List Passage}
    (C : LeadReturnFirstContact lead fresh)
    (hlead : PhysicalTrace w (g, base) lead (e, base))
    (hleadSimple : SwitchSimple lead)
    (hreturn : PhysicalTrace w (e, base) fresh (g, after))
    (hforward : C.new.2 = C.old.2)
    (hchanged :
      let data := C.contact_data hlead hleadSimple hreturn
      let u := Classical.choose data
      let v := Classical.choose (Classical.choose_spec data)
      v (C.new.1 / 3) ≠ u (C.new.1 / 3)) :
    Exists fun v =>
      (Exists fun suffix =>
        C.newAfter = C.oldAfter ++ suffix /\
        PhysicalTrace w (e, v) suffix (g, after)) \/
      (Exists fun suffix =>
        C.oldAfter = C.newAfter ++ suffix /\
        PhysicalTrace w (g, after) suffix (e, v)) := by
  let data := C.contact_data hlead hleadSimple hreturn
  let u := Classical.choose data
  let dataU := Classical.choose_spec data
  let v := Classical.choose dataU
  have hspec := Classical.choose_spec dataU
  rcases hspec with ⟨hbefore, hnewCons, harrive, hgrooved⟩
  have hchanged'' : v (C.new.1 / 3) ≠ u (C.new.1 / 3) := by
    simpa only [data, u, dataU, v] using hchanged
  have holdPrefix := simple_grooved_trace_prefix_to_occurrence
    hlead C.lead_split hgrooved hleadSimple
  have hleadU := hlead.replay_grooved u hgrooved
  have hleadUSplit := hleadU
  rw [C.lead_split] at hleadUSplit
  obtain ⟨middle, hOldPrefix, hOldCons⟩ :=
    hleadUSplit.split_append
  have hmiddle : middle = (C.old.1, u) := by
    have h1 := hOldPrefix.sound
    have h2 := holdPrefix.1.sound
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  rw [hmiddle] at hOldCons
  have hOldSimple : SwitchSimple (C.old :: C.oldAfter) := by
    have hs := hleadSimple
    unfold SwitchSimple at hs ⊢
    rw [C.lead_split] at hs
    simp only [List.map_append, List.map_cons] at hs
    exact (List.nodup_append.mp hs).2.1
  have holdMem : C.old ∈ lead := by
    have hm : C.old ∈ C.oldBefore ++ C.old :: C.oldAfter :=
      List.mem_append_right _ List.mem_cons_self
    exact Eq.mp
      (congrArg (fun xs => C.old ∈ xs) C.lead_split.symm) hm
  have hold : arrive u C.old.1 = (C.old.2, u) :=
    groove_forward (hgrooved C.old holdMem)
  have hswitch : C.old.1 / 3 = C.new.1 / 3 := by
    simpa [passageSwitch] using C.same_switch
  have hnewEq : C.new = (C.new.1, C.old.2) := by
    apply Prod.ext
    · rfl
    · exact hforward
  have hnewCons'' : PhysicalTrace w (C.new.1, u)
      ((C.new.1, C.old.2) :: C.newAfter) (g, after) := by
    rw [← hnewEq]
    exact hnewCons
  have harrive'' : arrive u C.new.1 = (C.old.2, v) := by
    change arrive u C.new.1 = (C.new.2, v) at harrive
    rw [hforward] at harrive
    exact harrive
  have hcomparison := forward_merge_tails_endpoint_dichotomy
    hOldCons hnewCons'' hOldSimple hold hswitch harrive'' hchanged''
  have hflip : v = flipAt u (C.new.1 / 3) :=
    changed_arrival_eq_flipAt harrive'' hchanged''
  rw [← hflip] at hcomparison
  exact ⟨v, hcomparison⟩

/-- A productive forward first contact cannot leave a strict unmatched suffix:
that suffix would expose a positive strict return to the start port of either
the returned trace or the old lead.  Therefore the two boundary ports agree. -/
theorem LeadReturnFirstContact.forward_changed_forces_boundary_eq
    {w : Wiring} {g e : Nat} {base after : Tongues}
    {lead fresh : List Passage}
    (C : LeadReturnFirstContact lead fresh)
    (hlead : PhysicalTrace w (g, base) lead (e, base))
    (hleadSimple : SwitchSimple lead)
    (hreturn : PhysicalTrace w (e, base) fresh (g, after))
    (hreturnSimple : SwitchSimple fresh)
    (hforward : C.new.2 = C.old.2)
    (hchanged :
      let data := C.contact_data hlead hleadSimple hreturn
      let u := Classical.choose data
      let v := Classical.choose (Classical.choose_spec data)
      v (C.new.1 / 3) ≠ u (C.new.1 / 3)) :
    g = e := by
  obtain ⟨v, hcomparison⟩ :=
    C.forward_changed_suffix_comparison
      hlead hleadSimple hreturn hforward hchanged
  rcases hcomparison with
      ⟨suffix, hnewAfter, htail⟩ |
      ⟨suffix, holdAfter, htail⟩
  · cases suffix with
    | nil =>
        cases htail
        rfl
    | cons passage rest =>
        have hsplit : fresh =
            (C.newBefore ++ C.new :: C.oldAfter) ++
              passage :: rest := by
          calc
            fresh = C.newBefore ++ C.new :: C.newAfter :=
              C.fresh_split
            _ = C.newBefore ++ C.new ::
                (C.oldAfter ++ passage :: rest) := by
              rw [hnewAfter]
            _ = (C.newBefore ++ C.new :: C.oldAfter) ++
                passage :: rest := by
              simp only [List.append_assoc, List.cons_append]
        have hfull := hreturn
        rw [hsplit] at hfull
        obtain ⟨middle, hprefix, hactualTail⟩ :=
          hfull.split_append
        have htailStart : e = passage.1 :=
          htail.head_arrive.1
        have hactualStart : middle.1 = passage.1 :=
          hactualTail.head_arrive.1
        have hmiddlePort : middle.1 = e :=
          hactualStart.trans htailStart.symm
        rcases middle with ⟨middlePort, middleState⟩
        simp only at hmiddlePort
        subst middlePort
        have hpositive :
            0 < (C.newBefore ++ C.new :: C.oldAfter).length := by
          simp only [List.length_append, List.length_cons]
          omega
        have hinside :
            (C.newBefore ++ C.new :: C.oldAfter).length <
              fresh.length := by
          have hlen := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons] at hlen ⊢
          omega
        exact (hreturn.no_strict_return_to_start_port_public
          hreturnSimple hpositive hinside hprefix.sound).elim
  · cases suffix with
    | nil =>
        cases htail
        rfl
    | cons passage rest =>
        have hsplit : lead =
            (C.oldBefore ++ C.old :: C.newAfter) ++
              passage :: rest := by
          calc
            lead = C.oldBefore ++ C.old :: C.oldAfter :=
              C.lead_split
            _ = C.oldBefore ++ C.old ::
                (C.newAfter ++ passage :: rest) := by
              rw [holdAfter]
            _ = (C.oldBefore ++ C.old :: C.newAfter) ++
                passage :: rest := by
              simp only [List.append_assoc, List.cons_append]
        have hfull := hlead
        rw [hsplit] at hfull
        obtain ⟨middle, hprefix, hactualTail⟩ :=
          hfull.split_append
        have htailStart : g = passage.1 :=
          htail.head_arrive.1
        have hactualStart : middle.1 = passage.1 :=
          hactualTail.head_arrive.1
        have hmiddlePort : middle.1 = g :=
          hactualStart.trans htailStart.symm
        rcases middle with ⟨middlePort, middleState⟩
        simp only at hmiddlePort
        subst middlePort
        have hpositive :
            0 < (C.oldBefore ++ C.old :: C.newAfter).length := by
          simp only [List.length_append, List.length_cons]
          omega
        have hinside :
            (C.oldBefore ++ C.old :: C.newAfter).length <
              lead.length := by
          have hlen := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons] at hlen ⊢
          omega
        exact (hlead.no_strict_return_to_start_port_public
          hleadSimple hpositive hinside hprefix.sound).elim
/-- A no-change arrival changes no coordinate at all once its contact
coordinate is unchanged. -/
theorem arrive_state_eq_of_contact_bit_eq
    {u v : Tongues} {p x : Nat}
    (harrive : arrive u p = (x, v))
    (hbit : v (p / 3) = u (p / 3)) :
    v = u := by
  unfold arrive at harrive
  by_cases hp : p % 3 = 0
  · rw [if_pos hp] at harrive
    exact (congrArg Prod.snd harrive).symm
  · rw [if_neg hp] at harrive
    have hv : v = pin u p :=
      (congrArg Prod.snd harrive).symm
    rw [hv] at hbit ⊢
    apply pin_of_agrees
    simpa [pin] using hbit.symm

/-- If the canonical contact literally re-enters the old passage in its
recorded orientation, determinism makes the two tails prefix-comparable.
A strict unmatched suffix would return one of the two simple traces to its
own start port, so the boundary ports must coincide. -/
theorem LeadReturnFirstContact.forward_same_forces_boundary_eq
    {w : Wiring} {g e : Nat} {base after : Tongues}
    {lead fresh : List Passage}
    (C : LeadReturnFirstContact lead fresh)
    (hlead : PhysicalTrace w (g, base) lead (e, base))
    (hleadSimple : SwitchSimple lead)
    (hreturn : PhysicalTrace w (e, base) fresh (g, after))
    (hreturnSimple : SwitchSimple fresh)
    (hsame : C.new = C.old) :
    g = e := by
  obtain ⟨u, v, _hbefore, hnewCons, harrive, hgrooved⟩ :=
    C.contact_data hlead hleadSimple hreturn
  have holdMem : C.old ∈ lead := by
    have hm : C.old ∈ C.oldBefore ++ C.old :: C.oldAfter :=
      List.mem_append_right _ List.mem_cons_self
    exact Eq.mp
      (congrArg (fun xs => C.old ∈ xs) C.lead_split.symm) hm
  have hold : arrive u C.old.1 = (C.old.2, u) :=
    groove_forward (hgrooved C.old holdMem)
  have harriveOld : arrive u C.old.1 = (C.old.2, v) := by
    rw [← hsame]
    exact harrive
  have hvu : v = u := by
    have hpairs := hold.symm.trans harriveOld
    exact (congrArg Prod.snd hpairs).symm
  subst v
  have holdPrefix := simple_grooved_trace_prefix_to_occurrence
    hlead C.lead_split hgrooved hleadSimple
  have hleadU := hlead.replay_grooved u hgrooved
  have hleadUSplit := hleadU
  rw [C.lead_split] at hleadUSplit
  obtain ⟨middle, hOldPrefix, hOldCons⟩ :=
    hleadUSplit.split_append
  have hmiddle : middle = (C.old.1, u) := by
    have h1 := hOldPrefix.sound
    have h2 := holdPrefix.1.sound
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  rw [hmiddle] at hOldCons
  have hnewCons'' : PhysicalTrace w (C.old.1, u)
      (C.old :: C.newAfter) (g, after) := by
    rw [← hsame]
    exact hnewCons
  rcases physicalTrace_prefix_comparable_with_endpoints
      hOldCons hnewCons'' with
      ⟨suffix, hright, htail⟩ |
      ⟨suffix, hleft, htail⟩
  · have hnewAfter : C.newAfter = C.oldAfter ++ suffix := by
      have ht := congrArg List.tail hright
      simpa using ht
    cases suffix with
    | nil =>
        cases htail
        rfl
    | cons passage rest =>
        have hsplit : fresh =
            (C.newBefore ++ C.new :: C.oldAfter) ++
              passage :: rest := by
          calc
            fresh = C.newBefore ++ C.new :: C.newAfter :=
              C.fresh_split
            _ = C.newBefore ++ C.new ::
                (C.oldAfter ++ passage :: rest) := by
              rw [hnewAfter]
            _ = (C.newBefore ++ C.new :: C.oldAfter) ++
                passage :: rest := by
              simp only [List.append_assoc, List.cons_append]
        have hfull := hreturn
        rw [hsplit] at hfull
        obtain ⟨middle, hprefix, hactualTail⟩ :=
          hfull.split_append
        have htailStart : e = passage.1 :=
          htail.head_arrive.1
        have hactualStart : middle.1 = passage.1 :=
          hactualTail.head_arrive.1
        have hmiddlePort : middle.1 = e :=
          hactualStart.trans htailStart.symm
        rcases middle with ⟨middlePort, middleState⟩
        simp only at hmiddlePort
        subst middlePort
        have hpositive :
            0 < (C.newBefore ++ C.new :: C.oldAfter).length := by
          simp only [List.length_append, List.length_cons]
          omega
        have hinside :
            (C.newBefore ++ C.new :: C.oldAfter).length <
              fresh.length := by
          have hlen := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons] at hlen ⊢
          omega
        exact (hreturn.no_strict_return_to_start_port_public
          hreturnSimple hpositive hinside hprefix.sound).elim
  · have holdAfter : C.oldAfter = C.newAfter ++ suffix := by
      have ht := congrArg List.tail hleft
      simpa using ht
    cases suffix with
    | nil =>
        cases htail
        rfl
    | cons passage rest =>
        have hsplit : lead =
            (C.oldBefore ++ C.old :: C.newAfter) ++
              passage :: rest := by
          calc
            lead = C.oldBefore ++ C.old :: C.oldAfter :=
              C.lead_split
            _ = C.oldBefore ++ C.old ::
                (C.newAfter ++ passage :: rest) := by
              rw [holdAfter]
            _ = (C.oldBefore ++ C.old :: C.newAfter) ++
                passage :: rest := by
              simp only [List.append_assoc, List.cons_append]
        have hfull := hlead
        rw [hsplit] at hfull
        obtain ⟨middle, hprefix, hactualTail⟩ :=
          hfull.split_append
        have htailStart : g = passage.1 :=
          htail.head_arrive.1
        have hactualStart : middle.1 = passage.1 :=
          hactualTail.head_arrive.1
        have hmiddlePort : middle.1 = g :=
          hactualStart.trans htailStart.symm
        rcases middle with ⟨middlePort, middleState⟩
        simp only at hmiddlePort
        subst middlePort
        have hpositive :
            0 < (C.oldBefore ++ C.old :: C.newAfter).length := by
          simp only [List.length_append, List.length_cons]
          omega
        have hinside :
            (C.oldBefore ++ C.old :: C.newAfter).length <
              lead.length := by
          have hlen := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons] at hlen ⊢
          omega
        exact (hlead.no_strict_return_to_start_port_public
          hleadSimple hpositive hinside hprefix.sound).elim

/-- If the two boundary ports coincide, the nonempty old lead is itself a
grooved closed cycle, hence gives an immediate one-vector tail. -/
theorem LeadReturnFirstContact.boundary_eq_one_vector_tail
    {w : Wiring} {g e : Nat} {base : Tongues}
    {lead fresh : List Passage}
    (C : LeadReturnFirstContact lead fresh)
    (hlead : PhysicalTrace w (g, base) lead (e, base))
    (hleadSimple : SwitchSimple lead)
    (hboundary : g = e) :
    ∃ T : RawOneVectorTail w (e, base), T.shift ≤ fresh.length := by
  have hcycle : PhysicalTrace w (e, base) lead (e, base) := by
    simpa [hboundary] using hlead
  have hgrooved : PassagesGrooved base lead :=
    hcycle.grooved_of_switchSimple hleadSimple
  have holdMem : C.old ∈ lead := by
    have hm : C.old ∈ C.oldBefore ++ C.old :: C.oldAfter :=
      List.mem_append_right _ List.mem_cons_self
    exact Eq.mp
      (congrArg (fun xs => C.old ∈ xs) C.lead_split.symm) hm
  have hnonempty : lead ≠ [] := by
    intro hempty
    have hnil : C.old ∈ ([] : List Passage) :=
      Eq.mp (congrArg
        (fun xs : List Passage => C.old ∈ xs) hempty) holdMem
    cases hnil
  refine ⟨{
    shift := 0
    port := e
    phase := base
    reached := by simp [stepN]
    all_time := hcycle.stable_grooved_cycle_all_time
      hnonempty hgrooved
  }, by simp⟩

/-- **Physical elimination of the support-contact residual.**  Every
canonical first common-switch contact between the stable old lead and the
simple returned prefix reaches a one-vector tail no later than the end of
that returned prefix.  No contact is assumed impossible.

Backward orientation closes immediately.  In forward orientation, a
productive contact is killed by the strict-return argument; a quiet contact
is equal or reversed by the physical groove lemma, reducing to the same two
cases. -/
theorem LeadReturnFirstContact.one_vector_tail
    {w : Wiring} {g e : Nat} {base after : Tongues}
    {lead fresh : List Passage}
    (C : LeadReturnFirstContact lead fresh)
    (hlead : PhysicalTrace w (g, base) lead (e, base))
    (hleadSimple : SwitchSimple lead)
    (hreturn : PhysicalTrace w (e, base) fresh (g, after))
    (hreturnSimple : SwitchSimple fresh)
    (hentry : w.link e = some g) :
    ∃ T : RawOneVectorTail w (e, base), T.shift ≤ fresh.length := by
  rcases C.exit_dichotomy hlead hleadSimple hreturn with
      hbackward | hforward
  · exact C.backward_one_vector_tail hlead hleadSimple
      hreturn hreturnSimple hentry hbackward
  · let data := C.contact_data hlead hleadSimple hreturn
    let u := Classical.choose data
    let dataU := Classical.choose_spec data
    let v := Classical.choose dataU
    have hspec := Classical.choose_spec dataU
    rcases hspec with ⟨_hbefore, _hnewCons, harrive, hgrooved⟩
    by_cases hchanged :
        v (C.new.1 / 3) ≠ u (C.new.1 / 3)
    · have hchangedChoice :
          (let selected :=
              C.contact_data hlead hleadSimple hreturn
           let selectedU := Classical.choose selected
           let selectedV :=
             Classical.choose (Classical.choose_spec selected)
           selectedV (C.new.1 / 3) ≠
             selectedU (C.new.1 / 3)) := by
        simpa only [data, u, dataU, v] using hchanged
      have hboundary :=
        C.forward_changed_forces_boundary_eq
          hlead hleadSimple hreturn hreturnSimple
            hforward hchangedChoice
      exact C.boundary_eq_one_vector_tail
        hlead hleadSimple hboundary
    · have hunchanged :
          v (C.new.1 / 3) = u (C.new.1 / 3) :=
        Classical.not_not.mp hchanged
      have hvu : v = u :=
        arrive_state_eq_of_contact_bit_eq harrive hunchanged
      have holdMem : C.old ∈ lead := by
        have hm : C.old ∈ C.oldBefore ++ C.old :: C.oldAfter :=
          List.mem_append_right _ List.mem_cons_self
        exact Eq.mp
          (congrArg (fun xs => C.old ∈ xs)
            C.lead_split.symm) hm
      have hold :
          arrive u C.old.2 = (C.old.1, u) :=
        hgrooved C.old holdMem
      have hnew :
          arrive u C.new.1 = (C.new.2, u) := by
        change arrive u C.new.1 = (C.new.2, v) at harrive
        rw [hvu] at harrive
        exact harrive
      rcases grooved_same_switch_passages_eq_or_reverse
          hold hnew C.same_switch with hsame | hreverse
      · have hboundary :=
          C.forward_same_forces_boundary_eq
            hlead hleadSimple hreturn hreturnSimple hsame
        exact C.boundary_eq_one_vector_tail
          hlead hleadSimple hboundary
      · have hbackward'' : C.new.2 = C.old.1 :=
          congrArg Prod.snd hreverse
        exact C.backward_one_vector_tail hlead hleadSimple
          hreturn hreturnSimple hentry hbackward''

/-- A one-vector tail contains at most one distinct restricted tongue vector. -/
theorem RawOneVectorTail.distinct_le_one
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (T : RawOneVectorTail w start)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (T.port, T.phase))).Nodup) :
    times.length ≤ 1 := by
  have hcover : NoveltyCoverOn w N (T.port, T.phase) times
      [VectorCount.restrict N T.phase] 0 := by
    refine ⟨[], by simp, ?_⟩
    intro d _hd
    obtain ⟨port, hrun⟩ := T.all_time d
    simp [restrictedTonguesAt, tonguesAt, hrun]
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

/-- The literal second-first-writer lead-contact residual has the same bounded
one-vector tail as its canonical first contact. -/
theorem SecondFirstWriterLeadContact.one_vector_tail
    {w : Wiring} {N g e k0 : Nat}
    {B : ManufacturedReflector w e g}
    {lead : List Passage}
    (D : SecondFirstWriterLeadContact w N g e k0 B lead)
    (hlead : PhysicalTrace w (g, B.baseState) lead
      (e, B.baseState))
    (hleadSimple : SwitchSimple lead)
    (hentry : w.link e = some g) :
    ∃ T : RawOneVectorTail w (e, B.baseState),
      T.shift ≤ D.returned.returnPath.length := by
  obtain ⟨C⟩ := leadReturnFirstContact_of_common_switch
    (lead := lead) (fresh := D.returned.returnPath)
    ⟨D.oldPassage, D.old_mem,
      D.newPassage, D.new_mem, D.same_switch⟩
  exact C.one_vector_tail hlead hleadSimple
    D.returned.returnPath_trace
      D.returned.returnPath_simple hentry

/-- A bounded one-vector tail reached during the second first-writer return
closes the productive arbitrary-start boundary at exactly N+4. -/
theorem productive_initial_boundary_N_add_four_of_present_writer_tail
    {w : Wiring} {N g e k0 : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (R : SecondFirstWriterGlobalReturn w N g e k0 B)
    (T : RawOneVectorTail w (e, B.baseState))
    (hwithin : T.shift ≤ R.returnPath.length)
    (times : List Nat)
    (hlive : ∀ k, k ∈ times →
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length + 1 ≤ N + 4 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let returned := T.shift
  let totalTravel := firstTravel + returned
  let history := VectorCount.restrict N original ::
    A.preservedTwoHistoryCore B N
  have hAatBase :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  have hreachA :
      stepN w firstTravel (g, A.baseState) =
        some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hreachTail :
      stepN w returned (e, A.activatedState) =
        some (T.port, T.phase) := by
    simpa [returned, hbase] using T.reached
  have hreachTotal :
      stepN w totalTravel (g, A.baseState) =
        some (T.port, T.phase) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachTail
  have hreturnPathLeExploration :
      R.returnPath.length ≤ B.exploration.length := by
    rw [R.returnPath_eq, List.length_take]
    exact Nat.min_le_right _ _
  have hreturnedLeExploration :
      returned ≤ B.exploration.length := by
    dsimp [returned]
    omega
  have hprefix : ∀ d, d ≤ totalTravel →
      restrictedTonguesAt w N (g, A.baseState) d ∈ history := by
    intro d hd
    by_cases hfirst : d ≤ firstTravel
    · apply List.mem_cons_of_mem
      apply A.mem_preservedTwoHistoryCore B
      apply Or.inl
      exact A.manufacturing_journey_mem_sharpHistory
        hA (by simpa [firstTravel] using hfirst)
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLeReturned : q ≤ returned := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hqLeJourney :
          q ≤ B.exploration.length + B.runway.length + 1 := by
        omega
      have hliveQ := stepN_prefix_some hqLeReturned hreachTail
      have hshift := tonguesAt_add_of_reaches hreachA hliveQ
      have hmRaw := B.manufacturing_journey_mem_sharpHistory
        (N := N) hB (j := q) hqLeJourney
      have hm : restrictedTonguesAt w N
          (e, A.activatedState) q ∈
            B.sharpConstructionHistory N := by
        simpa [hbase] using hmRaw
      have heq :
          restrictedTonguesAt w N (g, A.baseState) d =
            restrictedTonguesAt w N (e, A.activatedState) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      apply List.mem_cons_of_mem
      exact A.mem_preservedTwoHistoryCore B (Or.inr hm)
  have hboundary :
      VectorCount.restrict N T.phase ∈ history := by
    have hqLeJourney :
        returned ≤ B.exploration.length + B.runway.length + 1 := by
      omega
    have hmRaw := B.manufacturing_journey_mem_sharpHistory
      (N := N) hB (j := returned) hqLeJourney
    have hvector : restrictedTonguesAt w N
        (e, B.baseState) returned =
          VectorCount.restrict N T.phase := by
      simp [restrictedTonguesAt, tonguesAt, returned, T.reached]
    apply List.mem_cons_of_mem
    apply A.mem_preservedTwoHistoryCore B
    apply Or.inr
    rwa [hvector] at hmRaw
  have htail : ∀ tailTimes : List Nat,
      (∀ k, k ∈ tailTimes →
        (stepN w k (T.port, T.phase)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N
          (T.port, T.phase))).Nodup →
      tailTimes.length ≤ 1 := by
    intro tailTimes _htailLive htailNodup
    exact T.distinct_le_one tailTimes htailNodup
  have hlocalNodup :
      (times.map
        (restrictedTonguesAt w N
          (g, A.baseState))).Nodup :=
    (List.nodup_cons.mp hnd).2
  have hcover := boundary_history_then_direct_tail_cover
    hreachTotal history hprefix hboundary htail
      (by omega) times hlive hlocalNodup
  have hextra :
      VectorCount.restrict N original ∈ history :=
    List.mem_cons_self
  have hcount := novelty_cover_count_with_historical_extra
    (VectorCount.restrict N original) hcover hextra hnd
  have hcoreLength :
      (A.preservedTwoHistoryCore B N).length ≤ N + 3 :=
    A.preservedTwoHistoryCore_length_le_N_add_three
      hN B hbase hAatBase hpre
  have hhistoryLength : history.length ≤ N + 4 := by
    dsimp [history]
    omega
  omega

/-- The literal support-contact residual is itself bounded by N+4. -/
theorem SecondFirstWriterLeadContact.all_run_distinct_le_N_add_four
    {w : Wiring} {N g e k0 : Nat}
    {B : ManufacturedReflector w e g}
    {lead : List Passage}
    (D : SecondFirstWriterLeadContact w N g e k0 B lead)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (original : Tongues)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (hlead : PhysicalTrace w (g, B.baseState) lead
      (e, B.baseState))
    (hleadSimple : SwitchSimple lead)
    (hentry : w.link e = some g)
    (times : List Nat)
    (hlive : ∀ k, k ∈ times →
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length + 1 ≤ N + 4 := by
  obtain ⟨T, hwithin⟩ :=
    D.one_vector_tail hlead hleadSimple hentry
  exact productive_initial_boundary_N_add_four_of_present_writer_tail
    hN A B original hbase hA hB hpre D.returned
      T hwithin times hlive hnd

/-- **Closed present-second-writer branch at N+4.**  This replaces the former
assumption that the explicit support contact was impossible.  The cycle arm
uses the existing cycle theorem; the contact arm uses the physical
first-contact elimination and its bounded one-vector tail. -/
theorem productive_initial_boundary_N_add_four_or_support_contact_closed
    {w : Wiring} {N g e k0 : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hentry : w.link e = some g)
    (hstem : e = 3 * k0)
    (hk0 : k0 < N)
    (original base : Tongues)
    (hbaseFlip : base = flipAt original k0)
    (A : ManufacturedReflector w g e)
    (hAbase : A.baseState = base)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (hpresent : k0 ∈ B.constructionFirstWriterSwitches N)
    (lead : List Passage)
    (hlead : PhysicalTrace w (g, B.baseState) lead
      (e, B.baseState))
    (hleadSimple : SwitchSimple lead)
    (times : List Nat)
    (hlive : ∀ k, k ∈ times →
      (stepN w k (g, base)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N (g, base))).Nodup) :
    times.length + 1 ≤ N + 4 := by
  rcases productive_initial_boundary_N_add_four_or_support_contact
      hN hentry hstem hk0 original base hbaseFlip A hAbase B
        hbase hA hB hpre hpresent lead hlead hleadSimple
        times hlive hnd with hbound | hcontact
  · exact hbound
  · obtain ⟨D⟩ := hcontact
    have hliveA : ∀ k, k ∈ times →
        (stepN w k (g, A.baseState)).isSome := by
      simpa [hAbase] using hlive
    have hndA : (VectorCount.restrict N original ::
        times.map
          (restrictedTonguesAt w N
            (g, A.baseState))).Nodup := by
      simpa [hAbase] using hnd
    exact D.all_run_distinct_le_N_add_four
      hN A original hbase hA hB hpre hlead hleadSimple
        hentry times hliveA hndA
/-- Reusable name for the now-unconditional present-second-writer closure. -/
theorem productive_initial_boundary_N_add_four_of_present_writer
    {w : Wiring} {N g e k0 : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hentry : w.link e = some g)
    (hstem : e = 3 * k0)
    (hk0 : k0 < N)
    (original base : Tongues)
    (hbaseFlip : base = flipAt original k0)
    (A : ManufacturedReflector w g e)
    (hAbase : A.baseState = base)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (hpresent : k0 ∈ B.constructionFirstWriterSwitches N)
    (lead : List Passage)
    (hlead : PhysicalTrace w (g, B.baseState) lead
      (e, B.baseState))
    (hleadSimple : SwitchSimple lead)
    (times : List Nat)
    (hlive : ∀ k, k ∈ times →
      (stepN w k (g, base)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N (g, base))).Nodup) :
    times.length + 1 ≤ N + 4 :=
  productive_initial_boundary_N_add_four_or_support_contact_closed
    hN hentry hstem hk0 original base hbaseFlip A hAbase B
      hbase hA hB hpre hpresent lead hlead hleadSimple
        times hlive hnd



end GeneralN
