import TwoHistoryUnionCharge

/-!
# The productive initial switch in the second first-writer history

This file isolates one case of the arbitrary-start boundary problem.  The
initial productive switch is `k0`, its stem is `e = 3 * k0`, and the shifted
run starts at the other end `g` of the edge `e -- g`.  Suppose a second
manufactured reflector `B : ManufacturedReflector w e g` has `k0` among the
productive first writers of its switch-simple exploration.

The occurrence cannot be facing: productivity says that its represented
tongue changes.  It is therefore a trailing traversal, exits through the
stem `3 * k0 = e`, and the edge hypothesis sends it to the original global
port `g`.  The prefix through that occurrence is still switch-simple.

No counting conclusion is asserted here.  The remaining boundary task after
this result is exact: either identify the returned tongue vector with an
already represented vector, or provide a replayable simple lead from `g` to
the beginning of this prefix.  The final theorem records the latter condition
without hiding it.
-/

namespace GeneralN

/-- Exact physical certificate extracted when the productive initial switch
occurs among the second reflector's first productive writers. -/
structure SecondFirstWriterGlobalReturn
    (w : Wiring) (N g e k0 : Nat)
    (B : ManufacturedReflector w e g) where
  time : Nat
  entryPort : Nat
  before : Tongues
  after : Tongues
  firstWriter :
    time ∈ rawFirstWriterTimes w N (e, B.baseState) B.exploration.length
  writer_eq : rawWriterAt w (e, B.baseState) time = k0
  before_reach :
    stepN w time (e, B.baseState) = some (entryPort, before)
  after_reach :
    stepN w (time + 1) (e, B.baseState) = some (g, after)
  changed_exactly_k0 : after = flipAt before k0
  returnPath : List Passage
  returnPath_eq : returnPath = B.exploration.take (time + 1)
  returnPath_trace :
    PhysicalTrace w (e, B.baseState) returnPath (g, after)
  returnPath_simple : SwitchSimple returnPath
  reverse_entry_edge : w.link g = some e

/-- If `k0` appears in the second reflector's first-writer history, its
productive occurrence returns the train to the original global port `g`.

The assumptions are only the finite-switch condition needed to turn visible
productivity into a genuine local tongue change, the physical edge and stem
identities, and literal membership in B's first-writer list. -/
theorem second_first_writer_present_returns_global_start
    {w : Wiring} {N g e k0 : Nat}
    (hN : ∀ p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (hentry : w.link e = some g)
    (hstem : e = 3 * k0)
    (B : ManufacturedReflector w e g)
    (hpresent : k0 ∈
      (rawFirstWriterTimes w N (e, B.baseState)
        B.exploration.length).map
          (rawWriterAt w (e, B.baseState))) :
    Nonempty (SecondFirstWriterGlobalReturn w N g e k0 B) := by
  classical
  obtain ⟨time, htime, hwriter⟩ := List.mem_map.mp hpresent
  have htimeData := mem_rawFirstWriterTimes_iff.mp htime
  have htimeLt : time < B.exploration.length := htimeData.1
  have hfirst : RawFirstWriterAt w N (e, B.baseState) time :=
    htimeData.2
  obtain ⟨cur, next, hcur, hnext, hstep, hchanged⟩ :=
    rawProductiveAt_changes_writer hN hfirst.1
  have hrawWriter :
      rawWriterAt w (e, B.baseState) time = cur.1 / 3 := by
    simp [rawWriterAt, rawEntryAt, hcur]
  have hcurSwitch : cur.1 / 3 = k0 :=
    hrawWriter.symm.trans hwriter
  have hparts := step_some_parts hstep
  have harrive :
      arrive cur.2 cur.1 = (exitPort cur, next.2) := by
    unfold exitPort
    rw [hparts.2]
    unfold arrivedTongues
    cases arrive cur.2 cur.1
    rfl
  have htrailing := changed_arrival_is_trailing harrive hchanged
  have hexit : exitPort cur = e := by
    rw [htrailing.2.1, hcurSwitch]
    exact hstem.symm
  have hnextLink : w.link e = some next.1 := by
    simpa [hexit] using hparts.1
  have hnextPort : next.1 = g := by
    exact Option.some.inj (hnextLink.symm.trans hentry)
  have hnextEq : next = (g, next.2) :=
    Prod.ext hnextPort rfl
  have hflip : next.2 = flipAt cur.2 k0 := by
    have hlocal := changed_arrival_eq_flipAt harrive hchanged
    simpa [hcurSwitch] using hlocal
  let returnPath := B.exploration.take (time + 1)
  have htimeLe : time + 1 ≤ B.exploration.length := by omega
  have hreturnPathLength : returnPath.length = time + 1 := by
    simp [returnPath, htimeLe]
  have hdecompose :
      B.exploration = returnPath ++ B.exploration.drop (time + 1) := by
    dsimp [returnPath]
    exact (List.take_append_drop (time + 1) B.exploration).symm
  have hwhole := B.exploration_trace
  rw [hdecompose] at hwhole
  obtain ⟨middle, hprefixTrace, _hsuffixTrace⟩ :=
    hwhole.split_append
  have hmiddle : middle = next := by
    have hsound := hprefixTrace.sound
    rw [hreturnPathLength, hnext] at hsound
    exact (Option.some.inj hsound).symm
  subst middle
  have hsimple : SwitchSimple returnPath := by
    have hall := B.exploration_simple
    unfold SwitchSimple at hall ⊢
    rw [hdecompose] at hall
    simp only [List.map_append] at hall
    exact (List.nodup_append.mp hall).1
  have hreverse : w.link g = some e :=
    w.symm e g hentry
  exact ⟨{
    time := time
    entryPort := cur.1
    before := cur.2
    after := next.2
    firstWriter := htime
    writer_eq := hwriter
    before_reach := hcur
    after_reach := hnext.trans (congrArg some hnextEq)
    changed_exactly_k0 := hflip
    returnPath := returnPath
    returnPath_eq := rfl
    returnPath_trace :=
      Eq.mp (congrArg
        (fun finish =>
          PhysicalTrace w (e, B.baseState) returnPath finish)
        hnextEq) hprefixTrace
    returnPath_simple := hsimple
    reverse_entry_edge := hreverse
  }⟩

/-- The return certificate closes a stable simple cycle as soon as the
already-traversed lead from `g` to `e` is compatible with the returned
prefix and their concatenation is switch-simple.  This theorem deliberately
keeps those two remaining physical assumptions visible. -/
theorem SecondFirstWriterGlobalReturn.closes_stable_simple_cycle
    {w : Wiring} {N g e k0 : Nat}
    {B : ManufacturedReflector w e g}
    (R : SecondFirstWriterGlobalReturn w N g e k0 B)
    (initial : Tongues)
    (lead : List Passage)
    (hlead : PhysicalTrace w (g, initial) lead (e, B.baseState))
    (hsimple : SwitchSimple (lead ++ R.returnPath)) :
    PhysicalTrace w (g, initial) (lead ++ R.returnPath) (g, R.after) ∧
      PhysicalTrace w (g, R.after) (lead ++ R.returnPath) (g, R.after) ∧
      SwitchSimple (lead ++ R.returnPath) := by
  have htransient := hlead.append R.returnPath_trace
  have hgrooved := htransient.grooved_of_switchSimple hsimple
  have hstable := htransient.replay_grooved R.after hgrooved
  exact ⟨htransient, hstable, hsimple⟩

/-- A switch-simple lead into the second exploration gives a sharp physical
dichotomy.  Either it is switch-disjoint from the returned prefix, in which
case the concatenation is an early stable simple cycle, or the two pieces
name an explicit common switch.  Thus the only non-cycle residue is a
concrete support contact, not an unspecified failure of replay. -/
theorem SecondFirstWriterGlobalReturn.cycle_or_lead_contact
    {w : Wiring} {N g e k0 : Nat}
    {B : ManufacturedReflector w e g}
    (R : SecondFirstWriterGlobalReturn w N g e k0 B)
    (initial : Tongues)
    (lead : List Passage)
    (hlead : PhysicalTrace w (g, initial) lead (e, B.baseState))
    (hleadSimple : SwitchSimple lead) :
    (PhysicalTrace w (g, initial) (lead ++ R.returnPath) (g, R.after) ∧
      PhysicalTrace w (g, R.after) (lead ++ R.returnPath) (g, R.after) ∧
      SwitchSimple (lead ++ R.returnPath)) ∨
    (∃ oldPassage, oldPassage ∈ lead ∧
      ∃ newPassage, newPassage ∈ R.returnPath ∧
        passageSwitch oldPassage = passageSwitch newPassage) := by
  classical
  by_cases hcontact :
      ∃ oldPassage, oldPassage ∈ lead ∧
        ∃ newPassage, newPassage ∈ R.returnPath ∧
          passageSwitch oldPassage = passageSwitch newPassage
  · exact Or.inr hcontact
  · apply Or.inl
    have hsimple : SwitchSimple (lead ++ R.returnPath) := by
      have hreturnSimple := R.returnPath_simple
      unfold SwitchSimple at hleadSimple hreturnSimple ⊢
      rw [List.map_append]
      apply List.nodup_append.mpr
      refine ⟨hleadSimple, hreturnSimple, ?_⟩
      intro oldSwitch hOld newSwitch hNew hEq
      obtain ⟨oldPassage, hOldPassage, hOldEq⟩ :=
        List.mem_map.mp hOld
      obtain ⟨newPassage, hNewPassage, hNewEq⟩ :=
        List.mem_map.mp hNew
      apply hcontact
      refine ⟨oldPassage, hOldPassage,
        newPassage, hNewPassage, ?_⟩
      exact hOldEq.trans (hEq.trans hNewEq.symm)
    exact R.closes_stable_simple_cycle initial lead hlead hsimple

end GeneralN
