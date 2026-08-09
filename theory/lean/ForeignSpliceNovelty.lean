import TrackGlobalRepair
import TrackNoveltyCover

/-!
# Pointwise novelty of foreign candy splices

The eventual-periodicity proof for a changed-forward splice through the
candy of a manufactured flip reflector is assembled from explicit physical
traces.  This file records the stronger pointwise fact needed by the sharp
novelty argument: arbitrarily long grooved portions do not create arbitrarily
many tongue vectors.  A completion has one change of phase, and the
contact-repair case has two changes returning to its initial phase.

Everything is stated over raw `Wiring` / `stepN` dynamics.  No finiteness or
small-`N` argument is used.
-/

namespace GeneralN

private theorem mem_reverse_nat_foreign {x : Nat} {xs : List Nat} :
    x ∈ xs.reverse ↔ x ∈ xs := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih, or_comm]

private theorem nodup_reverse_nat_foreign {xs : List Nat}
    (hnd : xs.Nodup) : xs.reverse.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.reverse_cons]
      apply List.nodup_append.mpr
      refine ⟨ih hnd.2, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro hax
      apply hnd.1
      rw [← hax]
      exact mem_reverse_nat_foreign.mp ha

private theorem passagesGrooved_append
    {u : Tongues} {left right : List Passage}
    (hleft : PassagesGrooved u left)
    (hright : PassagesGrooved u right) :
    PassagesGrooved u (left ++ right) := by
  intro passage hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hleft passage hp
  · exact hright passage hp

/-- A grooved trace, one changing passage, and another grooved trace expose
only the two endpoint tongue vectors at every intermediate time. -/
theorem PhysicalTrace.one_change_prefix_tongues
    {w : Wiring} {startPort p x q finishPort : Nat}
    {u v : Tongues} {before after : List Passage}
    (hbefore : PhysicalTrace w (startPort, u) before (p, u))
    (hbeforeGrooved : PassagesGrooved u before)
    (hchange : PhysicalTrace w (p, u) [(p, x)] (q, v))
    (hafter : PhysicalTrace w (q, v) after (finishPort, v))
    (hafterGrooved : PassagesGrooved v after)
    {d : Nat} (hd : d <= before.length + 1 + after.length) :
    exists port phase,
      stepN w d (startPort, u) = some (port, phase) /\
        (phase = u \/ phase = v) := by
  by_cases hprefix : d <= before.length
  · obtain ⟨port, hrun⟩ :=
      hbefore.grooved_prefix_tongues u hbeforeGrooved hprefix
    exact ⟨port, u, hrun, Or.inl rfl⟩
  · let r := d - (before.length + 1)
    have hr : r <= after.length := by
      dsimp [r]
      omega
    have hdecomp : d = before.length + (1 + r) := by
      dsimp [r]
      omega
    obtain ⟨port, htail⟩ :=
      hafter.grooved_prefix_tongues v hafterGrooved hr
    have hone : stepN w 1 (p, u) = some (q, v) := by
      simpa using hchange.sound
    have hrest : stepN w (1 + r) (p, u) = some (port, v) := by
      rw [stepN_add, hone]
      exact htail
    refine ⟨port, v, ?_, Or.inr rfl⟩
    rw [hdecomp, stepN_add, hbefore.sound]
    exact hrest

/-- Two changing passages separated by grooved traces still expose only two
tongue vectors when the second change restores the first phase. -/
theorem PhysicalTrace.two_change_prefix_tongues
    {w : Wiring}
    {startPort p x q r y s finishPort : Nat}
    {u v : Tongues}
    {before middle after : List Passage}
    (hbefore : PhysicalTrace w (startPort, u) before (p, u))
    (hbeforeGrooved : PassagesGrooved u before)
    (hforward : PhysicalTrace w (p, u) [(p, x)] (q, v))
    (hmiddle : PhysicalTrace w (q, v) middle (r, v))
    (hmiddleGrooved : PassagesGrooved v middle)
    (hback : PhysicalTrace w (r, v) [(r, y)] (s, u))
    (hafter : PhysicalTrace w (s, u) after (finishPort, u))
    (hafterGrooved : PassagesGrooved u after)
    {d : Nat}
    (hd : d <= before.length + 1 + middle.length + 1 + after.length) :
    exists port phase,
      stepN w d (startPort, u) = some (port, phase) /\
        (phase = u \/ phase = v) := by
  by_cases hfirst : d <= before.length + 1 + middle.length
  · exact PhysicalTrace.one_change_prefix_tongues
      hbefore hbeforeGrooved hforward hmiddle hmiddleGrooved hfirst
  · let tailDepth := d - (before.length + 1 + middle.length + 1)
    have htailDepth : tailDepth <= after.length := by
      dsimp [tailDepth]
      omega
    have hdecomp : d =
        (before.length + 1 + middle.length) + (1 + tailDepth) := by
      dsimp [tailDepth]
      omega
    obtain ⟨port, htail⟩ :=
      hafter.grooved_prefix_tongues u hafterGrooved htailDepth
    have hfirstRun : stepN w (before.length + 1 + middle.length)
        (startPort, u) = some (r, v) := by
      rw [show before.length + 1 + middle.length =
          before.length + (1 + middle.length) by omega,
        stepN_add, hbefore.sound]
      simp only [Option.bind_some]
      have hone : stepN w 1 (p, u) = some (q, v) := by
        simpa using hforward.sound
      rw [stepN_add, hone]
      exact hmiddle.sound
    have hbackOne : stepN w 1 (r, v) = some (s, u) := by
      simpa using hback.sound
    have hrest : stepN w (1 + tailDepth) (r, v) =
        some (port, u) := by
      rw [stepN_add, hbackOne]
      exact htail
    refine ⟨port, u, ?_, Or.inl rfl⟩
    rw [hdecomp, stepN_add, hfirstRun]
    exact hrest

/-- Any pointwise two-phase description gives a one-vector novelty cover
once the first phase is already historical. -/
theorem noveltyCoverOn_one_fresh_of_two_phases
    {w : Wiring} {N : Nat} {startPort : Nat} {u v : Tongues}
    {times : List Nat} {history : List (List Bool)}
    (hphase : ∀ d, d ∈ times → ∃ port phase,
      stepN w d (startPort, u) = some (port, phase) /\
        (phase = u \/ phase = v))
    (hu : VectorCount.restrict N u ∈ history) :
    NoveltyCoverOn w N (startPort, u) times history 1 := by
  refine ⟨[VectorCount.restrict N v], by simp, ?_⟩
  intro d hd
  obtain ⟨port, phase, hrun, hphaseEq⟩ := hphase d hd
  have hvector : restrictedTonguesAt w N (startPort, u) d =
      VectorCount.restrict N phase := by
    simp [restrictedTonguesAt, tonguesAt, hrun]
  rw [hvector]
  rcases hphaseEq with rfl | rfl
  · exact List.mem_append_left _ hu
  · exact List.mem_append_right _ (by simp)

private theorem stepN_mul_period_foreign
    {w : Wiring} {start : Nat × Tongues} {period : Nat}
    (hperiod : stepN w period start = some start) :
    ∀ q, stepN w (q * period) start = some start := by
  intro q
  induction q with
  | zero => simp [stepN]
  | succ q ih =>
      have hlen : (q + 1) * period = q * period + period := by
        simp [Nat.add_mul]
      rw [hlen, stepN_add, ih]
      exact hperiod

/-- A two-phase description of one positive period extends pointwise to the
whole infinite periodic run. -/
theorem periodic_two_phase_prefix_tongues
    {w : Wiring} {startPort : Nat} {u v : Tongues} {period : Nat}
    (hpositive : 0 < period)
    (hperiod : stepN w period (startPort, u) =
      some (startPort, u))
    (hwindow : ∀ d, d <= period → ∃ port phase,
      stepN w d (startPort, u) = some (port, phase) ∧
        (phase = u ∨ phase = v)) :
    ∀ d, ∃ port phase,
      stepN w d (startPort, u) = some (port, phase) ∧
        (phase = u ∨ phase = v) := by
  intro d
  let q := d / period
  let r := d % period
  have hr : r <= period := Nat.le_of_lt (Nat.mod_lt d hpositive)
  obtain ⟨port, phase, hlocal, hphase⟩ := hwindow r hr
  have hdecomp : d = q * period + r := by
    dsimp [q, r]
    have h := Nat.mod_add_div d period
    rw [Nat.mul_comm period (d / period)] at h
    omega
  refine ⟨port, phase, ?_, hphase⟩
  rw [hdecomp, stepN_add,
    stepN_mul_period_foreign hperiod q]
  exact hlocal

/-! ## The approach-foreign candy splice -/

/-- **Pointwise phase law for the approach-foreign candy splice.**

The old candy completion first carries the newly installed tongue vector and
then latches the old reflector action.  The reverse runway, fresh approach,
and final contact all carry that doubly-latched vector unchanged.  Thus the
entire explicit lead uses only two complete tongue vectors, independently of
the lengths of the three routes.

`happroachGrooved` is available from the changed-forward construction.  The
older periodicity theorem did not need to retain it in its interface, but a
pointwise novelty statement necessarily does. -/
theorem manufactured_flip_candy_splice_approach_foreign_two_phases
    {w : Wiring} {g e outside entry mouth returnPort : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {oldPrefix oldTail approach : List Passage}
    (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (htail : PhysicalTrace w (outside, state) oldTail
      ((ManufacturedReflector.flip R).orientedFinish state, state))
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (_hentryBranch : entry % 3 ≠ 0)
    {old : Passage} (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨
      (entry, mouth) = (old.2, old.1))
    (hentryGrooved : arrive state entry = (mouth, state))
    (happroach : PhysicalTrace w (g, state) approach
      (returnPort, state))
    (happroachGrooved : PassagesGrooved state approach)
    (happroachForeignNew : ∀ passage ∈ approach,
      passageSwitch passage ≠ mouth / 3)
    (happroachForeignOld : ∀ passage ∈ approach,
      passageSwitch passage ≠ R.actionSwitch)
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    {d : Nat}
    (hd : d <= oldTail.length + R.runway.length +
      approach.length + 2) :
    ∃ port phase,
      stepN w d (outside, flipAt state (mouth / 3)) =
          some (port, phase) ∧
        (phase = flipAt state (mouth / 3) ∨
          phase = flipAt (flipAt state (mouth / 3))
            R.actionSwitch) := by
  let finish := (ManufacturedReflector.flip R).orientedFinish state
  let completion := oldTail ++
    ((finish, R.mouth) :: reversePassages R.runway)
  let newState := flipAt state (mouth / 3)
  let bothState := flipAt newState R.actionSwitch

  have hentryNew : entry / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state entry
    rw [hentryGrooved] at hs
    exact hs.symm
  have hentryOld : entry / 3 ≠ R.actionSwitch :=
    R.candy_entry_foreign_action hold horientation
  have hnewOld : mouth / 3 ≠ R.actionSwitch := by
    intro hEq
    exact hentryOld (hentryNew.trans hEq)
  have hreturnNew : returnPort / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state returnPort
    rw [hcrossed] at hs
    exact hs.symm
  have hreturnOld : returnPort / 3 ≠ R.actionSwitch := by
    rw [hreturnNew]
    exact hnewOld
  have hcomm :
      flipAt (flipAt state R.actionSwitch) (mouth / 3) =
        bothState := by
    dsimp [bothState, newState]
    exact flipAt_comm (Ne.symm hnewOld)

  have hcompletionData := R.candy_completion_foreign state hpaths
    hsplit htail hnotRunway hold horientation
  change PhysicalTrace w (outside, state) completion
      (g, flipAt state R.actionSwitch) ∧
    (∀ passage ∈ completion,
      passageSwitch passage ≠ entry / 3) at hcompletionData
  have hcompletionForeignNew : ∀ passage ∈ completion,
      passageSwitch passage ≠ mouth / 3 := by
    intro passage hp hEq
    exact hcompletionData.2 passage hp (hEq.trans hentryNew.symm)
  have htailForeignNew : ∀ passage ∈ oldTail,
      passageSwitch passage ≠ mouth / 3 := by
    intro passage hp
    exact hcompletionForeignNew passage
      (List.mem_append_left _ hp)
  have hbefore := htail.flip_unvisited htailForeignNew
  change PhysicalTrace w (outside, newState) oldTail
    (finish, newState) at hbefore
  have hrouteTrace :=
    (ManufacturedReflector.flip R).orientedRoute_trace state hpaths
  have hrouteGrooved : PassagesGrooved state
      ((ManufacturedReflector.flip R).orientedRoute state) :=
    hrouteTrace.grooved_of_switchSimple
      ((ManufacturedReflector.flip R).orientedRoute_simple state)
  have htailGrooved : PassagesGrooved state oldTail := by
    intro passage hp
    exact hrouteGrooved passage (by
      rw [hsplit]
      exact List.mem_append_right oldPrefix
        (List.mem_cons_of_mem _ hp))
  have hbeforeGrooved : PassagesGrooved newState oldTail := by
    dsimp [newState]
    exact grooved_after_flip_other htailGrooved htailForeignNew

  have hreturn := R.oriented_return_trace state hpaths
  change PhysicalTrace w (finish, state)
    ((finish, R.mouth) :: reversePassages R.runway)
    (g, flipAt state R.actionSwitch) at hreturn
  cases hreturn with
  | @cons _ _ next _ after _ _ harrive hlink tail =>
      have hafterEq : after = flipAt state R.actionSwitch := by
        have hlocal := R.oriented_finish_arrive state
        rw [harrive] at hlocal
        exact congrArg Prod.snd hlocal
      subst after
      have hchangeOld : PhysicalTrace w (finish, state)
          [(finish, R.mouth)]
          (next, flipAt state R.actionSwitch) :=
        PhysicalTrace.cons harrive hlink (PhysicalTrace.nil _)
      have hchangeForeignNew : ∀ passage ∈ [(finish, R.mouth)],
          passageSwitch passage ≠ mouth / 3 := by
        intro passage hp
        simp only [List.mem_singleton] at hp
        subst passage
        apply hcompletionForeignNew (finish, R.mouth)
        apply List.mem_append_right oldTail
        exact List.mem_cons_self
      have hchange := hchangeOld.flip_unvisited hchangeForeignNew
      rw [hcomm] at hchange
      change PhysicalTrace w (finish, newState) [(finish, R.mouth)]
        (next, bothState) at hchange

      have hreverseForeignNew : ∀ passage ∈ reversePassages R.runway,
          passageSwitch passage ≠ mouth / 3 := by
        intro passage hp
        apply hcompletionForeignNew passage
        apply List.mem_append_right oldTail
        exact List.mem_cons_of_mem _ hp
      have hreverseTrace := tail.flip_unvisited hreverseForeignNew
      rw [hcomm] at hreverseTrace
      change PhysicalTrace w (next, bothState)
        (reversePassages R.runway) (g, bothState) at hreverseTrace
      have hrunwaySimple :=
        (ManufacturedReflector.flip R).runway_simple
      have hreverseSimple : SwitchSimple (reversePassages R.runway) := by
        unfold SwitchSimple at hrunwaySimple ⊢
        rw [map_passageSwitch_reversePassages R.runwayTrace]
        exact nodup_reverse_nat_foreign hrunwaySimple
      have hreverseGrooved :
          PassagesGrooved bothState (reversePassages R.runway) :=
        hreverseTrace.grooved_of_switchSimple hreverseSimple

      have happroachNew :=
        happroach.flip_unvisited happroachForeignNew
      have happroachBoth :=
        happroachNew.flip_unvisited happroachForeignOld
      change PhysicalTrace w (g, bothState) approach
        (returnPort, bothState) at happroachBoth
      have happroachGroovedNew : PassagesGrooved newState approach := by
        dsimp [newState]
        exact grooved_after_flip_other happroachGrooved
          happroachForeignNew
      have happroachGroovedBoth :
          PassagesGrooved bothState approach := by
        dsimp [bothState]
        exact grooved_after_flip_other happroachGroovedNew
          happroachForeignOld

      have hback := arrive_back state returnPort
      rw [hcrossed] at hback
      have hcontactNew : arrive newState returnPort =
          (mouth, newState) := by
        dsimp [newState]
        exact groove_forward hback
      have hcontactBoth := arrive_flip_other hcontactNew hreturnOld
      have hcontactTrace : PhysicalTrace w
          (returnPort, bothState) [(returnPort, mouth)]
          (outside, bothState) :=
        PhysicalTrace.cons hcontactBoth hmouthLink (PhysicalTrace.nil _)
      have hcontactGrooved :
          PassagesGrooved bothState [(returnPort, mouth)] := by
        intro passage hp
        simp only [List.mem_singleton] at hp
        subst passage
        have hg := arrive_back bothState returnPort
        rw [hcontactBoth] at hg
        exact hg

      have hafterTrace :=
        (hreverseTrace.append happroachBoth).append hcontactTrace
      have hafterGrooved : PassagesGrooved bothState
          ((reversePassages R.runway ++ approach) ++
            [(returnPort, mouth)]) :=
        passagesGrooved_append
          (passagesGrooved_append hreverseGrooved
            happroachGroovedBoth)
          hcontactGrooved
      have hphase := PhysicalTrace.one_change_prefix_tongues
        hbefore hbeforeGrooved hchange hafterTrace hafterGrooved
        (d := d) (by
          simp only [List.length_append, List.length_cons,
            List.length_nil, reversePassages_length]
          omega)
      simpa [newState, bothState] using hphase

/-- The approach-foreign splice contributes at most one restricted tongue
vector beyond its initial vector, regardless of route length. -/
theorem manufactured_flip_candy_splice_approach_foreign_one_novelty
    {w : Wiring} {g e outside entry mouth returnPort : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {oldPrefix oldTail approach : List Passage}
    (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (htail : PhysicalTrace w (outside, state) oldTail
      ((ManufacturedReflector.flip R).orientedFinish state, state))
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (hentryBranch : entry % 3 ≠ 0)
    {old : Passage} (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨
      (entry, mouth) = (old.2, old.1))
    (hentryGrooved : arrive state entry = (mouth, state))
    (happroach : PhysicalTrace w (g, state) approach
      (returnPort, state))
    (happroachGrooved : PassagesGrooved state approach)
    (happroachForeignNew : ∀ passage ∈ approach,
      passageSwitch passage ≠ mouth / 3)
    (happroachForeignOld : ∀ passage ∈ approach,
      passageSwitch passage ≠ R.actionSwitch)
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (N : Nat) (history : List (List Bool))
    (hinitial : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history)
    (times : List Nat)
    (htimes : ∀ d ∈ times,
      d <= oldTail.length + R.runway.length + approach.length + 2) :
    NoveltyCoverOn w N (outside, flipAt state (mouth / 3))
      times history 1 := by
  apply noveltyCoverOn_one_fresh_of_two_phases
    (v := flipAt (flipAt state (mouth / 3)) R.actionSwitch)
  · intro d hd
    exact manufactured_flip_candy_splice_approach_foreign_two_phases
      R state hpaths hsplit htail hnotRunway hentryBranch hold
      horientation hentryGrooved happroach happroachGrooved
      happroachForeignNew happroachForeignOld hcrossed hmouthLink
      (htimes d hd)
  · exact hinitial

/-! ## The approach-contact candy splice -/

/-- **Pointwise phase law for the approach-contact candy splice.**

The completion latches the old reflector action.  The fresh approach then
reaches its first trailing visit to that action, which repairs it.  Before and
after those two events every traversed passage is grooved.  Consequently the
entire explicit period uses only the initial newly-spliced vector and the
doubly-latched vector, even though the completion and approach may be
arbitrarily long. -/
theorem manufactured_flip_candy_splice_approach_contact_two_phases
    {w : Wiring} {g e outside entry mouth returnPort : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {oldPrefix oldTail approach : List Passage}
    (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (htail : PhysicalTrace w (outside, state) oldTail
      ((ManufacturedReflector.flip R).orientedFinish state, state))
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (hentryBranch : entry % 3 ≠ 0)
    {old : Passage} (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨
      (entry, mouth) = (old.2, old.1))
    (hentryGrooved : arrive state entry = (mouth, state))
    (happroach : PhysicalTrace w (g, state) approach
      (returnPort, state))
    (happroachGrooved : PassagesGrooved state approach)
    (happroachForeignNew : ∀ passage ∈ approach,
      passageSwitch passage ≠ mouth / 3)
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (harms : entry ≠ returnPort)
    (hcontact : ∃ passage ∈ approach,
      passageSwitch passage = R.actionSwitch)
    {d : Nat}
    (hd : d <= oldTail.length + R.runway.length +
      approach.length + 2) :
    ∃ port phase,
      stepN w d (outside, flipAt state (mouth / 3)) =
          some (port, phase) ∧
        (phase = flipAt state (mouth / 3) ∨
          phase = flipAt (flipAt state (mouth / 3))
            R.actionSwitch) := by
  let finish := (ManufacturedReflector.flip R).orientedFinish state
  let completion := oldTail ++
    ((finish, R.mouth) :: reversePassages R.runway)
  let newState := flipAt state (mouth / 3)
  let bothState := flipAt newState R.actionSwitch

  have hentryNew : entry / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state entry
    rw [hentryGrooved] at hs
    exact hs.symm
  have hentryOld : entry / 3 ≠ R.actionSwitch :=
    R.candy_entry_foreign_action hold horientation
  have hnewOld : mouth / 3 ≠ R.actionSwitch := by
    intro hEq
    exact hentryOld (hentryNew.trans hEq)
  have hreturnNew : returnPort / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state returnPort
    rw [hcrossed] at hs
    exact hs.symm
  have hcomm :
      flipAt (flipAt state R.actionSwitch) (mouth / 3) =
        bothState := by
    dsimp [bothState, newState]
    exact flipAt_comm (Ne.symm hnewOld)

  have hcompletionData := R.candy_completion_foreign state hpaths
    hsplit htail hnotRunway hold horientation
  change PhysicalTrace w (outside, state) completion
      (g, flipAt state R.actionSwitch) ∧
    (∀ passage ∈ completion,
      passageSwitch passage ≠ entry / 3) at hcompletionData
  have hcompletionForeignNew : ∀ passage ∈ completion,
      passageSwitch passage ≠ mouth / 3 := by
    intro passage hp hEq
    exact hcompletionData.2 passage hp (hEq.trans hentryNew.symm)
  have htailForeignNew : ∀ passage ∈ oldTail,
      passageSwitch passage ≠ mouth / 3 := by
    intro passage hp
    exact hcompletionForeignNew passage
      (List.mem_append_left _ hp)
  have hbeforeTrace := htail.flip_unvisited htailForeignNew
  change PhysicalTrace w (outside, newState) oldTail
    (finish, newState) at hbeforeTrace
  have hrouteTrace :=
    (ManufacturedReflector.flip R).orientedRoute_trace state hpaths
  have hrouteGrooved : PassagesGrooved state
      ((ManufacturedReflector.flip R).orientedRoute state) :=
    hrouteTrace.grooved_of_switchSimple
      ((ManufacturedReflector.flip R).orientedRoute_simple state)
  have htailGrooved : PassagesGrooved state oldTail := by
    intro passage hp
    exact hrouteGrooved passage (by
      rw [hsplit]
      exact List.mem_append_right oldPrefix
        (List.mem_cons_of_mem _ hp))
  have hbeforeGrooved : PassagesGrooved newState oldTail := by
    dsimp [newState]
    exact grooved_after_flip_other htailGrooved htailForeignNew

  have hreturn := R.oriented_return_trace state hpaths
  change PhysicalTrace w (finish, state)
    ((finish, R.mouth) :: reversePassages R.runway)
    (g, flipAt state R.actionSwitch) at hreturn
  cases hreturn with
  | @cons _ _ next _ afterReturn _ _ harriveReturn hlinkReturn
      reverseTrace =>
      have hafterReturn :
          afterReturn = flipAt state R.actionSwitch := by
        have hlocal := R.oriented_finish_arrive state
        rw [harriveReturn] at hlocal
        exact congrArg Prod.snd hlocal
      subst afterReturn
      have hchangeOld : PhysicalTrace w (finish, state)
          [(finish, R.mouth)]
          (next, flipAt state R.actionSwitch) :=
        PhysicalTrace.cons harriveReturn hlinkReturn
          (PhysicalTrace.nil _)
      have hchangeForeignNew : ∀ passage ∈ [(finish, R.mouth)],
          passageSwitch passage ≠ mouth / 3 := by
        intro passage hp
        simp only [List.mem_singleton] at hp
        subst passage
        apply hcompletionForeignNew (finish, R.mouth)
        apply List.mem_append_right oldTail
        exact List.mem_cons_self
      have hfirstChange :=
        hchangeOld.flip_unvisited hchangeForeignNew
      rw [hcomm] at hfirstChange
      change PhysicalTrace w (finish, newState) [(finish, R.mouth)]
        (next, bothState) at hfirstChange

      have hreverseForeignNew : ∀ passage ∈ reversePassages R.runway,
          passageSwitch passage ≠ mouth / 3 := by
        intro passage hp
        apply hcompletionForeignNew passage
        apply List.mem_append_right oldTail
        exact List.mem_cons_of_mem _ hp
      have hreverseTrace :=
        reverseTrace.flip_unvisited hreverseForeignNew
      rw [hcomm] at hreverseTrace
      change PhysicalTrace w (next, bothState)
        (reversePassages R.runway) (g, bothState) at hreverseTrace
      have hrunwaySimple :=
        (ManufacturedReflector.flip R).runway_simple
      have hreverseSimple : SwitchSimple (reversePassages R.runway) := by
        unfold SwitchSimple at hrunwaySimple ⊢
        rw [map_passageSwitch_reversePassages R.runwayTrace]
        exact nodup_reverse_nat_foreign hrunwaySimple
      have hreverseGrooved :
          PassagesGrooved bothState (reversePassages R.runway) :=
        hreverseTrace.grooved_of_switchSimple hreverseSimple

      have happroachNew :=
        happroach.flip_unvisited happroachForeignNew
      change PhysicalTrace w (g, newState) approach
        (returnPort, newState) at happroachNew
      have happroachGroovedNew : PassagesGrooved newState approach := by
        dsimp [newState]
        exact grooved_after_flip_other happroachGrooved
          happroachForeignNew
      have hbackContact := arrive_back state returnPort
      rw [hcrossed] at hbackContact
      have hcontactNew : arrive newState returnPort =
          (mouth, newState) := by
        dsimp [newState]
        exact groove_forward hbackContact
      have hcontactTraceNew : PhysicalTrace w
          (returnPort, newState) [(returnPort, mouth)]
          (outside, newState) :=
        PhysicalTrace.cons hcontactNew hmouthLink (PhysicalTrace.nil _)
      have hcontactGroovedNew :
          PassagesGrooved newState [(returnPort, mouth)] := by
        intro passage hp
        simp only [List.mem_singleton] at hp
        subst passage
        have hg := arrive_back newState returnPort
        rw [hcontactNew] at hg
        exact hg

      obtain ⟨before, target, after, happSplit, hbeforeForeignOld,
          htargetSwitch⟩ :=
        exists_first_satisfying_split
          (fun passage => passageSwitch passage = R.actionSwitch)
          approach hcontact
      have htargetMem : target ∈ approach := by
        rw [happSplit]
        exact List.mem_append_right before List.mem_cons_self
      have happroachNew' := happroachNew
      rw [happSplit] at happroachNew'
      obtain ⟨middleConfig, hbeforeRaw, hrest⟩ :=
        happroachNew'.split_append
      have hmiddlePort : middleConfig.1 = target.1 :=
        hrest.head_arrive.1
      have hbeforeGroovedNew : PassagesGrooved newState before := by
        intro passage hp
        exact happroachGroovedNew passage (by
          rw [happSplit]
          exact List.mem_append_left _ hp)
      have hprefix : PhysicalTrace w (g, newState) before
          (target.1, newState) := by
        have hreplay := hbeforeRaw.replay_grooved newState
          hbeforeGroovedNew
        simpa [hmiddlePort] using hreplay
      have hmiddleEq : middleConfig = (target.1, newState) := by
        exact Option.some.inj
          (hbeforeRaw.sound.symm.trans hprefix.sound)
      subst middleConfig
      have hstem := happroach.passage_stem_endpoint target htargetMem
      rcases target with ⟨p, x⟩
      simp only [passageSwitch] at htargetSwitch
      change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
      have hpNotStem : p ≠ 3 * (p / 3) := by
        intro hpStem
        apply R.facing_approach_to_candy_splice_impossible state hpaths
          hsplit hnotRunway hentryBranch happroach happroachGrooved
          happroachForeignNew hcrossed harms
          (target := (p, x)) htargetMem
        · simpa [passageSwitch] using htargetSwitch
        · omega
      have hxStem : x = 3 * (p / 3) := hstem.resolve_left hpNotStem
      have hxMouth : x = R.mouth := by
        have hm := R.mouth_is_stem
        unfold ManufacturedFlipReflector.actionSwitch at htargetSwitch
        omega
      clear hxStem
      subst x
      have htargetGroove : arrive newState R.mouth =
          (p, newState) :=
        happroachGroovedNew (p, R.mouth) htargetMem
      have hforward : arrive newState p = (R.mouth, newState) :=
        groove_forward htargetGroove
      have hpbranch : p % 3 ≠ 0 := by
        intro hpmod
        have hpEq : p = 3 * (p / 3) := by omega
        exact hpNotStem hpEq

      cases hrest with
      | @cons _ _ q _ targetAfter _ _ harriveTarget hlinkTarget
          afterTrace =>
          have htargetAfter : targetAfter = newState := by
            have hEq := hforward.symm.trans harriveTarget
            exact (congrArg Prod.snd hEq).symm
          subst targetAfter
          have hprefixBoth :=
            hprefix.flip_unvisited hbeforeForeignOld
          change PhysicalTrace w (g, bothState) before
            (p, bothState) at hprefixBoth
          have hprefixGroovedBoth :
              PassagesGrooved bothState before := by
            dsimp [bothState]
            exact grooved_after_flip_other hbeforeGroovedNew
              hbeforeForeignOld
          have hmiddleTrace := hreverseTrace.append hprefixBoth
          have hmiddleGrooved : PassagesGrooved bothState
              (reversePassages R.runway ++ before) :=
            passagesGrooved_append hreverseGrooved
              hprefixGroovedBoth

          have hrepairArrive : arrive bothState p =
              (R.mouth, newState) := by
            have hrepair :=
              flipped_passage_forward_trailing hforward hpbranch
            dsimp [bothState]
            simpa [htargetSwitch] using hrepair
          have hrepairTrace : PhysicalTrace w (p, bothState)
              [(p, R.mouth)] (q, newState) :=
            PhysicalTrace.cons hrepairArrive hlinkTarget
              (PhysicalTrace.nil _)

          have hafterGroovedNew : PassagesGrooved newState after := by
            intro passage hp
            exact happroachGroovedNew passage (by
              rw [happSplit]
              exact List.mem_append_right before
                (List.mem_cons_of_mem _ hp))
          have hafterFullTrace :=
            afterTrace.append hcontactTraceNew
          have hafterFullGrooved : PassagesGrooved newState
              (after ++ [(returnPort, mouth)]) :=
            passagesGrooved_append hafterGroovedNew
              hcontactGroovedNew

          have hphase := PhysicalTrace.two_change_prefix_tongues
            hbeforeTrace hbeforeGrooved hfirstChange hmiddleTrace
            hmiddleGrooved hrepairTrace hafterFullTrace
            hafterFullGrooved (d := d) (by
              simp only [List.length_append, List.length_cons,
                List.length_nil, reversePassages_length]
              have happLength : approach.length =
                  before.length + 1 + after.length := by
                have hlen := congrArg List.length happSplit
                simp only [List.length_append, List.length_cons] at hlen
                omega
              omega)
          simpa [newState, bothState] using hphase

/-- The approach-contact splice likewise contributes at most one restricted
tongue vector beyond its initial vector.  The long damaged repair is therefore
novelty-constant, not merely eventually periodic. -/
theorem manufactured_flip_candy_splice_approach_contact_one_novelty
    {w : Wiring} {g e outside entry mouth returnPort : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {oldPrefix oldTail approach : List Passage}
    (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (htail : PhysicalTrace w (outside, state) oldTail
      ((ManufacturedReflector.flip R).orientedFinish state, state))
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (hentryBranch : entry % 3 ≠ 0)
    {old : Passage} (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨
      (entry, mouth) = (old.2, old.1))
    (hentryGrooved : arrive state entry = (mouth, state))
    (happroach : PhysicalTrace w (g, state) approach
      (returnPort, state))
    (happroachGrooved : PassagesGrooved state approach)
    (happroachForeignNew : ∀ passage ∈ approach,
      passageSwitch passage ≠ mouth / 3)
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (harms : entry ≠ returnPort)
    (hcontact : ∃ passage ∈ approach,
      passageSwitch passage = R.actionSwitch)
    (N : Nat) (history : List (List Bool))
    (hinitial : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history)
    (times : List Nat)
    (htimes : ∀ d ∈ times,
      d <= oldTail.length + R.runway.length + approach.length + 2) :
    NoveltyCoverOn w N (outside, flipAt state (mouth / 3))
      times history 1 := by
  apply noveltyCoverOn_one_fresh_of_two_phases
    (v := flipAt (flipAt state (mouth / 3)) R.actionSwitch)
  · intro d hd
    exact manufactured_flip_candy_splice_approach_contact_two_phases
      R state hpaths hsplit htail hnotRunway hentryBranch hold
      horientation hentryGrooved happroach happroachGrooved
      happroachForeignNew hcrossed hmouthLink harms hcontact
      (htimes d hd)
  · exact hinitial

/-- The contact-repair period returns to its initial configuration, so the
two-vector phase law holds at every future time, not just in the first macro
traversal. -/
theorem manufactured_flip_candy_splice_approach_contact_all_two_phases
    {w : Wiring} {g e outside entry mouth returnPort : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {oldPrefix oldTail approach : List Passage}
    (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (htail : PhysicalTrace w (outside, state) oldTail
      ((ManufacturedReflector.flip R).orientedFinish state, state))
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (hentryBranch : entry % 3 ≠ 0)
    {old : Passage} (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨
      (entry, mouth) = (old.2, old.1))
    (hentryGrooved : arrive state entry = (mouth, state))
    (happroach : PhysicalTrace w (g, state) approach
      (returnPort, state))
    (happroachGrooved : PassagesGrooved state approach)
    (happroachForeignNew : ∀ passage ∈ approach,
      passageSwitch passage ≠ mouth / 3)
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (harms : entry ≠ returnPort)
    (hcontact : ∃ passage ∈ approach,
      passageSwitch passage = R.actionSwitch) :
    ∀ d, ∃ port phase,
      stepN w d (outside, flipAt state (mouth / 3)) =
          some (port, phase) ∧
        (phase = flipAt state (mouth / 3) ∨
          phase = flipAt (flipAt state (mouth / 3))
            R.actionSwitch) := by
  let period := oldTail.length + R.runway.length +
    approach.length + 2
  have hpositive : 0 < period := by
    dsimp [period]
    omega
  have hperiod : stepN w period
      (outside, flipAt state (mouth / 3)) =
        some (outside, flipAt state (mouth / 3)) := by
    have hclosed :=
      (manufactured_flip_candy_splice_periodic_of_approach_contact
        R state hpaths hsplit htail hnotRunway hentryBranch hold
        horientation hentryGrooved happroach happroachGrooved
        happroachForeignNew hcrossed hmouthLink harms hcontact).2
    simpa [period] using hclosed
  apply periodic_two_phase_prefix_tongues hpositive hperiod
  intro d hd
  exact manufactured_flip_candy_splice_approach_contact_two_phases
    R state hpaths hsplit htail hnotRunway hentryBranch hold
    horientation hentryGrooved happroach happroachGrooved
    happroachForeignNew hcrossed hmouthLink harms hcontact
    (by simpa [period] using hd)

/-- Unrestricted-time novelty cover for the contact-repair orbit.  Every
sampled future vector is historical or the one doubly-latched vector. -/
theorem manufactured_flip_candy_splice_approach_contact_all_one_novelty
    {w : Wiring} {g e outside entry mouth returnPort : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {oldPrefix oldTail approach : List Passage}
    (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (htail : PhysicalTrace w (outside, state) oldTail
      ((ManufacturedReflector.flip R).orientedFinish state, state))
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (hentryBranch : entry % 3 ≠ 0)
    {old : Passage} (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨
      (entry, mouth) = (old.2, old.1))
    (hentryGrooved : arrive state entry = (mouth, state))
    (happroach : PhysicalTrace w (g, state) approach
      (returnPort, state))
    (happroachGrooved : PassagesGrooved state approach)
    (happroachForeignNew : ∀ passage ∈ approach,
      passageSwitch passage ≠ mouth / 3)
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (harms : entry ≠ returnPort)
    (hcontact : ∃ passage ∈ approach,
      passageSwitch passage = R.actionSwitch)
    (N : Nat) (history : List (List Bool))
    (hinitial : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history)
    (times : List Nat) :
    NoveltyCoverOn w N (outside, flipAt state (mouth / 3))
      times history 1 := by
  apply noveltyCoverOn_one_fresh_of_two_phases
    (v := flipAt (flipAt state (mouth / 3)) R.actionSwitch)
  · intro d _hd
    exact manufactured_flip_candy_splice_approach_contact_all_two_phases
      R state hpaths hsplit htail hnotRunway hentryBranch hold
      horientation hentryGrooved happroach happroachGrooved
      happroachForeignNew hcrossed hmouthLink harms hcontact d
  · exact hinitial

end GeneralN
