import FacingForwardConstant
import ChangedStayCountConstant
import ChangedFlipCountConstant
import CompleteRepairConstant
import EarlyFacingConstant
import TrackEarlyRepairConstant
import KnownEdgeFive

/-!
# Every protected repair costs at most six tongue vectors

The protected repair prefix has two phases.  Backward contacts, final-mouth
captures, facing-forward splices and changed stay splices then close in at
most three vectors; a complete repair costs five; the remaining changed flip
splice costs six.  This file retains the early-contact geometry long enough
to use those constant bounds instead of the older route-window counts.
-/

namespace GeneralN

/-- State-changing protected contact, retaining a constant backward-contact
count instead of the old `N+2` route-window count. -/
theorem ManufacturedReflector.protected_changed_contact_three_or_forward
    {w : Wiring} {N g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {u v : Tongues}
    {approach suffix : List Passage}
    {path : List Passage} {old : Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState)
      approach (p, u))
    (hpaths : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      times.length ≤ 3) ∨
      ∃ oriented repaired,
        oriented ∈ B.orientedRoute u ∧
        arrive u oriented.2 = (oriented.1, u) ∧
        passageSwitch oriented = p / 3 ∧
        x = oriented.2 ∧
        arrive v oriented.1 = (oriented.2, repaired) ∧
        arrive repaired oriented.2 = (oriented.1, repaired) := by
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hdirection⟩ :=
    B.changed_contact_on_orientedRoute u v hpaths
      hpath hold hswitch harrive hchanged
  rcases hdirection with hbackward | hforward
  · obtain ⟨recorded, tail, hBsplit⟩ :=
      List.append_of_mem horiented
    have hBroute := B.orientedRoute_trace u hpaths
    have hBsimple := B.orientedRoute_simple u
    have hBgrooved := hBroute.grooved_of_switchSimple hBsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hBroute hBsplit hBgrooved hBsimple
    have hrecorded := hprefixData.1
    have hrecordedForeign : ∀ passage ∈ recorded,
        passageSwitch passage ≠ p / 3 := by
      intro passage hp hEq
      apply hprefixData.2 passage hp
      exact hEq.trans horientedSwitch.symm
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hBsimple ⊢
      rw [hBsplit] at hBsimple
      simp only [List.map_append, List.map_cons] at hBsimple
      exact (List.nodup_append.mp hBsimple).1
    have hflip : v = flipAt u (p / 3) :=
      changed_arrival_eq_flipAt harrive hchanged
    have hrecordedV : PhysicalTrace w
        (e, v) recorded (oriented.1, v) := by
      rw [hflip]
      exact hrecorded.flip_unvisited hrecordedForeign
    have hrecordedGroovedV : PassagesGrooved v recorded :=
      hrecordedV.grooved_of_switchSimple hrecordedSimple
    have hrouteSimple := A.orientedRoute_simple B.activatedState
    rw [hrouteSplit] at hrouteSimple
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple
      exact (List.nodup_append.mp hrouteSimple).1
    have happroachForeign : ∀ passage ∈ approach,
        passageSwitch passage ≠ p / 3 := by
      unfold SwitchSimple at hrouteSimple
      simp only [List.map_append, List.map_cons] at hrouteSimple
      have hparts := List.nodup_append.mp hrouteSimple
      intro passage hp hEq
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (p / 3) (by simp [passageSwitch])
      exact hne hEq
    have happroachV : PhysicalTrace w
        (g, flipAt B.activatedState (p / 3)) approach (p, v) := by
      rw [hflip]
      exact happroach.flip_unvisited happroachForeign
    have happroachGroovedV : PassagesGrooved v approach :=
      happroachV.grooved_of_switchSimple happroachSimple
    have happroachGroovedU : PassagesGrooved u approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachReplayU :
        PhysicalTrace w (g, u) approach (p, u) :=
      happroach.replay_grooved u happroachGroovedU
    have happroachRoute : ∀ passage ∈ approach,
        passage ∈ A.orientedRoute B.activatedState := by
      intro passage hp
      rw [hrouteSplit]
      exact List.mem_append_left _ hp
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes, (stepN w k (p, u)).isSome) →
        (tailTimes.map (restrictedTonguesAt w N (p, u))).Nodup →
        tailTimes.length ≤ 2 := by
      intro tailTimes _ htailNodup
      exact backward_contact_tail_distinct_le_two
        hrecorded hrecordedGroovedV B.entryEdge
        (by simpa [hbackward] using harrive)
        happroachReplayU happroachGroovedV tailTimes htailNodup
    exact Or.inl (fun times hlive hnd =>
      two_phase_prefix_then_direct_tail_distinct_le_succ
        happroach.sound hphase htail (by omega) times hlive hnd)
  · obtain ⟨hforwardExit, repaired, hrepair, hgroove⟩ := hforward
    exact Or.inr ⟨oriented, repaired, horiented,
      horientedGroove, horientedSwitch,
      hforwardExit, hrepair, hgroove⟩

/-- No-change protected contact, retaining the constant backward-contact
count. -/
theorem ManufacturedReflector.protected_facing_contact_three_or_forward
    {w : Wiring} {N g e p marker fresh : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {contact : Tongues}
    {approach suffix path : List Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, marker) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState)
      approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hpath : path ∈ B.toSupported.paths)
    (hold : (fresh, p) ∈ path)
    (harrive : arrive contact p = (fresh, contact)) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      times.length ≤ 3) ∨
      (p, fresh) ∈ B.orientedRoute contact := by
  obtain ⟨oriented, horiented, horientation⟩ :=
    B.support_passage_on_orientedRoute contact hpath hold
  rcases horientation with hsame | hreverse
  · have horientedEq : oriented = (fresh, p) := hsame
    subst oriented
    obtain ⟨recorded, tail, hBsplit⟩ :=
      List.append_of_mem horiented
    have hBroute := B.orientedRoute_trace contact hpaths
    have hBsimple := B.orientedRoute_simple contact
    have hBgrooved := hBroute.grooved_of_switchSimple hBsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hBroute hBsplit hBgrooved hBsimple
    have hrecorded := hprefixData.1
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hBsimple ⊢
      rw [hBsplit] at hBsimple
      simp only [List.map_append, List.map_cons] at hBsimple
      exact (List.nodup_append.mp hBsimple).1
    have hrecordedGrooved : PassagesGrooved contact recorded :=
      hrecorded.grooved_of_switchSimple hrecordedSimple
    have hrouteSimple := A.orientedRoute_simple B.activatedState
    rw [hrouteSplit] at hrouteSimple
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple
      exact (List.nodup_append.mp hrouteSimple).1
    have happroachGrooved : PassagesGrooved contact approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachReplay :
        PhysicalTrace w (g, contact) approach (p, contact) :=
      happroach.replay_grooved contact happroachGrooved
    have happroachRoute : ∀ passage ∈ approach,
        passage ∈ A.orientedRoute B.activatedState := by
      intro passage hp
      rw [hrouteSplit]
      exact List.mem_append_left _ hp
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes, (stepN w k (p, contact)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (p, contact))).Nodup →
        tailTimes.length ≤ 2 := by
      intro tailTimes _ htailNodup
      exact backward_contact_tail_distinct_le_two
        hrecorded hrecordedGrooved B.entryEdge harrive
        happroachReplay happroachGrooved tailTimes htailNodup
    exact Or.inl (fun times hlive hnd =>
      two_phase_prefix_then_direct_tail_distinct_le_succ
        happroach.sound hphase htail (by omega) times hlive hnd)
  · right
    simpa [hreverse] using horiented

/-- Protected-repair classification in which every early exit already carries
its constant three-vector count. -/
theorem manufactured_pair_protected_repair_constant_outcomes
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      times.length ≤ 3) ∨
      A.FacingForwardMerge B ∨
      A.ChangedForwardMerge B ∨
      ∃ finalState,
        PhysicalTrace w (g, B.activatedState)
          (A.orientedRoute B.activatedState)
          (A.orientedFinish B.activatedState, finalState) ∧
        PathGrooves A.toSupported.paths finalState ∧
        PathGrooves B.toSupported.paths finalState := by
  rcases A.repair_current_route_preserving_until_conflict
      B.baseState B.activatedState hA hB with hfacing | hrest
  · obtain ⟨before, p, x, after, contact, other,
        hsplit, hprefix, hBcontact, hp, hchange,
        hcontact, harrive, hother⟩ := hfacing
    rcases B.facing_exit_matches_activation_passage
        hchange hcontact hp harrive with hreturn | hexploration
    · left
      intro times hlive hnd
      exact ManufacturedReflector.return_change_facing_distinct_le_three
        A B hA hB hsplit hprefix hBcontact hp
        hreturn.1 hreturn.2 times hlive hnd
    · obtain ⟨oldApproach, fresh, oldSuffix, oldU, oldV, path,
          _holdSplit, _holdSwitch, _holdTrace, _holdArrive,
          hpath, hold, hotherFresh⟩ := hexploration
      have harriveFresh : arrive contact p = (fresh, contact) := by
        simpa [hotherFresh] using harrive
      rcases A.protected_facing_contact_three_or_forward B hA hB
          hsplit hprefix hBcontact hpath hold harriveFresh with
        hcount | hforward
      · exact Or.inl hcount
      · exact Or.inr (Or.inl ⟨before, p, x, after,
          contact, fresh, path, hsplit, hprefix, hBcontact, hp,
          hchange, by simpa [passageSwitch] using hcontact,
          hpath, hold, harriveFresh,
          by simpa [hotherFresh] using hother,
          hforward⟩)
  · rcases hrest with hchanged | hcomplete
    · obtain ⟨approach, p, x, suffix, u, v, path, old,
          hsplit, hprefix, hBu, harrive,
          hpath, hold, hswitch, hchange⟩ := hchanged
      rcases A.protected_changed_contact_three_or_forward B hA hB
          hsplit hprefix hBu harrive hpath hold hswitch hchange with
        hcount | hforward
      · exact Or.inl hcount
      · obtain ⟨oriented, repaired, horiented, horientedGroove,
            horientedSwitch, hforwardExit, hrepair,
            hgroove⟩ := hforward
        exact Or.inr (Or.inr (Or.inl
          ⟨approach, p, x, suffix, u, v, path, old,
            oriented, repaired, hsplit, hprefix, hBu, harrive,
            hpath, hold, hswitch, hchange, horiented,
            horientedGroove, horientedSwitch, hforwardExit,
            hrepair, hgroove⟩))
    · exact Or.inr (Or.inr (Or.inr hcomplete))

/-- **Uniform protected-repair bound:** at most six distinct restricted tongue
vectors, independently of the number of switches. -/
theorem manufactured_pair_protected_repair_distinct_le_six
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 6 := by
  rcases manufactured_pair_protected_repair_constant_outcomes
      A B hA hB with hcount | hrest
  · have hc := hcount times hlive hnd
    omega
  · rcases hrest with hfacing | hrest
    · have hc := hfacing.distinct_le_three hA hB times hlive hnd
      omega
    · rcases hrest with hchanged | hcomplete
      · cases B with
        | stay R =>
            have hc := hchanged.stay_distinct_le_three
              hA hB times hlive hnd
            omega
        | flip R =>
            have hc := hchanged.flip_distinct_le_six
              hA hB times hnd
            omega
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        have hc := A.completed_protected_route_with_pair_distinct_le_five
          B hA hB hrepair hAfinal hBfinal times hlive hnd
        omega

end GeneralN
