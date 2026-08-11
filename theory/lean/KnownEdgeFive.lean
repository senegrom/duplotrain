import TrackEarlyRepairCount
import FacingMergeCount
import KnownEdgeEight

/-!
# Known-edge coefficient-5 linear bound

Every protected-repair branch now has a switch-count-free or window-sized
tongue count:

* early retrace/capture exits: `N+2` (the cycles are grooved or
  two-phase);
* facing-forward splice: `N+2` (route window plus the alternate phase);
* changed stay splice: `N+2`;
* changed flip splice: `2*N+5`;
* complete repair: `N+4`.

Protected repair therefore exposes at most `2*N+5` distinct restricted
tongue vectors, and the two construction histories give `4*N+8` for the
two-reflector component.  The remaining `5*N+1` cost is the *first
periodic outcome* — the settle-on-a-cycle exit of the first activation,
still counted by time — which now decides the coefficient: the known-edge
bound is `5*N+8`, and the first-exploration lasso is the next frontier.
-/

namespace GeneralN

/-- Count form of the state-changing protected-support classification. -/
theorem ManufacturedReflector.protected_changed_contact_count_or_forward
    {w : Wiring} {N g e p x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedReflector w e g)
    {startState u v : Tongues}
    {route approach suffix : List Passage}
    {path : List Passage} {old : Passage}
    (hrouteSplit : route = approach ++ (p, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, u))
    (hpaths : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    (∀ times : List Nat,
      (times.map (restrictedTonguesAt w N (g, startState))).Nodup →
      times.length ≤ N + 2) ∨
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
    have hrouteSimple' := hrouteSimple
    rw [hrouteSplit] at hrouteSimple'
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple' ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      exact (List.nodup_append.mp hrouteSimple').1
    have happroachForeign : ∀ passage ∈ approach,
        passageSwitch passage ≠ p / 3 := by
      unfold SwitchSimple at hrouteSimple'
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      have hparts := List.nodup_append.mp hrouteSimple'
      intro passage hp hEq
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (p / 3) (by simp [passageSwitch])
      exact hne hEq
    have happroachV : PhysicalTrace w
        (g, flipAt startState (p / 3)) approach (p, v) := by
      rw [hflip]
      exact happroach.flip_unvisited happroachForeign
    have happroachGroovedV : PassagesGrooved v approach :=
      happroachV.grooved_of_switchSimple happroachSimple
    have happroachLe : approach.length ≤ N :=
      happroach.switchSimple_length_le_switches hN happroachSimple
    exact Or.inl (fun times hnd =>
      backward_contact_distinct_le_succ_succ happroachLe
        hrecorded hrecordedGroovedV B.entryEdge
        (by simpa [hbackward] using harrive)
        happroach happroachGroovedV times hnd)
  · obtain ⟨hforwardExit, repaired, hrepair, hgroove⟩ := hforward
    exact Or.inr ⟨oriented, repaired, horiented,
      horientedGroove, horientedSwitch,
      hforwardExit, hrepair, hgroove⟩

/-- Count form of the no-change protected-support classification. -/
theorem ManufacturedReflector.protected_facing_contact_count_or_forward
    {w : Wiring} {N g e p marker fresh : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedReflector w e g)
    {startState contact : Tongues}
    {route approach suffix path : List Passage}
    (hrouteSplit : route = approach ++ (p, marker) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hpath : path ∈ B.toSupported.paths)
    (hold : (fresh, p) ∈ path)
    (harrive : arrive contact p = (fresh, contact)) :
    (∀ times : List Nat,
      (times.map (restrictedTonguesAt w N (g, startState))).Nodup →
      times.length ≤ N + 2) ∨
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
    have hrouteSimple' := hrouteSimple
    rw [hrouteSplit] at hrouteSimple'
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple' ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      exact (List.nodup_append.mp hrouteSimple').1
    have happroachGrooved : PassagesGrooved contact approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachLe : approach.length ≤ N :=
      happroach.switchSimple_length_le_switches hN happroachSimple
    exact Or.inl (fun times hnd =>
      backward_contact_distinct_le_succ_succ happroachLe
        hrecorded hrecordedGrooved B.entryEdge harrive
        happroach happroachGrooved times hnd)
  · right
    simpa [hreverse] using horiented

/-- Protected-repair classification with every early exit carried as an
`N+2` tongue count. -/
theorem manufactured_pair_protected_repair_quantitative_outcomes_count
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    (∀ times : List Nat,
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      times.length ≤ N + 2) ∨
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
      intro times hnd
      exact B.return_change_facing_distinct_le_succ_succ hN
        hsplit (A.orientedRoute_simple B.activatedState)
        hprefix hBcontact hp hreturn.1 hreturn.2 times hnd
    · obtain ⟨oldApproach, fresh, oldSuffix, oldU, oldV, path,
          _holdSplit, _holdSwitch, _holdTrace, _holdArrive,
          hpath, hold, hotherFresh⟩ := hexploration
      have harriveFresh : arrive contact p = (fresh, contact) := by
        simpa [hotherFresh] using harrive
      rcases B.protected_facing_contact_count_or_forward
          hN hsplit (A.orientedRoute_simple B.activatedState)
          hprefix hBcontact hpath hold harriveFresh with
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
      rcases B.protected_changed_contact_count_or_forward
          hN hsplit (A.orientedRoute_simple B.activatedState)
          hprefix hBu harrive hpath hold hswitch hchange with
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

/-- Protected repair exposes at most `2*N+5` distinct restricted tongue
vectors. -/
theorem manufactured_pair_protected_repair_distinct_le_two_mul_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 2 * N + 5 := by
  rcases manufactured_pair_protected_repair_quantitative_outcomes_count
      hN A B hA hB with hcount | hrest
  · have hc := hcount times hnd
    omega
  · rcases hrest with hfacing | hrest
    · have hc := hfacing.distinct_le_succ_succ hN times hnd
      omega
    · rcases hrest with hchanged | hcomplete
      · cases B with
        | stay R =>
            have hc := hchanged.stay_distinct_le_n_succ_two hN times hnd
            omega
        | flip R =>
            have hc := hchanged.flip_distinct_le_two_mul_add_five
              hN times hnd
            omega
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        have hc := A.completed_route_with_pair_support_distinct_le_n_succ_four
          hN B B.baseState B.activatedState finalState hA hrepair
          hAfinal hBfinal times hlive hnd
        omega

/-- Known-edge long-run coefficient-5 bound.  The two-reflector component
counts `4*N+8`; the first periodic outcome still costs its `5*N+1` time
cap, so the uniform bound is `5*N+8`. -/
theorem known_edge_long_run_distinct_le_five
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlong : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 5 * N + 8 := by
  rcases two_component_quantitative_outcome_exact hN hlong hentry with
    hperiodic | hpair
  · have hsmall := hperiodic.tongue_vector_count times hlive (by
      exact hnd)
    omega
  · obtain ⟨A, B, stateA, stateB,
      _hfirstLe, _hsecondLe, hbaseA, hactivatedA,
      hreachA, hgroovesA, hbaseB, hactivatedB,
      hreachB, hgroovesB, _hpreservesB⟩ := hpair
    have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
      simpa [hbaseB] using hgroovesA
    have hBatActivated :
        PathGrooves B.toSupported.paths B.activatedState := by
      simpa [← hactivatedB] using hgroovesB
    have htail : ∀ (tailTimes : List Nat),
        (∀ k ∈ tailTimes,
          (stepN w k (start.1, stateB)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (start.1, stateB))).Nodup →
        tailTimes.length ≤ 2 * N + 5 := by
      intro tailTimes htailLive htailNodup
      have htailLive' : ∀ k ∈ tailTimes,
          (stepN w k (start.1, B.activatedState)).isSome := by
        simpa [← hactivatedB] using htailLive
      have htailNodup' :
          (tailTimes.map
            (restrictedTonguesAt w N
              (start.1, B.activatedState))).Nodup := by
        simpa [← hactivatedB] using htailNodup
      exact manufactured_pair_protected_repair_distinct_le_two_mul_add_five
        hN A B hAatBase hBatActivated tailTimes
          htailLive' htailNodup'
    have hassembled :=
      two_manufacturing_journeys_then_direct_tail_distinct_le
        (tailCap := 2 * N + 5)
        hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
        hbaseB hactivatedB hreachB hgroovesB htail times hlive hnd
    omega

end GeneralN
