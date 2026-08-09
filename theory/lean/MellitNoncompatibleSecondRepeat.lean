import MellitSupportInteraction
import MinimalBABADogbone

/-!
# The non-compatible Mellit second repeat

The literal reflector manufactured from a BABA endpoint has empty runway and
empty candy.  Consequently the opposite reflector's action always avoids its
support.  If the direct lobe's flip also avoided the opposite support, the
early compatible-pair theorem would give the forbidden four-cover.  Thus an
early pair in a raw six-event obstruction contains an actual support passage
through the direct lobe's action switch.

The final theorem feeds that physical passage into the exact oriented-contact
dichotomy.  A forward contact constructs `ChangedForwardMerge` and is closed
by `early_changedForward_second_repeat_false`; hence only the literal backward
retrace contact can remain.  This is a raw, general-`N` reduction, not a
cardinality assumption.
-/

namespace GeneralN

/-- An early opposite pair whose first reflector is a literal direct lobe
must expose a passage of the second reflector's support through the lobe's
action switch.  The alternative would be a compatible pair, already
contradicting the six-event obstruction. -/
theorem RawSixEventReduction.early_direct_lobe_pair_support_contact
    {w : Wiring} {N g e K : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (S : RawSixEventReduction w N start)
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hB : PathGrooves B.toSupported.paths state)
    (hreach : stepN w K start = some (g, state))
    (hK : K ≤ S.z1 + 1) :
    ∃ path ∈ B.toSupported.paths, ∃ passage ∈ path,
      passageSwitch passage = D.actionSwitch := by
  have hD : PathGrooves
      (ManufacturedReflector.flip D).toSupported.paths state := by
    change PathGrooves [D.runway, D.candy] state
    rw [hRunway, hCandy]
    simp [PathGrooves, PassagesGrooved]
  have hBD : B.toSupported.action.Avoids
      (ManufacturedReflector.flip D).toSupported.paths := by
    change B.toSupported.action.Avoids [D.runway, D.candy]
    rw [hRunway, hCandy]
    cases B.toSupported.action <;> simp [LocalAction.Avoids]
  by_cases hDB :
      (ManufacturedReflector.flip D).toSupported.action.Avoids
        B.toSupported.paths
  · exact (S.early_compatible_second_repeat_false hN
      (.flip D) B state hD hB hDB hBD hreach hK).elim
  · have hnot : ¬ (LocalAction.flip D.actionSwitch).Avoids
        B.toSupported.paths := by
      simpa [ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported] using hDB
    exact contact_of_not_avoids_flip hnot

/-- The support contact can be placed on the route which the opposite
reflector actually traverses in the reached state.  The stored support
passage may occur in either orientation; in both cases the oriented passage
is a genuine groove. -/
theorem RawSixEventReduction.early_direct_lobe_pair_oriented_contact
    {w : Wiring} {N g e K : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (S : RawSixEventReduction w N start)
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hB : PathGrooves B.toSupported.paths state)
    (hreach : stepN w K start = some (g, state))
    (hK : K ≤ S.z1 + 1) :
    ∃ path old oriented,
      path ∈ B.toSupported.paths ∧
      old ∈ path ∧
      passageSwitch old = D.actionSwitch ∧
      oriented ∈ B.orientedRoute state ∧
      arrive state oriented.2 = (oriented.1, state) ∧
      (oriented = old ∨ oriented = (old.2, old.1)) := by
  obtain ⟨path, hpath, old, hold, hswitch⟩ :=
    S.early_direct_lobe_pair_support_contact hN D B state
      hRunway hCandy hB hreach hK
  obtain ⟨oriented, horiented, horientation⟩ :=
    B.support_passage_on_orientedRoute state hpath hold
  have holdGroove : arrive state old.2 = (old.1, state) :=
    hB path hpath old hold
  have horientedGroove :
      arrive state oriented.2 = (oriented.1, state) := by
    rcases horientation with rfl | hreverse
    · exact holdGroove
    · subst oriented
      exact groove_forward holdGroove
  exact ⟨path, old, oriented, hpath, hold, hswitch,
    horiented, horientedGroove, horientation⟩

/-- **Sharp support-interaction reduction.**

Suppose the old repair route encounters a state-changing passage at the
switch named by an early direct-lobe pair.  The preceding theorem supplies
an old support passage at that switch.  The orientation-normalized contact
theorem gives exactly two cases:

* a backward contact, returned below as the remaining retrace residue;
* a forward self-repair, which is a `ChangedForwardMerge` and contradicts
  the already-proved early changed-forward four-cover.

Thus no unclassified "support interaction" remains. -/
theorem RawOverlappingFiveWindowReduction.early_direct_lobe_changed_contact_is_backward
    {w : Wiring} {N g e K p x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (D : ManufacturedFlipReflector w g e)
    (R : ManufacturedFlipReflector w e g)
    (A : ManufacturedReflector w g e)
    {approach suffix : List Passage}
    {u v : Tongues}
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hRactivated : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
        (ManufacturedReflector.flip R).activatedState)
    (hreach : stepN w K start =
      some (g, (ManufacturedReflector.flip R).activatedState))
    (hrouteSplit : A.orientedRoute
        (ManufacturedReflector.flip R).activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w
      (g, (ManufacturedReflector.flip R).activatedState)
        approach (p, u))
    (hRu : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hswitch : p / 3 = D.actionSwitch)
    (hchanged : v (p / 3) ≠ u (p / 3))
    (hlead : K + A.toSupported.travel ≤ C.z1 + 1) :
    ∃ oriented ∈
        (ManufacturedReflector.flip R).orientedRoute u,
      arrive u oriented.2 = (oriented.1, u) ∧
      passageSwitch oriented = p / 3 ∧
      x = oriented.1 := by
  have hK : K ≤ C.z1 + 1 :=
    Nat.le_trans (Nat.le_add_right K A.toSupported.travel) hlead
  obtain ⟨path, hpath, old, hold, holdSwitch⟩ :=
    C.toSixEventReduction.early_direct_lobe_pair_support_contact
      hN D (.flip R)
      (ManufacturedReflector.flip R).activatedState
      hRunway hCandy hRactivated hreach hK
  have holdSwitch' : passageSwitch old = p / 3 := by
    rw [holdSwitch, hswitch]
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hdirection⟩ :=
    (ManufacturedReflector.flip R).changed_contact_on_orientedRoute
      u v hRu hpath hold holdSwitch' harrive hchanged
  rcases hdirection with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · exact ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hbackward⟩
  · have hmerge : A.ChangedForwardMerge
        (ManufacturedReflector.flip R) :=
      ⟨approach, p, x, suffix, u, v, path, old, oriented,
        repaired, hrouteSplit, happroach, hRu, harrive,
        hpath, hold, holdSwitch', hchanged, horiented,
        horientedGroove, horientedSwitch, hforward,
        hrepair, hrestored⟩
    exact (C.early_changedForward_second_repeat_false
      hN hmerge hreach hlead).elim

/-- A backward changing contact followed by exact retrace and a grooved
return route has only its pre-contact and post-contact tongue vectors for all
time.  The first lap changes from `u` to `v`; every subsequent lap is wholly
grooved in `v`. -/
private theorem backward_contact_all_time_two_phase
    {w : Wiring} {g e p oldEntry : Nat}
    {oldBase oldEnd base u v : Tongues}
    {recorded approach : List Passage}
    (hrecorded :
      PhysicalTrace w (g, oldBase) recorded (oldEntry, oldEnd))
    (hrecordedGrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (happroach : PhysicalTrace w (e, base) approach (p, u))
    (happroachGrooved : PassagesGrooved v approach) :
    ∀ d, ∃ port phase,
      stepN w d (p, u) = some (port, phase) ∧
        (phase = u ∨ phase = v) := by
  have hback := physicalTrace_contact_retraces_prefix
    hrecorded hrecordedGrooved hentry hcontact
  have hforward := happroach.replay_grooved v happroachGrooved
  let cycle := (p, oldEntry) ::
    reversePassages recorded ++ approach
  have hcycleU : PhysicalTrace w (p, u) cycle (p, v) := by
    dsimp [cycle]
    simpa [List.append_assoc] using hback.append hforward
  have hheadGrooved : arrive v oldEntry = (p, v) := by
    have hbackLocal := arrive_back u p
    rwa [hcontact] at hbackLocal
  have hcycleGrooved : PassagesGrooved v cycle := by
    intro passage hp
    dsimp [cycle] at hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadGrooved
    · rcases List.mem_append.mp htail with hold | hnew
      · exact reversePassages_grooved
          hrecordedGrooved passage hold
      · exact happroachGrooved passage hnew
  have hcycleV : PhysicalTrace w (p, v) cycle (p, v) :=
    hcycleU.replay_grooved v hcycleGrooved
  have hpositive : 0 < cycle.length := by
    simp [cycle]
  have hwindowV : ∀ d, d ≤ cycle.length → ∃ port phase,
      stepN w d (p, v) = some (port, phase) ∧
        (phase = v ∨ phase = v) := by
    intro d hd
    obtain ⟨port, hrun⟩ :=
      hcycleV.grooved_prefix_tongues v hcycleGrooved hd
    exact ⟨port, v, hrun, Or.inl rfl⟩
  have hallV : ∀ d, ∃ port phase,
      stepN w d (p, v) = some (port, phase) ∧
        (phase = v ∨ phase = v) :=
    periodic_two_phase_prefix_tongues
      hpositive hcycleV.sound hwindowV
  have hbackSound :
      stepN w (recorded.length + 1) (p, u) = some (e, v) := by
    simpa [reversePassages_length] using hback.sound
  have hfirstLap : ∀ d, d ≤ cycle.length → ∃ port phase,
      stepN w d (p, u) = some (port, phase) ∧
        (phase = u ∨ phase = v) := by
    intro d hd
    by_cases hbackDepth : d ≤ recorded.length + 1
    · obtain ⟨port, hrun⟩ :=
        (physicalTrace_contact_retraces_prefix_pointwise
          hrecorded hrecordedGrooved hentry hcontact).2
          d hbackDepth
      refine ⟨port, if d = 0 then u else v, hrun, ?_⟩
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · let r := d - (recorded.length + 1)
      have hr : r ≤ approach.length := by
        dsimp [r]
        simp [cycle, reversePassages_length] at hd
        omega
      obtain ⟨port, hrun⟩ :=
        hforward.grooved_prefix_tongues v happroachGrooved hr
      have hdecomp : d = recorded.length + 1 + r := by
        dsimp [r]
        omega
      refine ⟨port, v, ?_, Or.inr rfl⟩
      rw [hdecomp, stepN_add, hbackSound]
      exact hrun
  intro d
  by_cases hfirst : d ≤ cycle.length
  · exact hfirstLap d hfirst
  · let r := d - cycle.length
    have hdecomp : d = cycle.length + r := by
      dsimp [r]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hallV r
    refine ⟨port, phase, ?_, ?_⟩
    · rw [hdecomp, stepN_add, hcycleU.sound]
      exact hrun
    · rcases hphase with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inr rfl

/-- **The early non-compatible support-interaction branch is closed.**

The preceding theorem forces the changing contact backward.  Exact retrace
then gives a two-vector tail from the contact time onward.  Since the complete
repair lead ends by `z1+1`, all five selected closes lie in that two-vector
tail, yielding the forbidden four-cover. -/
theorem RawOverlappingFiveWindowReduction.early_direct_lobe_changed_contact_false
    {w : Wiring} {N g e K p x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (D : ManufacturedFlipReflector w g e)
    (R : ManufacturedFlipReflector w e g)
    (A : ManufacturedReflector w g e)
    {approach suffix : List Passage}
    {u v : Tongues}
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hRactivated : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
        (ManufacturedReflector.flip R).activatedState)
    (hreach : stepN w K start =
      some (g, (ManufacturedReflector.flip R).activatedState))
    (hrouteSplit : A.orientedRoute
        (ManufacturedReflector.flip R).activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w
      (g, (ManufacturedReflector.flip R).activatedState)
        approach (p, u))
    (hRu : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hswitch : p / 3 = D.actionSwitch)
    (hchanged : v (p / 3) ≠ u (p / 3))
    (hlead : K + A.toSupported.travel ≤ C.z1 + 1) : False := by
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hbackward⟩ :=
    C.early_direct_lobe_changed_contact_is_backward hN D R A
      hRunway hCandy hRactivated hreach hrouteSplit happroach
      hRu harrive hswitch hchanged hlead
  obtain ⟨recorded, tail, hRsplit⟩ :=
    List.append_of_mem horiented
  have hRroute :=
    (ManufacturedReflector.flip R).orientedRoute_trace u hRu
  have hRsimple :=
    (ManufacturedReflector.flip R).orientedRoute_simple u
  have hRgrooved := hRroute.grooved_of_switchSimple hRsimple
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    hRroute hRsplit hRgrooved hRsimple
  have hrecorded := hprefixData.1
  have hrecordedForeign : ∀ passage ∈ recorded,
      passageSwitch passage ≠ p / 3 := by
    intro passage hp hEq
    apply hprefixData.2 passage hp
    exact hEq.trans horientedSwitch.symm
  have hrecordedSimple : SwitchSimple recorded := by
    unfold SwitchSimple at hRsimple ⊢
    rw [hRsplit] at hRsimple
    simp only [List.map_append, List.map_cons] at hRsimple
    exact (List.nodup_append.mp hRsimple).1
  have hflip : v = flipAt u (p / 3) :=
    changed_arrival_eq_flipAt harrive hchanged
  have hrecordedV : PhysicalTrace w
      (e, v) recorded (oriented.1, v) := by
    rw [hflip]
    exact hrecorded.flip_unvisited hrecordedForeign
  have hrecordedGroovedV : PassagesGrooved v recorded :=
    hrecordedV.grooved_of_switchSimple hrecordedSimple
  have hrouteSimple := A.orientedRoute_simple
    (ManufacturedReflector.flip R).activatedState
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
      (g, flipAt
        (ManufacturedReflector.flip R).activatedState (p / 3))
      approach (p, v) := by
    rw [hflip]
    exact happroach.flip_unvisited happroachForeign
  have happroachGroovedV : PassagesGrooved v approach :=
    happroachV.grooved_of_switchSimple happroachSimple
  have hcontact : arrive u p = (oriented.1, v) := by
    simpa [hbackward] using harrive
  have htwoPhase := backward_contact_all_time_two_phase
    hrecorded hrecordedGroovedV
      (ManufacturedReflector.flip R).entryEdge
      hcontact happroach happroachGroovedV
  let contactTime := K + approach.length
  have hcontactReach : stepN w contactTime start = some (p, u) := by
    dsimp [contactTime]
    rw [stepN_add, hreach]
    exact happroach.sound
  have hrouteLe := A.orientedRoute_length_le_travel
    (ManufacturedReflector.flip R).activatedState
  have hcontactBefore : contactTime ≤ C.z1 + 1 := by
    dsimp [contactTime]
    rw [hrouteSplit] at hrouteLe
    simp only [List.length_append, List.length_cons] at hrouteLe
    omega
  let times :=
    [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1]
  let history := rawFirstWriterHistory w N start (C.z5 + 1) ++
    [restrictedTonguesAt w N start (C.z0 + 1)]
  have hcover : NoveltyCoverOn w N start times history 4 := by
    refine ⟨[VectorCount.restrict N u, VectorCount.restrict N v],
      by simp, ?_⟩
    intro t ht
    have o12 : C.z1 < C.z2 := C.order12
    have o23 : C.z2 < C.z3 := C.order23
    have o34 : C.z3 < C.z4 := C.order34
    have o45 : C.z4 < C.z5 := C.order45
    have htLower : contactTime ≤ t := by
      dsimp [times] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl <;> omega
    let d := t - contactTime
    have htEq : t = contactTime + d := by
      dsimp [d]
      omega
    obtain ⟨port, phase, hlocal, hphase⟩ := htwoPhase d
    have hglobal : stepN w t start = some (port, phase) := by
      rw [htEq, stepN_add, hcontactReach]
      exact hlocal
    have hvector : restrictedTonguesAt w N start t =
        VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    apply List.mem_append_right history
    rw [hvector]
    rcases hphase with rfl | rfl <;> simp
  exact C.toSixEventReduction.no_tail_four_cover hN (by
    simpa [RawOverlappingFiveWindowReduction.toSixEventReduction,
      times, history] using hcover)

end GeneralN
