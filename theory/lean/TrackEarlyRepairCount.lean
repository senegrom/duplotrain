import TrackQuantitativeRouteSharp
import TrackStayContactAllTime

/-!
# Tongue counts for the early protected-repair exits

The `6*N+3` early lassos are time-shaped, but their vector content is tiny:

* a **backward contact** retraces the recorded prefix and replays the
  approach, all grooved at the post-contact state — the cycle carries **one**
  tongue vector, so the lasso counts the approach window plus one;
* the **final-mouth capture** alternates between exactly **two** phases
  after its switch-simple approach.

Both count at most `N+2` distinct restricted tongue vectors, with no
liveness hypothesis.
-/

namespace GeneralN

/-- **Backward-contact count.**  The retrace/replay cycle is grooved at the
post-contact state, so the entire lasso shows the approach window plus a
single further vector: at most `N+2` in total. -/
theorem backward_contact_distinct_le_succ_succ
    {w : Wiring} {N g e p oldEntry : Nat}
    {oldBase oldEnd base u v : Tongues}
    {recorded approach : List Passage}
    (happroachLe : approach.length ≤ N)
    (hrecorded :
      PhysicalTrace w (g, oldBase) recorded (oldEntry, oldEnd))
    (hrecordedGrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (happroach : PhysicalTrace w (e, base) approach (p, u))
    (happroachGrooved : PassagesGrooved v approach)
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N (e, base))).Nodup) :
    times.length ≤ N + 2 := by
  have hback := physicalTrace_contact_retraces_prefix
    hrecorded hrecordedGrooved hentry hcontact
  have hforward := happroach.replay_grooved v happroachGrooved
  let cycle := (p, oldEntry) ::
    reversePassages recorded ++ approach
  have hcycle : PhysicalTrace w (p, u) cycle (p, v) := by
    dsimp [cycle]
    simpa [List.append_assoc] using hback.append hforward
  have hheadGrooved : arrive v oldEntry = (p, v) := by
    have hbackLocal := arrive_back u p
    rwa [hcontact] at hbackLocal
  have hallGrooved : PassagesGrooved v cycle := by
    intro passage hp
    dsimp [cycle] at hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadGrooved
    · rcases List.mem_append.mp htail with hold | hnew
      · exact reversePassages_grooved hrecordedGrooved passage hold
      · exact happroachGrooved passage hnew
  have hperiod : stepN w cycle.length (p, v) = some (p, v) := by
    dsimp [cycle]
    exact run_grooved_passages w v p oldEntry p
      (reversePassages recorded ++ approach)
      hcycle.linked hallGrooved hcycle.last_link
  have hcycleV : PhysicalTrace w (p, v) cycle (p, v) :=
    hcycle.replay_grooved v hallGrooved
  have hpositive : 0 < cycle.length := by
    dsimp [cycle]
    simp
  have hallV : ∀ m, ∃ port, stepN w m (p, v) = some (port, v) := by
    intro m
    have hwindow : ∀ d, d ≤ cycle.length → ∃ port phase,
        stepN w d (p, v) = some (port, phase) ∧
          (phase = v ∨ phase = v) := by
      intro d hd
      obtain ⟨port, hrun⟩ :=
        hcycleV.grooved_prefix_tongues v hallGrooved hd
      exact ⟨port, v, hrun, Or.inl rfl⟩
    obtain ⟨port, phase, hrun, hphase⟩ :=
      periodic_two_phase_prefix_tongues hpositive hperiod hwindow m
    rcases hphase with h | h
    · exact ⟨port, by rwa [h] at hrun⟩
    · exact ⟨port, by rwa [h] at hrun⟩
  have hfromU : ∀ m, 1 ≤ m →
      ∃ port, stepN w m (p, u) = some (port, v) := by
    intro m hm
    cases hback with
    | @cons _ _ q₀ _ v' _ _ harrive hlink htailBack =>
        have hv' : v' = v := by
          have h := harrive.symm.trans hcontact
          exact congrArg Prod.snd h
        rw [hv'] at harrive htailBack
        have htail := htailBack.append hforward
        have hone : stepN w 1 (p, u) = some (q₀, v) := by
          simp [stepN, step, harrive, hlink]
        let m' := m - 1
        have hmEq : m = 1 + m' := by
          dsimp [m']
          omega
        have htailGrooved : PassagesGrooved v
            (reversePassages recorded ++ approach) := by
          intro passage hp
          exact hallGrooved passage (List.mem_cons_of_mem _ hp)
        by_cases hfirst : m' ≤
            (reversePassages recorded ++ approach).length
        · obtain ⟨port, hrun⟩ :=
            htail.grooved_prefix_tongues v htailGrooved hfirst
          refine ⟨port, ?_⟩
          rw [hmEq, stepN_add, hone]
          simpa using hrun
        · let m'' := m' -
            (reversePassages recorded ++ approach).length
          have hm'Eq : m' =
              (reversePassages recorded ++ approach).length + m'' := by
            dsimp [m'']
            omega
          obtain ⟨port, hrun⟩ := hallV m''
          refine ⟨port, ?_⟩
          rw [hmEq, stepN_add, hone]
          simp only [Option.bind_some]
          rw [hm'Eq, stepN_add]
          have htailV := htail.replay_grooved v htailGrooved
          rw [htailV.sound]
          simpa using hrun
  have hcover : NoveltyCoverOn w N (e, base) times [] (N + 2) := by
    refine ⟨((List.range (approach.length + 1)).map
      (restrictedTonguesAt w N (e, base))) ++
        [VectorCount.restrict N v], by simp; omega, ?_⟩
    intro k hk
    simp only [List.nil_append]
    by_cases hkpre : k ≤ approach.length
    · exact List.mem_append_left _
        (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩)
    · let m := k - approach.length
      have hm : 1 ≤ m := by
        dsimp [m]
        omega
      have hkEq : k = approach.length + m := by
        dsimp [m]
        omega
      obtain ⟨port, hrun⟩ := hfromU m hm
      have hglobal : stepN w k (e, base) = some (port, v) := by
        rw [hkEq, stepN_add, happroach.sound]
        simpa using hrun
      apply List.mem_append_right
      have hvec : restrictedTonguesAt w N (e, base) k =
          VectorCount.restrict N v := by
        simp [restrictedTonguesAt, tonguesAt, hglobal]
      simp [hvec]
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

/-- **Final-mouth capture count.**  After the switch-simple approach the
walk alternates between exactly two phases forever: at most `N+2` distinct
restricted tongue vectors. -/
theorem ManufacturedFlipReflector.facing_mouth_contact_distinct_le_succ_succ
    {w : Wiring} {N g e x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedFlipReflector w e g)
    {startState contact : Tongues}
    {route approach suffix : List Passage}
    (hrouteSplit : route = approach ++ (B.mouth, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach
      (B.mouth, contact))
    (hpaths : PathGrooves [B.runway, B.candy] contact)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, startState))).Nodup) :
    times.length ≤ N + 2 := by
  have hrouteSimple' := hrouteSimple
  rw [hrouteSplit] at hrouteSimple'
  have happroachSimple : SwitchSimple approach := by
    unfold SwitchSimple at hrouteSimple' ⊢
    simp only [List.map_append, List.map_cons] at hrouteSimple'
    exact (List.nodup_append.mp hrouteSimple').1
  have hforeign : ∀ passage ∈ approach,
      passageSwitch passage ≠ B.actionSwitch := by
    unfold SwitchSimple at hrouteSimple'
    simp only [List.map_append, List.map_cons] at hrouteSimple'
    have hparts := List.nodup_append.mp hrouteSimple'
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (B.mouth, x)) (by simp)
    apply hne
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hEq
  have happroachGrooved : PassagesGrooved contact approach :=
    happroach.grooved_of_switchSimple happroachSimple
  have happroachContact : PhysicalTrace w
      (g, contact) approach (B.mouth, contact) :=
    happroach.replay_grooved contact happroachGrooved
  let alternate := flipAt contact B.actionSwitch
  have happroachAlternate : PhysicalTrace w
      (g, alternate) approach (B.mouth, alternate) := by
    dsimp [alternate]
    exact happroachContact.flip_unvisited hforeign
  have hpathsAlternate :
      PathGrooves [B.runway, B.candy] alternate := by
    dsimp [alternate]
    change PathGrooves [B.runway, B.candy]
      ((LocalAction.flip B.actionSwitch).apply contact)
    exact hpaths.after_avoiding_action B.support_foreign
  have happroachAlternateGrooved : PassagesGrooved alternate approach := by
    dsimp [alternate]
    exact grooved_after_flip_other happroachGrooved hforeign
  let cap := B.candy.length + 2 + B.runway.length
  have hcaptureFromAlternate :
      stepN w cap (B.mouth, alternate) = some (g, contact) := by
    dsimp [cap, alternate]
    exact B.capture_from_mouth contact
      (pathGrooves_pair.mp hpaths).1
      (pathGrooves_pair.mp hpaths).2
  have hcaptureFromContact :
      stepN w cap (B.mouth, contact) = some (g, alternate) := by
    have hcapture := B.capture_from_mouth alternate
      (pathGrooves_pair.mp hpathsAlternate).1
      (pathGrooves_pair.mp hpathsAlternate).2
    simpa [cap, alternate, flipAt_flipAt] using hcapture
  have hcapPhaseFromAlternate : ∀ d, d ≤ cap → ∃ port phase,
      stepN w d (B.mouth, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, phase, hrun, hphase⟩ :=
      B.capture_from_mouth_two_phase contact
        (pathGrooves_pair.mp hpaths).1
        (pathGrooves_pair.mp hpaths).2 (d := d) (by
          dsimp [cap] at hd
          omega)
    refine ⟨port, phase, hrun, ?_⟩
    rcases hphase with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hcapPhaseFromContact : ∀ d, d ≤ cap → ∃ port phase,
      stepN w d (B.mouth, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, phase, hrun, hphase⟩ :=
      B.capture_from_mouth_two_phase alternate
        (pathGrooves_pair.mp hpathsAlternate).1
        (pathGrooves_pair.mp hpathsAlternate).2 (d := d) (by
          dsimp [cap] at hd
          omega)
    have hstart : flipAt alternate B.actionSwitch = contact := by
      dsimp [alternate]
      exact flipAt_flipAt contact B.actionSwitch
    rw [hstart] at hrun hphase
    refine ⟨port, phase, hrun, ?_⟩
    rcases hphase with h | h
    · exact Or.inr h
    · exact Or.inl h
  let half := approach.length + cap
  have hhalfAlternate :
      stepN w half (g, alternate) = some (g, contact) := by
    dsimp [half]
    rw [stepN_add, happroachAlternate.sound]
    exact hcaptureFromAlternate
  have hhalfContact :
      stepN w half (g, contact) = some (g, alternate) := by
    dsimp [half]
    rw [stepN_add, happroachContact.sound]
    exact hcaptureFromContact
  have hhalfPhaseFromAlternate : ∀ d, d ≤ half → ∃ port phase,
      stepN w d (g, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    refine stay_twoPhase_concat happroachAlternate.sound
      ?_ hcapPhaseFromAlternate d (by dsimp [half] at hd; omega)
    intro dd hdd
    obtain ⟨port, hrun⟩ :=
      happroachAlternate.grooved_prefix_tongues alternate
        happroachAlternateGrooved hdd
    exact ⟨port, alternate, hrun, Or.inl rfl⟩
  have hhalfPhaseFromContact : ∀ d, d ≤ half → ∃ port phase,
      stepN w d (g, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    refine stay_twoPhase_concat happroachContact.sound
      ?_ hcapPhaseFromContact d (by dsimp [half] at hd; omega)
    intro dd hdd
    obtain ⟨port, hrun⟩ :=
      happroachContact.grooved_prefix_tongues contact
        happroachGrooved hdd
    exact ⟨port, contact, hrun, Or.inr rfl⟩
  have hperiod :
      stepN w (half + half) (g, alternate) =
        some (g, alternate) := by
    rw [stepN_add, hhalfAlternate]
    exact hhalfContact
  have hpositive : 0 < half + half := by
    dsimp [half, cap]
    omega
  have hwindowPhase : ∀ d, d ≤ half + half → ∃ port phase,
      stepN w d (g, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    exact stay_twoPhase_concat hhalfAlternate
      hhalfPhaseFromAlternate hhalfPhaseFromContact d hd
  have hallPhase := periodic_two_phase_prefix_tongues
    hpositive hperiod hwindowPhase
  have hlead : stepN w half (g, startState) =
      some (g, alternate) := by
    dsimp [half]
    rw [stepN_add, happroach.sound]
    exact hcaptureFromContact
  have happroachLe : approach.length ≤ N :=
    happroach.switchSimple_length_le_switches hN happroachSimple
  have hcontactWindow :
      restrictedTonguesAt w N (g, startState) approach.length =
        VectorCount.restrict N contact := by
    simp [restrictedTonguesAt, tonguesAt, happroach.sound]
  have hcover : NoveltyCoverOn w N (g, startState) times []
      (N + 2) := by
    refine ⟨((List.range (approach.length + 1)).map
      (restrictedTonguesAt w N (g, startState))) ++
        [VectorCount.restrict N alternate], by simp; omega, ?_⟩
    intro k hk
    simp only [List.nil_append]
    by_cases hkpre : k ≤ approach.length
    · exact List.mem_append_left _
        (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩)
    · have hmem : ∀ {port phase},
          stepN w k (g, startState) = some (port, phase) →
          (phase = alternate ∨ phase = contact) →
          restrictedTonguesAt w N (g, startState) k ∈
            ((List.range (approach.length + 1)).map
              (restrictedTonguesAt w N (g, startState))) ++
              [VectorCount.restrict N alternate] := by
        intro port phase hrun hphase
        have hvec : restrictedTonguesAt w N (g, startState) k =
            VectorCount.restrict N phase := by
          simp [restrictedTonguesAt, tonguesAt, hrun]
        rcases hphase with h | h
        · apply List.mem_append_right
          simp [hvec, h]
        · apply List.mem_append_left
          refine List.mem_map.mpr
            ⟨approach.length, List.mem_range.mpr (by omega), ?_⟩
          rw [hcontactWindow, hvec, h]
      by_cases hkhalf : k ≤ half
      · let r := k - approach.length
        have hr : r ≤ cap := by
          dsimp [r]
          dsimp [half] at hkhalf
          omega
        have hkEq : k = approach.length + r := by
          dsimp [r]
          omega
        obtain ⟨port, phase, hrun, hphase⟩ :=
          hcapPhaseFromContact r hr
        have hrunGlobal : stepN w k (g, startState) =
            some (port, phase) := by
          rw [hkEq, stepN_add, happroach.sound]
          simpa using hrun
        exact hmem hrunGlobal hphase
      · let r := k - half
        have hkEq : k = half + r := by
          dsimp [r]
          omega
        obtain ⟨port, phase, hrun, hphase⟩ := hallPhase r
        have hrunGlobal : stepN w k (g, startState) =
            some (port, phase) := by
          rw [hkEq, stepN_add, hlead]
          simpa using hrun
        exact hmem hrunGlobal hphase
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

/-- Orientation-free count for the final-return exception. -/
theorem ManufacturedReflector.return_change_facing_distinct_le_succ_succ
    {w : Wiring} {N g e p x : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (B : ManufacturedReflector w e g)
    {startState contact : Tongues}
    {route approach suffix : List Passage}
    (hrouteSplit : route = approach ++ (p, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hp : p % 3 = 0)
    (hswitch : p / 3 = B.preReturn.1 / 3)
    (hreturnChange : B.activatedState (p / 3) ≠
      B.preReturn.2 (p / 3))
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, startState))).Nodup) :
    times.length ≤ N + 2 := by
  cases B with
  | stay R => exact (hreturnChange rfl).elim
  | flip R =>
      have hsecondSwitch : R.secondArm / 3 = R.mouth / 3 := by
        have hs := arrive_exit_switch R.returnState R.secondArm
        rw [R.crossed] at hs
        exact hs.symm
      have hmouthStem := R.mouth_is_stem
      have hpmouth : p = R.mouth := by
        change p / 3 = R.secondArm / 3 at hswitch
        omega
      subst p
      exact R.facing_mouth_contact_distinct_le_succ_succ hN
        hrouteSplit hrouteSimple happroach hpaths times hnd

end GeneralN
