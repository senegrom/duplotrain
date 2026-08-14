import RepairLeadTwoPhase
import TrackEarlyRepairCount

/-!
# Constant vector counts for protected backward contacts

A protected repair prefix has two phases.  Once a backward contact is taken,
the retrace/replay cycle has only the incoming contact vector and its settled
post-contact vector.  The whole branch therefore has at most three vectors.
-/

namespace GeneralN

/-- Starting at the contact itself, a backward retrace/replay cycle has at
most two distinct restricted tongue vectors. -/
theorem backward_contact_tail_distinct_le_two
    {w : Wiring} {N g e p oldEntry : Nat}
    {oldBase oldEnd u v : Tongues}
    {recorded approach : List Passage}
    (hrecorded :
      PhysicalTrace w (g, oldBase) recorded (oldEntry, oldEnd))
    (hrecordedGrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (happroach : PhysicalTrace w (e, u) approach (p, u))
    (happroachGrooved : PassagesGrooved v approach)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (p, u))).Nodup) :
    times.length ≤ 2 := by
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
  have hcover : NoveltyCoverOn w N (p, u) times [] 2 := by
    refine ⟨[VectorCount.restrict N u,
      VectorCount.restrict N v], by simp, ?_⟩
    intro k hk
    simp only [List.nil_append]
    cases k with
    | zero =>
        simp [restrictedTonguesAt, tonguesAt, stepN]
    | succ k =>
        obtain ⟨port, hrun⟩ := hfromU (k + 1) (by omega)
        have hvec : restrictedTonguesAt w N (p, u) (k + 1) =
            VectorCount.restrict N v := by
          simp [restrictedTonguesAt, tonguesAt, hrun]
        simp [hvec]
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

end GeneralN
