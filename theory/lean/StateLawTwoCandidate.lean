import FacingForwardNovelty
import FirstCycleCountSharp
import EarlyFacingConstant

/-!
# Constant tongue count for protected facing-forward repairs

The existing facing-forward theorem charged every position of the repair
approach.  Under the protected-repair hypotheses that approach has only its
activated and contact tongue phases.  The reverse-candy suffix and the whole
absorbing future use only the contact phase and its one-switch alternate.
The two pieces share the contact endpoint, so the complete branch has at most
three restricted tongue vectors.
-/

namespace GeneralN

/-! ## Raw counting for a history-covered journey and a short suffix
These lemmas deliberately expose every semantic hypothesis.  The first says
that once a raw `stepN` run is dead at a horizon, all live sample times lie
strictly before that horizon.  The remaining lemmas compose an explicitly
history-covered prefix with such a suffix.  If the boundary vector is already
in the prefix history, it is counted only once.

No manufactured-reflector certificate is hidden in this file: callers supply
the reachability equation, the pointwise history cover, and (when available)
the boundary-membership proof directly.
-/

/-- If the train is off-track at time `L`, a list of live sample times whose
restricted tongue vectors are pairwise distinct has length at most `L`.

The conclusion is positional, not dynamical: every live sample lies in the
finite interval `[0,L)`, and vector-nodup implies time-nodup. -/
theorem dead_horizon_live_distinct_le
    {w : Wiring} {N L : Nat} {start : Nat × Tongues}
    (hdead : stepN w L start = none)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ L := by
  have htimesNodup : times.Nodup :=
    List.Pairwise.of_map (restrictedTonguesAt w N start)
      (fun _ _ hne hEq => hne (congrArg _ hEq)) hnd
  have hlt : ∀ k ∈ times, k < L := by
    intro k hk
    by_cases hsmall : k < L
    · exact hsmall
    · have hkLive := hlive k hk
      rw [show k = L + (k - L) by omega, stepN_add, hdead] at hkLive
      simp at hkLive
  exact nodup_nat_lt_length htimesNodup hlt

/-! ## Constant vector counts for protected backward contacts
A protected repair prefix has two phases.  Once a backward contact is taken,
the retrace/replay cycle has only the incoming contact vector and its settled
post-contact vector.  The whole branch therefore has at most three vectors.
-/

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
  have hall := backward_contact_all_time_two_phase hrecorded hrecordedGrooved
    hentry hcontact happroach happroachGrooved
  have hcover : NoveltyCoverOn w N (p, u) times [] 2 := by
    refine ⟨[VectorCount.restrict N u, VectorCount.restrict N v], by simp, ?_⟩
    intro d _hd
    obtain ⟨port, phase, hr, hp⟩ := hall d
    rcases hp with rfl | rfl <;> simp [restrictedTonguesAt, tonguesAt, hr]
  simpa using noveltyCoverOn_distinct_count hcover hnd

/-- **Protected facing-forward count:** at most three distinct restricted
tongue vectors. -/
theorem ManufacturedReflector.FacingForwardMerge.distinct_le_three
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    (hmerge : A.FacingForwardMerge B)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 3 := by
  obtain ⟨R, before, p, x, after, contact, fresh,
      hB, hrouteSplit, hprefix, hpaths,
      hcandyMem, hsecond⟩ :=
    hmerge.flip_candy
  subst B
  obtain ⟨candyBefore, candyAfter, hcandySplit⟩ :=
    List.append_of_mem hcandyMem
  let alternate := flipAt contact R.actionSwitch
  obtain ⟨tailTravel, htailPositive, _htailLe, htailContact,
      htailAlternate, htailContactPhase, htailAlternatePhase⟩ :=
    R.reverse_candy_suffix_absorbs_twoPhases contact hpaths hsecond
      hcandySplit
  have hrouteSimple :=
    A.orientedRoute_simple
      (ManufacturedReflector.flip R).activatedState
  rw [hrouteSplit] at hrouteSimple
  have hbeforeSimple : SwitchSimple before := by
    unfold SwitchSimple at hrouteSimple ⊢
    simp only [List.map_append, List.map_cons] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).1
  have hbeforeRoute : ∀ passage ∈ before,
      passage ∈ A.orientedRoute
        (ManufacturedReflector.flip R).activatedState := by
    intro passage hpassage
    rw [hrouteSplit]
    exact List.mem_append_left _ hpassage
  have hprefixPhase := A.repair_prefix_two_phase (.flip R) hA hBstart
    hprefix hbeforeSimple hbeforeRoute hpaths
  have hbeforeGrooved : PassagesGrooved contact before :=
    hprefix.grooved_of_switchSimple hbeforeSimple
  have hprefixContact :
      PhysicalTrace w (g, contact) before (p, contact) :=
    hprefix.replay_grooved contact hbeforeGrooved
  have htailAll : ∀ d, ∃ port phase,
      stepN w d (p, contact) = some (port, phase) ∧
        (phase = contact ∨ phase = alternate) := by
    apply R.grooved_return_two_phase contact hpaths hprefixContact hbeforeGrooved
      ?_ (Or.inr rfl) (Or.inl rfl)
    intro current hs
    refine ⟨tailTravel, alternate, htailPositive, ?_, Or.inr rfl, ?_⟩
    · rcases hs with rfl | rfl
      · exact htailContact
      · exact htailAlternate
    · rcases hs with rfl | rfl
      · exact htailContactPhase
      · exact htailAlternatePhase
  have htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes, (stepN w k (p, contact)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (p, contact))).Nodup →
      tailTimes.length ≤ 2 := by
    intro tailTimes _ htailNodup
    let history := [VectorCount.restrict N contact,
      VectorCount.restrict N alternate]
    have hcover : NoveltyCoverOn w N (p, contact) tailTimes [] 2 := by
      refine ⟨history, by simp [history], ?_⟩
      intro d hd
      simp only [List.nil_append]
      obtain ⟨port, phase, hrun, hphase⟩ := htailAll d
      have hvec : restrictedTonguesAt w N (p, contact) d =
          VectorCount.restrict N phase := by
        simp [restrictedTonguesAt, tonguesAt, hrun]
      rw [hvec]
      rcases hphase with h | h <;>
        simp [history, h]
    have hcount := noveltyCoverOn_distinct_count hcover htailNodup
    simpa using hcount
  exact two_phase_prefix_then_direct_tail_distinct_le_succ
    hprefix.sound hprefixPhase htail (by omega) times hlive hnd

end GeneralN

/-!
## Constant protected-repair classification

The existing classifier erased the physical witnesses of its early backward
branches and retained only an `N+2` count.  The two lemmas below keep those
witnesses: the protected approach has two phases, while the retrace/replay
tail has two phases and shares the contact boundary.  Hence each early branch
has at most three vectors.
-/

