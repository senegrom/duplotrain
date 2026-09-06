import FacingForwardNovelty
import FirstCycleCountSharp
import TrackEarlyRepairConstant
import EarlyFacingConstant
import ShortSuffixCount

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

