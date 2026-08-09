import MellitSupportInteraction

/-!
# Closing the forward crossing-caller branch

`crossing_frame_open_in_caller_oriented_contact` now proves more than an
endpoint dichotomy: because the old caller occurrence is the productive
opening of the same last-writer frame, it exits through the switch stem.
Consequently the first productive escape after the completed return meets
that caller passage in the forward orientation.

This file instantiates that raw contact as an actual
`ChangedForwardMerge`.  The resulting early three-vector tail is transported
to the five selected closes and contradicts the literal four-cover
obstruction.  What remains outside the theorem is only the global placement
of the already manufactured pair and the proof that the selected escape lies
on the older reflector's repair route early enough.
-/

namespace GeneralN

/-- Every runway passage occurs in either selected orientation of a
manufactured reflector.  The runway is the common prefix; only the lobe/candy
suffix depends on the action tongue. -/
theorem ManufacturedReflector.runway_mem_orientedRoute
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues)
    {passage : Passage} (hpassage : passage ∈ A.runway) :
    passage ∈ A.orientedRoute state := by
  cases A with
  | stay R =>
      exact List.mem_append_left _ hpassage
  | flip R =>
      by_cases hselected :
          state R.actionSwitch = bval R.firstArm
      · simp only [ManufacturedReflector.orientedRoute, hselected,
          if_pos]
        exact List.mem_append_left _ hpassage
      · simp only [ManufacturedReflector.orientedRoute, hselected,
          ]
        exact List.mem_append_left _ hpassage

/-- Every switch occurring in a reusable reflector support is one of the
`N` switches bounded by the ambient wiring. -/
theorem ManufacturedReflector.support_passage_switch_lt
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    {path : List Passage} (hpath : path ∈ A.toSupported.paths)
    {passage : Passage} (hpassage : passage ∈ path) :
    passageSwitch passage < N := by
  apply A.exploration_trace.switch_lt hN passage
  cases A with
  | stay R =>
      change path ∈ [R.runway, [(R.mouth, R.arm)]] at hpath
      rcases List.mem_cons.mp hpath with hrunway | hcore
      · subst path
        exact List.mem_append_left _ hpassage
      · have hpathEq : path = [(R.mouth, R.arm)] :=
          List.eq_of_mem_singleton hcore
        subst path
        have hp : passage = (R.mouth, R.arm) :=
          List.eq_of_mem_singleton hpassage
        subst passage
        exact List.mem_append_right _ (by simp)
  | flip R =>
      change path ∈ [R.runway, R.candy] at hpath
      rcases List.mem_cons.mp hpath with hrunway | hcandy
      · subst path
        exact List.mem_append_left _ hpassage
      · have hpathEq : path = R.candy :=
          List.eq_of_mem_singleton hcandy
        subst path
        exact List.mem_append_right _
          (List.mem_cons_of_mem _ hpassage)

/-- Equality of bounded tongue vectors transfers every reusable support
groove.  This is the precise bridge from a productive-free raw interval to
the complete protected-support premise used by the repair theorem. -/
theorem ManufacturedReflector.pathGrooves_of_restrict_eq
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    {before after : Tongues}
    (hrestrict : VectorCount.restrict N after =
      VectorCount.restrict N before)
    (hgrooves : PathGrooves A.toSupported.paths before) :
    PathGrooves A.toSupported.paths after := by
  intro path hpath passage hpassage
  have hold := hgrooves path hpath passage hpassage
  have hexitSwitch : passage.2 / 3 = passageSwitch passage := by
    have hs := arrive_exit_switch before passage.2
    rw [hold] at hs
    exact hs.symm
  apply groove_transfer hold
  rw [hexitSwitch]
  exact restrict_eq_apply hrestrict
    (A.support_passage_switch_lt hN hpath hpassage)

/-- **The raw crossing-caller branch closes once the manufactured pair is
placed on the selected repair route.**

The hypotheses before `A` are exactly those of the raw crossing theorem.
The remaining hypotheses identify the completed caller as `B`'s runway,
place the first escape on `A`'s selected repair route, and bound the repair
lead by the paid first selected post-state.  No merge or novelty-cover
hypothesis is assumed.

The proof obtains the concrete caller passage from the raw last-writer frame,
transfers all of `B`'s support grooves across the productive-free interval,
uses the now-forced forward endpoint to construct `ChangedForwardMerge`, and
then builds the literal forbidden four-cover. -/
theorem RawOverlappingFiveWindowReduction.early_crossing_caller_false
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    {callerStart returnTime left escape callerEdge : Nat}
    {callerState settled : Tongues}
    {callerFinish : Nat × Tongues} {caller : List Passage}
    {g e : Nat}
    (hcallerStart :
      stepN w callerStart start = some (e, callerState))
    (hcaller : PhysicalTrace w (e, callerState) caller callerFinish)
    (hcallerGrooved : PassagesGrooved settled caller)
    (hreturn :
      stepN w returnTime start = some (callerEdge, settled))
    (hreturnEscape : returnTime ≤ escape)
    (hminimal : ∀ t, returnTime ≤ t → t < escape →
      ¬ RawProductiveAt w N start t)
    (F : RawLastWriterFrame w N start left escape)
    (hleftStart : callerStart ≤ left)
    (hleftEnd : left < callerStart + caller.length)
    {shift C : Nat} {cur next : Nat × Tongues}
    {approach suffix : List Passage}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (hcallerRunway : caller =
      (ManufacturedReflector.flip B).runway)
    (hBsettled : PathGrooves
      (ManufacturedReflector.flip B).toSupported.paths settled)
    (hcur : stepN w escape start = some cur)
    (hnext : stepN w (escape + 1) start = some next)
    (hC : C = rawWriterAt w start escape)
    (hrouteSplit : A.orientedRoute
        (ManufacturedReflector.flip B).activatedState =
      approach ++ (cur.1, 3 * C) :: suffix)
    (happroach : PhysicalTrace w
      (g, (ManufacturedReflector.flip B).activatedState)
      approach cur)
    (hreach : stepN w shift start =
      some (g, (ManufacturedReflector.flip B).activatedState))
    (hlead : shift + A.toSupported.travel ≤ R.z1 + 1) : False := by
  obtain ⟨old, foundCur, foundNext, foundC, hold,
      hfoundC, hswitch, hfoundCur, hfoundNext, hfresh,
      holdGroove, hflip, hchanged, hforward⟩ :=
    crossing_frame_open_in_caller_oriented_contact hN
      hcallerStart hcaller
      hcallerGrooved hreturn hreturnEscape hminimal F
      hleftStart hleftEnd
  have hcurEq : foundCur = cur := by
    rw [hcur] at hfoundCur
    exact (Option.some.inj hfoundCur).symm
  have hnextEq : foundNext = next := by
    rw [hnext] at hfoundNext
    exact (Option.some.inj hfoundNext).symm
  have hCEq : foundC = C := hfoundC.trans hC.symm
  subst foundCur
  subst foundNext
  subst foundC
  let quietSpan := escape - returnTime
  have hreturnSum : returnTime + quietSpan = escape := by
    dsimp [quietSpan]
    omega
  have hquiet : ∀ t, returnTime ≤ t →
      t < returnTime + quietSpan →
      ¬ RawProductiveAt w N start t := by
    intro t ht hbound
    apply hminimal t ht
    rw [hreturnSum] at hbound
    exact hbound
  have hquietVector := restrictedTonguesAt_eq_of_quiet_interval
    (first := returnTime) (span := quietSpan) (finish := cur)
    (by simpa [hreturnSum] using hcur) hquiet
  have hrestrict : VectorCount.restrict N cur.2 =
      VectorCount.restrict N settled := by
    simpa [restrictedTonguesAt, tonguesAt, hreturnSum,
      hcur, hreturn] using hquietVector
  have hBcur : PathGrooves
      (ManufacturedReflector.flip B).toSupported.paths cur.2 :=
    (ManufacturedReflector.flip B).pathGrooves_of_restrict_eq
      hN hrestrict hBsettled
  have holdRunway : old ∈
      (ManufacturedReflector.flip B).runway := by
    rw [← hcallerRunway]
    exact hold
  have holdPath :
      (ManufacturedReflector.flip B).runway ∈
        (ManufacturedReflector.flip B).toSupported.paths :=
    (ManufacturedReflector.flip B).runway_mem_support
  have holdOriented : old ∈
      (ManufacturedReflector.flip B).orientedRoute cur.2 :=
    (ManufacturedReflector.flip B).runway_mem_orientedRoute
      cur.2 holdRunway
  have hfreshC : arrive cur.2 cur.1 = (3 * C, next.2) := by
    simpa [hC] using hfresh
  have hswitchC : passageSwitch old = C := by
    simpa [hC] using hswitch
  have hchangedC : next.2 C ≠ cur.2 C := by
    simpa [hC] using hchanged
  have hforwardC : 3 * C = old.2 := by
    simpa [hC] using hforward
  have hmerge : A.ChangedForwardMerge
      (ManufacturedReflector.flip B) :=
    have hentryC : cur.1 / 3 = C := by
      simpa [rawWriterAt, rawEntryAt, hcur] using hC.symm
    A.changedForwardMerge_of_forward_contact
      (ManufacturedReflector.flip B)
      hrouteSplit happroach hBcur
      hfreshC
      holdPath holdRunway holdOriented
      (hswitchC.trans hentryC.symm)
      (by simpa [hentryC] using hchangedC)
      holdGroove hforwardC
  exact R.early_changedForward_second_repeat_false
    hN hmerge hreach hlead

end GeneralN
