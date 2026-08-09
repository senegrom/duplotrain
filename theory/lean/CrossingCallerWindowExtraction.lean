import CrossingCallerSerialAssembly

/-!
# Exact placement for the crossing-caller serial branch

This file keeps the physical caller window and the manufactured reflector
window in the same absolute clock.  The first theorem removes the former
coarse `travel` deadline: only the concrete prefix ending at the oriented
caller contact must occur by the first selected close.
-/

namespace GeneralN

/-- A crossing frame whose opening lies inside the caller runway gives the
literal forward contact consumed by `early_forward_contact_exact_false`.
The deadline is the exact length of the concrete approach, not the full
manufactured-reflector travel bound. -/
theorem RawOverlappingFiveWindowReduction.early_crossing_caller_exact_false
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
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
    (hminimal : forall t, returnTime ≤ t -> t < escape ->
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
    (hdeadline : shift + (approach.length + 1) ≤ R.z1 + 1) : False := by
  obtain ⟨old, foundCur, foundNext, foundC, hold,
      hfoundC, hswitch, hfoundCur, hfoundNext, hfresh,
      holdGroove, _hflip, hchanged, hforward⟩ :=
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
  have hquiet : forall t, returnTime ≤ t ->
      t < returnTime + quietSpan ->
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
  have hentryC : cur.1 / 3 = C := by
    simpa [rawWriterAt, rawEntryAt, hcur] using hC.symm
  exact R.early_forward_contact_exact_false hN A B
    hrouteSplit happroach hBcur hfreshC
    holdPath holdRunway holdOriented
    (hswitchC.trans hentryC.symm)
    (by simpa [hentryC] using hchangedC)
    holdGroove hforwardC hreach hdeadline

end GeneralN
