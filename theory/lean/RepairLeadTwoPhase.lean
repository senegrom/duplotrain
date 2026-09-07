import SimpleTraceOneNetChange
import TrackGlobalRepair

/-!
# A protected repair lead can change only the protected return switch

The protected reflector's activation differs from its base only on its
reusable support or at its final repeated-mouth switch.  A repair prefix keeps
the reusable support grooved.  Its reference also agrees with the activated
state at any private action coordinate.  Consequently every net change in the
prefix must occur at the protected reflector's final return switch.

Combined with the switch-simple trace theorem, every such repair lead has at
most two tongue phases.
-/

namespace GeneralN

/-- States grooving the same support family agree at every switch represented
by a support passage. -/
theorem pathGrooves_agree_at_support_passage
    {paths : List (List Passage)} {u v : Tongues}
    (hu : PathGrooves paths u) (hv : PathGrooves paths v)
    {path : List Passage} (hpath : path ∈ paths)
    {passage : Passage} (hpassage : passage ∈ path) :
    u (passageSwitch passage) = v (passageSwitch passage) := by
  exact same_groove_same_tongue (hu path hpath passage hpassage) (hv path hpath passage hpassage)


section
variable {w : Wiring} {g e : Nat}
  (A : ManufacturedReflector w g e)
  (B : ManufacturedReflector w e g)
  (hA : PathGrooves A.toSupported.paths B.baseState)
  (hBstart : PathGrooves B.toSupported.paths B.activatedState)
  {approach : List Passage} {finishPort : Nat} {contact : Tongues}
  (hprefix : PhysicalTrace w (g, B.activatedState) approach
    (finishPort, contact))
  (hsimple : SwitchSimple approach)
  (hroute : ∀ passage ∈ approach,
    passage ∈ A.orientedRoute B.activatedState)
  (hBcontact : PathGrooves B.toSupported.paths contact)
include w g e A B hA hBstart approach finishPort contact hprefix hsimple hroute hBcontact

/-- Every net changed coordinate of a switch-simple prefix which follows the
current repair route while preserving `B`'s support is `B`'s final return
switch. -/
theorem ManufacturedReflector.repair_prefix_changes_only_protected_return :
    ∀ j, contact j ≠ B.activatedState j →
      j = B.preReturn.1 / 3 := by
  obtain ⟨reference, _hreferencePaths, _hrouteEq, _hfinishEq,
      hreferenceGrooved, hguard⟩ :=
    A.current_route_reference B.baseState B.activatedState hA
  intro j hchange
  obtain ⟨before, p, x, after, u, v,
      happSplit, hswitch, hbefore, harrive,
      huStart, _hcontactV, hvu⟩ :=
    hprefix.changed_switch_has_changed_passage hsimple hchange
  have huStart' : u j = B.activatedState j := by
    simpa using huStart
  have hmemApproach : (p, x) ∈ approach := by
    rw [happSplit]
    exact List.mem_append_right before List.mem_cons_self
  have hmemRoute : (p, x) ∈ A.orientedRoute B.activatedState :=
    hroute (p, x) hmemApproach
  have hrefBack : arrive reference x = (p, reference) :=
    hreferenceGrooved (p, x) hmemRoute
  have hvReference : v j = reference j := by
    have hback := arrive_back u p
    rw [harrive] at hback
    simpa [hswitch] using same_groove_same_tongue (old := (p, x)) hback hrefBack
  have hactivatedChange : B.activatedState j ≠ B.baseState j := by
    have hguardAt := hguard j
    grind
  rcases B.activated_change_return_or_exploration hactivatedChange with
    hreturn | hexploration
  · exact hreturn.1
  · obtain ⟨bBefore, bp, bx, bAfter, bu, bv,
        hBsplit, hBswitch, hBbefore, hBarrive,
        hBbase, hBactivated, hBchanged⟩ := hexploration
    have hBmem : (bp, bx) ∈ B.exploration := by
      rw [hBsplit]
      exact List.mem_append_right bBefore List.mem_cons_self
    obtain ⟨path, hpath, hpassage⟩ :=
      B.changed_exploration_passage_mem_support
        hBmem hBarrive (by
          simpa [hBswitch] using hBchanged)
    have hagree := pathGrooves_agree_at_support_passage
      hBstart hBcontact hpath hpassage
    have hj : passageSwitch (bp, bx) = j := hBswitch
    exfalso
    apply hchange
    simpa [hj] using hagree.symm

/-- Every support-preserving protected repair prefix ends in either the
protected reflector's activated state or its pre-return state.  For a flip
reflector these are the two values of its action tongue; for a stay
reflector the core groove rules out even that one-coordinate difference. -/
theorem ManufacturedReflector.repair_prefix_contact_eq_activated_or_preReturn :
    contact = B.activatedState ∨ contact = B.preReturn.2 := by
  have hchanges := A.repair_prefix_changes_only_protected_return
    B hA hBstart hprefix hsimple hroute hBcontact
  cases B with
  | stay R =>
      left
      have hkey := grooved_states_agree_on_passage
        (passagesGrooved_singleton.mp (pathGrooves_pair.mp hBstart).2)
        (passagesGrooved_singleton.mp (pathGrooves_pair.mp hBcontact).2)
      funext j
      by_cases hj : contact j = R.returnState j
      · exact hj
      · have hs := hchanges j hj
        change j = R.arm / 3 at hs
        exact hs ▸ hkey.symm
  | flip R =>
      change contact = R.afterReturn ∨ contact = R.returnState
      have hrelation := tongues_eq_or_eq_flipAt_of_changes_only
        (u := R.afterReturn) (v := contact) (k := R.actionSwitch)
        (fun j hj => (hchanges j hj).trans R.secondArm_switch)
      have hpre := (ManufacturedReflector.flip R).preReturn_eq_action_activated
      change R.returnState = flipAt R.afterReturn R.actionSwitch at hpre
      rcases hrelation with heq | heq
      · exact Or.inl heq.symm
      · right; rw [hpre, heq, flipAt_flipAt]

/-- **Two-phase protected repair lead.** -/
theorem ManufacturedReflector.repair_prefix_two_phase :
    ∀ d, d ≤ approach.length →
      ∃ port phase,
        stepN w d (g, B.activatedState) = some (port, phase) ∧
        (phase = B.activatedState ∨ phase = contact) := by
  exact hprefix.two_phase_of_net_changes_only hsimple
    (A.repair_prefix_changes_only_protected_return B hA hBstart
      hprefix hsimple hroute hBcontact)

end

end GeneralN
