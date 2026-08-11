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

/-- Two states which groove the same passage agree on that switch's tongue. -/
theorem grooved_states_agree_on_passage
    {u v : Tongues} {p x : Nat}
    (hu : arrive u x = (p, u))
    (hv : arrive v x = (p, v)) :
    u (x / 3) = v (x / 3) := by
  by_cases hx : x % 3 = 0
  · have hpu : branchPort (x / 3) (u (x / 3)) = p := by
      simpa [arrive, hx] using congrArg Prod.fst hu
    have hpv : branchPort (x / 3) (v (x / 3)) = p := by
      simpa [arrive, hx] using congrArg Prod.fst hv
    cases huval : u (x / 3) <;>
      cases hvval : v (x / 3) <;>
      simp_all [branchPort] <;> omega
  · have hpinu : pin u x = u := by
      simpa [arrive, hx] using congrArg Prod.snd hu
    have hpinv : pin v x = v := by
      simpa [arrive, hx] using congrArg Prod.snd hv
    have huval := congrFun hpinu (x / 3)
    have hvval := congrFun hpinv (x / 3)
    simp only [pin, if_pos] at huval hvval
    exact huval.symm.trans hvval

/-- States grooving the same support family agree at every switch represented
by a support passage. -/
theorem pathGrooves_agree_at_support_passage
    {paths : List (List Passage)} {u v : Tongues}
    (hu : PathGrooves paths u) (hv : PathGrooves paths v)
    {path : List Passage} (hpath : path ∈ paths)
    {passage : Passage} (hpassage : passage ∈ path) :
    u (passageSwitch passage) = v (passageSwitch passage) := by
  have hgu := hu path hpath passage hpassage
  have hgv := hv path hpath passage hpassage
  have hagree := grooved_states_agree_on_passage hgu hgv
  have hexit := arrive_exit_switch u passage.2
  rw [hgu] at hexit
  simpa [passageSwitch, hexit] using hagree

/-- Every net changed coordinate of a switch-simple prefix which follows the
current repair route while preserving `B`'s support is `B`'s final return
switch. -/
theorem ManufacturedReflector.repair_prefix_changes_only_protected_return
    {w : Wiring} {g e : Nat}
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
    (hBcontact : PathGrooves B.toSupported.paths contact) :
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
  have hrefForward : arrive reference p = (x, reference) :=
    groove_forward hrefBack
  have hswitch' : p / 3 = j := by
    simpa [passageSwitch] using hswitch
  have hchangedLocal : v (p / 3) ≠ u (p / 3) := by
    simpa [hswitch'] using hvu
  obtain ⟨hpBranch, _hxStem, hvPin, _hback⟩ :=
    changed_arrival_is_trailing harrive hchangedLocal
  have hvValue : v (p / 3) = bval p := by
    rw [hvPin]
    simp [pin]
  have hrefPin : pin reference p = reference := by
    unfold arrive at hrefForward
    rw [if_neg hpBranch] at hrefForward
    exact (Prod.mk.inj hrefForward).2
  have hrefValue : reference (p / 3) = bval p := by
    have h := congrFun hrefPin (p / 3)
    simp only [pin, if_pos] at h
    exact h.symm
  have hvReference : v j = reference j := by
    rw [← hswitch']
    exact hvValue.trans hrefValue.symm
  have hrefNeState : reference j ≠ B.activatedState j := by
    intro heq
    apply hvu
    calc
      v j = reference j := hvReference
      _ = B.activatedState j := heq
      _ = u j := huStart'.symm
  have hrefBase : reference j = B.baseState j := by
    by_cases hbase : reference j = B.baseState j
    · exact hbase
    · exact (hrefNeState (hguard j hbase)).elim
  have hactivatedChange :
      B.activatedState j ≠ B.baseState j := by
    intro heq
    apply hvu
    calc
      v j = reference j := hvReference
      _ = B.baseState j := hrefBase
      _ = B.activatedState j := heq.symm
      _ = u j := huStart'.symm
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

/-- **Two-phase protected repair lead.** -/
theorem ManufacturedReflector.repair_prefix_two_phase
    {w : Wiring} {g e : Nat}
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
    (hBcontact : PathGrooves B.toSupported.paths contact) :
    ∀ d, d ≤ approach.length →
      ∃ port phase,
        stepN w d (g, B.activatedState) = some (port, phase) ∧
        (phase = B.activatedState ∨ phase = contact) := by
  exact hprefix.two_phase_of_net_changes_only hsimple
    (A.repair_prefix_changes_only_protected_return B hA hBstart
      hprefix hsimple hroute hBcontact)

end GeneralN
