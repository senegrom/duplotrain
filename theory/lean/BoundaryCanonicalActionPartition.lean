import BoundaryCanonicalOriginalOverlap

/-!
# A tight action-coordinate partition

This file retains a reusable coordinate-exhaustion fact discovered while
studying the now-closed canonical productive-boundary residual.  The
canonical geometry and its stronger two-phase contradiction are deliberately
not duplicated here.  If the first reflector is a flip, its omitted action
coordinate is absent from the second construction's first writers, and the
one-reserved-coordinate charge is tight, then the action coordinate of a
second flip reflector has only two possible locations:

* it is the first action coordinate itself; or
* it belongs to the first reflector's reusable support.

The second alternative is physical, not merely combinatorial: the second
reflector's final trailing traversal flips that coordinate and therefore
breaks the previously grooved first support.

All statements are uniform in `N` and use only the raw `Wiring`/`stepN`
semantics.
-/

namespace GeneralN

/-- Immediately before a manufactured flip reflector's final trailing
traversal, its action tongue still has its construction-base value. -/
theorem ManufacturedFlipReflector.preReturn_action_eq_base
    {w : Wiring} {g e : Nat}
    (Q : ManufacturedFlipReflector w g e) :
    (ManufacturedReflector.flip Q).preReturn.2 Q.actionSwitch =
      (ManufacturedReflector.flip Q).baseState Q.actionSwitch := by
  have hpre :=
    (ManufacturedReflector.flip Q).preReturn_eq_action_activated
  have hactivated := Q.activated_action_eq_not_base
  have hpreBit := congrFun hpre Q.actionSwitch
  change Q.returnState Q.actionSwitch =
      (flipAt Q.afterReturn Q.actionSwitch) Q.actionSwitch at hpreBit
  change Q.afterReturn Q.actionSwitch = !(Q.base Q.actionSwitch) at hactivated
  change Q.returnState Q.actionSwitch = Q.base Q.actionSwitch
  rw [hpreBit]
  simp [flipAt, hactivated]

/-- A manufactured flip reflector never productively first-writes its own
facing action coordinate during its outward construction.  The facing step
does not change the tongue, and switch simplicity would make any hypothetical
productive write survive to `preReturn`, contradicting
`preReturn_action_eq_base`. -/
theorem ManufacturedFlipReflector.action_not_mem_own_construction_first_writers
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (Q : ManufacturedFlipReflector w g e) :
    Q.actionSwitch ∉
      (ManufacturedReflector.flip Q).constructionFirstWriterSwitches N := by
  intro hmem
  unfold ManufacturedReflector.constructionFirstWriterSwitches at hmem
  obtain ⟨t, ht, hwriter⟩ := List.mem_map.mp hmem
  have htData := mem_rawFirstWriterTimes_iff.mp ht
  have hsurvives :=
    (ManufacturedReflector.flip Q).exploration_trace
      |>.simple_raw_productive_writer_survives
        hN (ManufacturedReflector.flip Q).exploration_simple
          htData.1 htData.2.1
  rw [hwriter] at hsurvives
  exact hsurvives Q.preReturn_action_eq_base

/-- If a second flip reflector's action coordinate lies on an old reusable
support which is grooved immediately before the second return, the second
activation necessarily breaks that old support. -/
theorem ManufacturedFlipReflector.activated_breaks_reusable_support_of_action_mem
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (Q : ManufacturedFlipReflector w e g)
    (hpre : PathGrooves A.toSupported.paths
      (ManufacturedReflector.flip Q).preReturn.2)
    (hmem : Q.actionSwitch ∈ A.reusableSwitches) :
    Not (PathGrooves A.toSupported.paths
      (ManufacturedReflector.flip Q).activatedState) := by
  obtain ⟨path, hpath, old, hold, hswitch⟩ :=
    A.mem_reusableSwitches hmem
  have hgroove := hpre path hpath old hold
  have hpreEq :=
    (ManufacturedReflector.flip Q).preReturn_eq_action_activated
  have hpreBit := congrFun hpreEq Q.actionSwitch
  change Q.returnState Q.actionSwitch =
      (flipAt Q.afterReturn Q.actionSwitch) Q.actionSwitch at hpreBit
  have hchangeAction : Q.afterReturn Q.actionSwitch ≠
      Q.returnState Q.actionSwitch := by
    rw [hpreBit]
    simp [flipAt]
  have hchange :
      (ManufacturedReflector.flip Q).activatedState (passageSwitch old) ≠
        (ManufacturedReflector.flip Q).preReturn.2 (passageSwitch old) := by
    change Q.afterReturn (passageSwitch old) ≠
      Q.returnState (passageSwitch old)
    rw [hswitch]
    exact hchangeAction
  have hbroken := changed_tongue_breaks_groove hgroove hchange
  intro hgrooves
  exact hbroken (hgrooves path hpath old hold)

/-- Tight one-reserved-coordinate charge exhausts all switch coordinates.
The second flip's own action is not one of its construction first writers,
so it must be either the reserved first action or a coordinate of the first
reusable support. -/
theorem ManufacturedFlipReflector.second_action_eq_or_mem_first_reusable_of_tight
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (Q : ManufacturedFlipReflector w e g)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
        (ManufacturedReflector.flip Q).baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
        (ManufacturedReflector.flip Q).preReturn.2)
    (hfirstActionAbsent : R.actionSwitch ∉
      (ManufacturedReflector.flip Q).constructionFirstWriterSwitches N)
    (htight :
      (ManufacturedReflector.flip R).reusableSwitches.length +
          (rawFirstWriterTimes w N
            (e, (ManufacturedReflector.flip Q).baseState)
            (ManufacturedReflector.flip Q).exploration.length).length + 1 = N) :
    Q.actionSwitch = R.actionSwitch ∨
      Q.actionSwitch ∈
        (ManufacturedReflector.flip R).reusableSwitches := by
  by_cases heq : Q.actionSwitch = R.actionSwitch
  · exact Or.inl heq
  · apply Or.inr
    apply Classical.byContradiction
    intro hnotReusable
    have htwo :=
      (ManufacturedReflector.flip R).reusable_add_second_first_writers_add_two_reserved_le
          hN (ManufacturedReflector.flip Q)
            hbaseGrooves hpreGrooves
            (R.action_lt hN) (Q.action_lt hN) (Ne.symm heq)
            R.action_not_mem_reusable hfirstActionAbsent
            hnotReusable
            (Q.action_not_mem_own_construction_first_writers hN)
    omega

/-- Physical form of the tight partition: unequal action coordinates force
the second activation to damage the first reusable support. -/
theorem ManufacturedFlipReflector.second_action_eq_or_breaks_first_support_of_tight
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (Q : ManufacturedFlipReflector w e g)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
        (ManufacturedReflector.flip Q).baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
        (ManufacturedReflector.flip Q).preReturn.2)
    (hfirstActionAbsent : R.actionSwitch ∉
      (ManufacturedReflector.flip Q).constructionFirstWriterSwitches N)
    (htight :
      (ManufacturedReflector.flip R).reusableSwitches.length +
          (rawFirstWriterTimes w N
            (e, (ManufacturedReflector.flip Q).baseState)
            (ManufacturedReflector.flip Q).exploration.length).length + 1 = N) :
    Q.actionSwitch = R.actionSwitch ∨
      Not (PathGrooves
        (ManufacturedReflector.flip R).toSupported.paths
          (ManufacturedReflector.flip Q).activatedState) := by
  rcases R.second_action_eq_or_mem_first_reusable_of_tight
      hN Q hbaseGrooves hpreGrooves hfirstActionAbsent htight with
    heq | hmem
  · exact Or.inl heq
  · exact Or.inr
      (Q.activated_breaks_reusable_support_of_action_mem
        (ManufacturedReflector.flip R) hpreGrooves hmem)


end GeneralN
