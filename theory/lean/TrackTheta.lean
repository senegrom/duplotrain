import TrackNormalForm

/-!
# The theta-intersection engine

This file studies the only obstruction left by the supported-reflector normal
form: one reflector flips a switch lying on the other reflector's grooved
support.  The local core is that a flipped groove has only two behaviours.
Approached trailing-first it repairs itself; approached facing-first it leaves
through the third arm.  For a manufactured lobe that third arm is precisely
the entrance into the older reflector, which is the theta capture.
-/

namespace GeneralN

/-! ## Equivariance away from the flipped switch -/

theorem pin_flip_other {u : Tongues} {p k : Nat}
    (hpk : p / 3 ≠ k) :
    pin (flipAt u k) p = flipAt (pin u p) k := by
  funext j
  by_cases hj : j = p / 3 <;> simp [pin, flipAt, hj, hpk]

/-- Flipping an unvisited switch commutes with one local lazy-point
traversal. -/
theorem arrive_flip_other {u v : Tongues} {p x k : Nat}
    (harrive : arrive u p = (x, v))
    (hpk : p / 3 ≠ k) :
    arrive (flipAt u k) p = (x, flipAt v k) := by
  unfold arrive at harrive ⊢
  split at harrive <;> cases harrive <;> simp_all [flipAt, pin_flip_other]

/-- A passage which genuinely changes its switch is necessarily trailing:
its entry is a branch, its exit is the stem, and immediately re-entering
that stem follows the freshly selected branch back.  This is the local
algebra behind the forward theta splice. -/
theorem changed_arrival_is_trailing
    {u v : Tongues} {p x : Nat}
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    p % 3 ≠ 0 ∧ x = 3 * (p / 3) ∧ v = pin u p := by
  unfold arrive at harrive
  split at harrive <;> cases harrive <;> simp_all

theorem changed_arrival_eq_flipAt
    {u v : Tongues} {p x : Nat}
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    v = flipAt u (p / 3) := by
  obtain ⟨_, _, rfl⟩ := changed_arrival_is_trailing harrive hchanged
  apply pin_eq_flipAt rfl
  simp only [pin] at hchanged
  cases hu : u (p / 3) <;> cases hb : bval p <;> simp_all

/-- Deterministic traces from one configuration coincide until one ends;
the remainder is itself a trace from that endpoint. -/
theorem physicalTrace_prefix_comparable_with_endpoints
    {w : Wiring} {start finishA finishB : Nat × Tongues} {left right : List Passage}
    (hleft : PhysicalTrace w start left finishA)
    (hright : PhysicalTrace w start right finishB) :
    (∃ suffix, right = left ++ suffix ∧ PhysicalTrace w finishA suffix finishB) ∨
    (∃ suffix, left = right ++ suffix ∧ PhysicalTrace w finishB suffix finishA) := by
  induction hleft generalizing right finishB with
  | nil c => exact Or.inl ⟨right, rfl, hright⟩
  | @cons p x q u v rest finishA harrive hlink tail ih =>
      cases hright with
      | nil => exact Or.inr ⟨_, rfl, PhysicalTrace.cons harrive hlink tail⟩
      | @cons _ x₂ q₂ _ v₂ right finishB harrive₂ hlink₂ tail₂ =>
          have hlocal : (x, v) = (x₂, v₂) := harrive.symm.trans harrive₂
          cases hlocal
          have hnext : q = q₂ := by grind
          subst q₂
          rcases ih tail₂ with ⟨suffix, hs, ht⟩ | ⟨suffix, hs, ht⟩
          · exact Or.inl ⟨suffix, by simp [hs], ht⟩
          · exact Or.inr ⟨suffix, by simp [hs], ht⟩

/-- A complete physical trace can be replayed after flipping a switch absent
from the trace.  Every intermediate state is simply conjugated by that flip.
-/
theorem PhysicalTrace.flip_unvisited
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage} {k : Nat}
    (htrace : PhysicalTrace w start passages finish)
    (hforeign : ∀ passage ∈ passages,
      passageSwitch passage ≠ k) :
    PhysicalTrace w (start.1, flipAt start.2 k) passages
      (finish.1, flipAt finish.2 k) := by
  induction htrace with
  | nil c => exact PhysicalTrace.nil _
  | @cons p x q u v passages finish harrive hlink tail ih =>
      have hpk : p / 3 ≠ k := by
        simpa [passageSwitch] using
          hforeign (p, x) List.mem_cons_self
      have harrive' := arrive_flip_other harrive hpk
      apply PhysicalTrace.cons harrive' hlink
      apply ih
      intro passage hp
      exact hforeign passage (List.mem_cons_of_mem _ hp)

private theorem nodup_prefix_head_reverse_tail
    {pre tail : List Nat} {head : Nat}
    (hnd : (pre ++ head :: tail).Nodup) :
    (pre ++ head :: tail.reverse).Nodup := by grind

theorem PhysicalTrace.passage_exit_switch
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) :
    ∀ passage ∈ passages,
      passage.2 / 3 = passageSwitch passage := by
  induction htrace with
  | nil =>
      intro passage hp
      cases hp
  | @cons p x q u v passages finish harrive hlink tail ih =>
      intro passage hp
      rcases List.mem_cons.mp hp with hhead | htail
      · subst passage
        have hs := arrive_exit_switch u p
        rw [harrive] at hs
        exact hs
      · exact ih passage htail

theorem map_passageSwitch_reversePassages
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) :
    (reversePassages passages).map passageSwitch =
      (passages.map passageSwitch).reverse := by
  change (passages.reverse.map Prod.swap).map passageSwitch = _
  rw [List.map_map, ← List.map_reverse]
  exact List.map_congr_left fun passage hp =>
    htrace.passage_exit_switch passage (List.mem_reverse.mp hp)

/-! ## One deliberately broken groove -/

/-- If a grooved passage is entered trailing-first after its switch has been
flipped, the trailing move repairs the tongue and follows the old passage.
This is the self-healing half of the theta case. -/
theorem flipped_passage_forward_trailing
    {u : Tongues} {p x : Nat}
    (hforward : arrive u p = (x, u))
    (hpbranch : p % 3 ≠ 0) :
    arrive (flipAt u (p / 3)) p = (x, u) := by
  have hpin : pin (flipAt u (p / 3)) p = pin u p := by
    funext j
    by_cases hj : j = p / 3 <;> simp [pin, flipAt, hj]
  simpa only [arrive, if_neg hpbranch, hpin] using hforward

/-- After the crossed passage at a first revisit, every groove away from the
revisited switch survives.  In particular, the simple runway and the candy
interior are simultaneously grooved in the state in which the train starts
its forced retrace.  This is the activation invariant needed to manufacture
the next reflector from the far side. -/
theorem crossed_revisit_support_grooved
    {w : Wiring} {start : Nat × Tongues}
    {runway path : List Passage}
    {p x q y : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hsw : p / 3 = q / 3)
    (hrepeat : arrive u q = (y, v)) :
    PathGrooves [runway, path] v := by
  have hfull := hrunway.append hexcursion
  have hold := hfull.grooved_of_switchSimple hsimple
  have hs : (runway.map passageSwitch ++ p / 3 :: path.map passageSwitch).Nodup := by
    simpa only [SwitchSimple, List.map_append, List.map_cons, passageSwitch] using hsimple
  have hgrooved : PassagesGrooved v (runway ++ path) := by
    apply PassagesGrooved.transfer
      (fun passage hp => hold passage (by grind))
    intro passage hp
    apply arrive_preserves_other hrepeat
    have hm : passageSwitch passage ∈ runway.map passageSwitch ++ path.map passageSwitch := by
      simpa only [List.map_append] using List.mem_map.mpr ⟨passage, hp, rfl⟩
    grind
  exact pathGrooves_pair.mpr
    ⟨fun passage hp => hgrooved passage (List.mem_append_left _ hp),
     fun passage hp => hgrooved passage (List.mem_append_right _ hp)⟩

/-! ## Retaining the construction data -/

/-- The nondegenerate reflector produced by a crossed first revisit, with
the runway and candy traces retained.  `SupportedReflector` is ideal for
composition, but deliberately forgets exactly this data; theta capture needs
it once, at the intersected mouth. -/
structure ManufacturedFlipReflector (w : Wiring) (g e : Nat) where
  base : Tongues
  mouthState : Tongues
  returnState : Tongues
  afterReturn : Tongues
  runway : List Passage
  candy : List Passage
  mouth : Nat
  firstArm : Nat
  secondArm : Nat
  runwayTrace :
    PhysicalTrace w (g, base) runway (mouth, mouthState)
  candyTrace :
    PhysicalTrace w (mouth, mouthState)
      ((mouth, firstArm) :: candy) (secondArm, returnState)
  simple : SwitchSimple (runway ++ (mouth, firstArm) :: candy)
  crossed : arrive returnState secondArm = (mouth, afterReturn)
  arms_ne : firstArm ≠ secondArm
  entryEdge : w.link e = some g

def ManufacturedFlipReflector.actionSwitch
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) : Nat :=
  A.mouth / 3

def ManufacturedFlipReflector.toSupported
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    SupportedReflector w g e where
  travel := 2 * A.runway.length + A.candy.length + 2
  paths := [A.runway, A.candy]
  action := .flip A.actionSwitch
  run := by
    have href := crossed_revisit_full_reflector w A.runwayTrace
      A.candyTrace A.simple A.crossed A.arms_ne A.entryEdge
    intro state hs
    obtain ⟨hstep, hnext⟩ := href state (pathGrooves_pair.mp hs)
    exact ⟨hstep, pathGrooves_pair.mpr hnext⟩

section
variable {w : Wiring} {g e : Nat}
  (A : ManufacturedFlipReflector w g e)
include w g e A

private theorem ManufacturedFlipReflector.port_geometry :
    A.mouth % 3 = 0 ∧ A.firstArm % 3 ≠ 0 ∧ A.secondArm % 3 ≠ 0 ∧
      A.mouth / 3 = A.firstArm / 3 ∧ A.mouth / 3 = A.secondArm / 3 := by
  obtain ⟨_, hold⟩ := A.candyTrace.head_arrive.2
  exact crossed_arrivals_geometry hold A.crossed A.arms_ne

/-- A manufactured lobe's mouth is the stem, with two distinct branch arms. -/
theorem ManufacturedFlipReflector.mouth_is_stem : A.mouth % 3 = 0 :=
  A.port_geometry.1

theorem ManufacturedFlipReflector.firstArm_switch : A.firstArm / 3 = A.actionSwitch :=
  A.port_geometry.2.2.2.1.symm

theorem ManufacturedFlipReflector.secondArm_switch : A.secondArm / 3 = A.actionSwitch :=
  A.port_geometry.2.2.2.2.symm

theorem ManufacturedFlipReflector.firstArm_branch : A.firstArm % 3 ≠ 0 :=
  A.port_geometry.2.1

theorem ManufacturedFlipReflector.secondArm_branch : A.secondArm % 3 ≠ 0 :=
  A.port_geometry.2.2.1

theorem ManufacturedFlipReflector.selected_arm
    (state : Tongues) :
    state A.actionSwitch = bval A.firstArm ∨
      state A.actionSwitch = bval A.secondArm := by
  have hopp := branch_values_opposite A.firstArm_branch A.secondArm_branch
    (A.firstArm_switch.trans A.secondArm_switch.symm) A.arms_ne
  cases hs : state A.actionSwitch <;>
    cases hf : bval A.firstArm <;>
    cases hq : bval A.secondArm <;>
    simp_all

/-- Rebase the manufactured runway to any state satisfying its grooves. -/
theorem ManufacturedFlipReflector.runway_trace
    (state : Tongues)
    (hgrooved : PassagesGrooved state A.runway) :
    PhysicalTrace w (g, state) A.runway (A.mouth, state) := by
  exact A.runwayTrace.replay_grooved state hgrooved

/-- The first candy arm is grooved whenever the action tongue selects it. -/
theorem ManufacturedFlipReflector.firstArm_groove_of_selected
    (state : Tongues) (hselected : state A.actionSwitch = bval A.firstArm) :
    arrive state A.firstArm = (A.mouth, state) :=
  stem_branch_groove A.mouth_is_stem A.firstArm_branch A.firstArm_switch
    (by simpa only [A.firstArm_switch] using hselected)

/-- Candy traversal in its recorded direction, before the mouth switch is
pinned on the return arm. -/
theorem ManufacturedFlipReflector.candy_forward_trace
    (state : Tongues)
    (hselected : state A.actionSwitch = bval A.firstArm)
    (hgrooved : PassagesGrooved state A.candy) :
    PhysicalTrace w (A.mouth, state)
      ((A.mouth, A.firstArm) :: A.candy)
      (A.secondArm, state) := by
  apply physicalTrace_grooved_passages w state A.mouth A.firstArm A.secondArm A.candy
    A.candyTrace.linked ?_ A.candyTrace.last_link
  intro passage hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact A.firstArm_groove_of_selected state hselected
  · exact hgrooved passage hp

/-- Candy traversal in the opposite direction, with the reverse passage
list retained explicitly. -/
theorem ManufacturedFlipReflector.candy_reverse_trace
    (state : Tongues)
    (hselected : state A.actionSwitch = bval A.secondArm)
    (hgrooved : PassagesGrooved state A.candy) :
    PhysicalTrace w (A.mouth, state)
      ((A.mouth, A.secondArm) :: reversePassages A.candy)
      (A.firstArm, state) := by
  have hg := stem_branch_groove A.mouth_is_stem A.secondArm_branch A.secondArm_switch
    (by simpa only [A.secondArm_switch] using hselected)
  cases A.candyTrace with
  | cons _ hentry tail =>
      exact physicalTrace_contact_retraces_prefix tail hgrooved hentry (groove_forward hg)

theorem ManufacturedFlipReflector.reverse_support_simple :
    SwitchSimple
      (A.runway ++
        (A.mouth, A.secondArm) :: reversePassages A.candy) := by
  have hmap :
      (reversePassages A.candy).map passageSwitch =
        (A.candy.map passageSwitch).reverse := by
    have htrace := A.candyTrace
    cases htrace with
    | cons harrive hlink tail =>
        exact map_passageSwitch_reversePassages tail
  have hs := A.simple
  unfold SwitchSimple at hs ⊢
  simp only [List.map_append, List.map_cons] at hs ⊢
  rw [hmap]
  exact nodup_prefix_head_reverse_tail hs

/-- The lobe mouth is absent from both support paths; its flip is therefore
the unique possible support fault seen by another reflector. -/
theorem ManufacturedFlipReflector.support_foreign :
    ∀ path ∈ [A.runway, A.candy], ∀ passage ∈ path,
      passageSwitch passage ≠ A.actionSwitch := by
  have hs := A.simple
  intro path hp passage hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    grind [SwitchSimple, passageSwitch, ManufacturedFlipReflector.actionSwitch]

/-- Core capture, packaged on the retained manufactured-reflector data. -/
theorem ManufacturedFlipReflector.capture_from_mouth
    (state : Tongues)
    (hrunway : PassagesGrooved state A.runway)
    (hcandy : PassagesGrooved state A.candy) :
    stepN w (A.candy.length + 2 + A.runway.length)
      (A.mouth, flipAt state A.actionSwitch) = some (e, state) := by
  have hrunwayFlip := grooved_after_flip_other hrunway
    (A.support_foreign A.runway (by simp))
  have hcandyFlip := grooved_after_flip_other hcandy
    (A.support_foreign A.candy (by simp))
  have hwhole := (A.toSupported.run (flipAt state A.actionSwitch)
    (pathGrooves_pair.mpr ⟨hrunwayFlip, hcandyFlip⟩)).1
  change stepN w (2 * A.runway.length + A.candy.length + 2)
    (g, flipAt state A.actionSwitch) =
      some (e, flipAt (flipAt state A.actionSwitch) A.actionSwitch) at hwhole
  rw [flipAt_flipAt] at hwhole
  have hlen : 2 * A.runway.length + A.candy.length + 2 =
      A.runway.length + (A.candy.length + 2 + A.runway.length) := by omega
  rw [hlen, stepN_add, (A.runway_trace _ hrunwayFlip).sound] at hwhole
  exact hwhole

end

/-- Degenerate first-revisit reflector: a grooved arm is linked to itself.
The train traverses the arm out and back, then retraces the runway; its local
action is the identity. -/
structure ManufacturedStayReflector (w : Wiring) (g e : Nat) where
  base : Tongues
  mouthState : Tongues
  returnState : Tongues
  runway : List Passage
  mouth : Nat
  arm : Nat
  runwayTrace :
    PhysicalTrace w (g, base) runway (mouth, mouthState)
  coreTrace :
    PhysicalTrace w (mouth, mouthState) [(mouth, arm)]
      (arm, returnState)
  simple : SwitchSimple (runway ++ [(mouth, arm)])
  stemEndpoint :
    mouth = 3 * (mouth / 3) ∨ arm = 3 * (mouth / 3)
  selfLink : w.link arm = some arm
  entryEdge : w.link e = some g

def ManufacturedStayReflector.toSupported
    {w : Wiring} {g e : Nat}
    (A : ManufacturedStayReflector w g e) :
    SupportedReflector w g e where
  travel := 2 * A.runway.length + 2
  paths := [A.runway, [(A.mouth, A.arm)]]
  action := .stay
  run := by
    have href := A.runwayTrace.sandwich_reflector A.entryEdge
      (fun _ hmouth => self_edge_groove_isReflector w A.selfLink hmouth)
      (fun _ hg => hg)
    intro state hpaths
    have hp := pathGrooves_pair.mp hpaths
    obtain ⟨hr, hg, hs⟩ := href state ⟨hp.1, passagesGrooved_singleton.mp hp.2⟩
    exact ⟨hr, pathGrooves_pair.mpr ⟨hg, passagesGrooved_singleton.mpr hs⟩⟩


theorem ManufacturedStayReflector.runway_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedStayReflector w g e)
    (state : Tongues)
    (hgrooved : PassagesGrooved state A.runway) :
    PhysicalTrace w (g, state) A.runway (A.mouth, state) := by
  exact A.runwayTrace.replay_grooved state hgrooved

inductive ManufacturedReflector (w : Wiring) (g e : Nat) where
  | stay (A : ManufacturedStayReflector w g e)
  | flip (A : ManufacturedFlipReflector w g e)

/-- The switch-simple outward exploration that manufactured a reflector.
It includes the lobe mouth passage, unlike `SupportedReflector.paths`,
because that mouth is exactly the additional switch the construction may
change. -/
def ManufacturedReflector.exploration
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : List Passage :=
  match A with
  | .stay R => R.runway ++ [(R.mouth, R.arm)]
  | .flip R => R.runway ++ (R.mouth, R.firstArm) :: R.candy

def ManufacturedReflector.baseState
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : Tongues :=
  match A with
  | .stay R => R.base
  | .flip R => R.base

def ManufacturedReflector.preReturn
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : Nat × Tongues :=
  match A with
  | .stay R => (R.arm, R.returnState)
  | .flip R => (R.secondArm, R.returnState)

def ManufacturedReflector.activatedState
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : Tongues :=
  match A with
  | .stay R => R.returnState
  | .flip R => R.afterReturn

def ManufacturedReflector.runway
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : List Passage :=
  match A with
  | .stay R => R.runway
  | .flip R => R.runway

def ManufacturedReflector.mouthConfig
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : Nat × Tongues :=
  match A with
  | .stay R => (R.mouth, R.mouthState)
  | .flip R => (R.mouth, R.mouthState)

section
variable {w : Wiring} {g e : Nat}
  (A : ManufacturedReflector w g e)
include w g e A

theorem ManufacturedReflector.runway_trace :
    PhysicalTrace w (g, A.baseState) A.runway A.mouthConfig := by
  cases A with
  | stay R => exact R.runwayTrace
  | flip R => exact R.runwayTrace

theorem ManufacturedReflector.exploration_trace :
    PhysicalTrace w (g, A.baseState) A.exploration A.preReturn := by
  cases A with
  | stay R => exact R.runwayTrace.append R.coreTrace
  | flip R => exact R.runwayTrace.append R.candyTrace

/-- The local return passage of either manufactured-reflector constructor
contacts the retained runway at its mouth and produces the advertised
activated state. -/
theorem ManufacturedReflector.return_arrive_mouth :
    arrive A.preReturn.2 A.preReturn.1 =
      (A.mouthConfig.1, A.activatedState) := by
  cases A with
  | flip R =>
      exact R.crossed
  | stay R =>
      obtain ⟨after, hhead⟩ := R.coreTrace.head_arrive.2
      have hsound := R.coreTrace.sound
      have hafter : after = R.returnState := by
        simp [stepN, step, hhead, R.selfLink] at hsound
        exact hsound
      have hback := arrive_back R.mouthState R.mouth
      rw [hhead, hafter] at hback
      exact hback

theorem ManufacturedReflector.exploration_simple :
    SwitchSimple A.exploration := by
  cases A with
  | stay R => exact R.simple
  | flip R => exact R.simple

end

def ManufacturedReflector.toSupported
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : SupportedReflector w g e :=
  match A with
  | .stay R => R.toSupported
  | .flip R => R.toSupported

theorem ManufacturedReflector.runway_mem_support
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    A.runway ∈ A.toSupported.paths := by
  cases A <;> simp [ManufacturedReflector.runway,
    ManufacturedReflector.toSupported,
    ManufacturedStayReflector.toSupported,
    ManufacturedFlipReflector.toSupported]

/-- The actual switch-simple outward route selected by `state`.  A flip
reflector may traverse its candy in either orientation; normalizing that
choice here lets every later contact be classified relative to the route the
train really takes. -/
def ManufacturedReflector.orientedRoute
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues) :
    List Passage :=
  match A with
  | .stay R => R.runway ++ [(R.mouth, R.arm)]
  | .flip R =>
      if state R.actionSwitch = bval R.firstArm then
        R.runway ++ (R.mouth, R.firstArm) :: R.candy
      else
        R.runway ++
          (R.mouth, R.secondArm) :: reversePassages R.candy

def ManufacturedReflector.orientedFinish
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues) : Nat :=
  match A with
  | .stay R => R.arm
  | .flip R =>
      if state R.actionSwitch = bval R.firstArm then
        R.secondArm
      else
        R.firstArm

/-- The selected far candy arm is the opposite branch, so its trailing
arrival applies the reflector action. This local fact also supplies the
head of the full return trace. -/
theorem ManufacturedFlipReflector.oriented_finish_arrive
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues) :
    arrive state
      ((ManufacturedReflector.flip R).orientedFinish state) =
        (R.mouth, flipAt state R.actionSwitch) := by
  have hm := R.mouth_is_stem
  have hf := R.firstArm_switch
  have hs := R.secondArm_switch
  have hopp := branch_values_opposite R.firstArm_branch R.secondArm_branch
    (hf.trans hs.symm) R.arms_ne
  have hstem₁ : 3 * (R.firstArm / 3) = R.mouth := by
    unfold ManufacturedFlipReflector.actionSwitch at hf; omega
  have hstem₂ : 3 * (R.secondArm / 3) = R.mouth := by
    unfold ManufacturedFlipReflector.actionSwitch at hs; omega
  by_cases hselected : state R.actionSwitch = bval R.firstArm
  · have hpin := pin_eq_flipAt (u := state) hs (by grind)
    simp [ManufacturedReflector.orientedFinish, hselected, arrive, R.secondArm_branch,
      hstem₂, hpin]
  · have hpin := pin_eq_flipAt (u := state) hf (by grind)
    simp [ManufacturedReflector.orientedFinish, hselected, arrive, R.firstArm_branch,
      hstem₁, hpin]

/-- The state before the final return is the action-applied activated state. -/
theorem ManufacturedReflector.preReturn_eq_action_activated
    {w : Wiring} {g e : Nat} (B : ManufacturedReflector w g e) :
    B.preReturn.2 = B.toSupported.action.apply B.activatedState := by
  cases B with
  | stay R => rfl
  | flip R =>
      change R.returnState = flipAt R.afterReturn R.actionSwitch
      have hs : SwitchSimple ((R.mouth, R.firstArm) :: R.candy) := by
        have := R.simple
        grind [SwitchSimple]
      have hfirst := R.candyTrace.grooved_of_switchSimple hs
        (R.mouth, R.firstArm) List.mem_cons_self
      have hselected : R.returnState R.actionSwitch = bval R.firstArm := by
        have hbit := congrArg (fun r => r.2 R.actionSwitch) hfirst
        simpa [arrive, R.firstArm_branch, pin, R.firstArm_switch] using hbit.symm
      have hafter := R.oriented_finish_arrive R.returnState
      simp only [ManufacturedReflector.orientedFinish, hselected, if_pos] at hafter
      have hcross := (Prod.mk.inj (R.crossed.symm.trans hafter)).2
      rw [hcross, flipAt_flipAt]

theorem ManufacturedReflector.orientedRoute_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state) :
    PhysicalTrace w (g, state) (A.orientedRoute state)
      (A.orientedFinish state, state) := by
  cases A with
  | stay R =>
      have hp := pathGrooves_pair.mp hpaths
      exact (R.runway_trace state hp.1).append (R.coreTrace.replay_grooved state hp.2)
  | flip R =>
      change PathGrooves [R.runway, R.candy] state at hpaths
      have hp := pathGrooves_pair.mp hpaths
      have hrun := R.runway_trace state hp.1
      by_cases hselected :
          state R.actionSwitch = bval R.firstArm
      · have hcandy := R.candy_forward_trace state hselected hp.2
        simpa [ManufacturedReflector.orientedRoute,
          ManufacturedReflector.orientedFinish, hselected] using
          hrun.append hcandy
      · have hsecond :
            state R.actionSwitch = bval R.secondArm := by
          rcases R.selected_arm state with hfirst | hsecond
          · exact absurd hfirst hselected
          · exact hsecond
        have hcandy := R.candy_reverse_trace state hsecond hp.2
        simpa [ManufacturedReflector.orientedRoute,
          ManufacturedReflector.orientedFinish, hselected] using
          hrun.append hcandy

theorem ManufacturedReflector.orientedRoute_simple
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues) :
    SwitchSimple (A.orientedRoute state) := by
  cases A with
  | stay R =>
      simpa [ManufacturedReflector.orientedRoute] using R.simple
  | flip R =>
      by_cases hselected :
          state R.actionSwitch = bval R.firstArm
      · simpa [ManufacturedReflector.orientedRoute, hselected] using
          R.simple
      · simpa [ManufacturedReflector.orientedRoute, hselected] using
          R.reverse_support_simple

/-- Every reusable support passage occurs on the selected outward route,
possibly in the opposite orientation when the candy is traversed backwards.
-/
theorem ManufacturedReflector.support_passage_on_orientedRoute
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues)
    {path : List Passage} (hpath : path ∈ A.toSupported.paths)
    {old : Passage} (hold : old ∈ path) :
    ∃ oriented ∈ A.orientedRoute state,
      oriented = old ∨ oriented = (old.2, old.1) := by
  cases A with
  | stay R =>
      change path ∈ [R.runway, [(R.mouth, R.arm)]] at hpath
      refine ⟨old, ?_, Or.inl rfl⟩
      change old ∈ R.runway ++ [(R.mouth, R.arm)]
      grind
  | flip R =>
      change path ∈ [R.runway, R.candy] at hpath
      by_cases hselected : state R.actionSwitch = bval R.firstArm
      · refine ⟨old, ?_, Or.inl rfl⟩
        simp only [ManufacturedReflector.orientedRoute, hselected, if_pos]
        grind
      · by_cases hr : old ∈ R.runway
        · exact ⟨old, by simp [ManufacturedReflector.orientedRoute, hselected, hr], Or.inl rfl⟩
        · have hc : old ∈ R.candy := by grind
          exact ⟨(old.2, old.1), by
            simp [ManufacturedReflector.orientedRoute, hselected, reversePassage_mem hc], Or.inr rfl⟩

/-- Orientation-normalized contact dichotomy.  At the instant a fresh
passage changes an old support switch, compare it with the passage on the
outward route the old reflector would actually take in that state.  The
fresh exit points either back into the already traversed prefix or forward
along the selected route. -/
theorem ManufacturedReflector.changed_contact_on_orientedRoute
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state next : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state)
    {path : List Passage} (hpath : path ∈ A.toSupported.paths)
    {old : Passage} (hold : old ∈ path)
    {p x : Nat}
    (hswitch : passageSwitch old = p / 3)
    (hfresh : arrive state p = (x, next)) :
    ∃ oriented ∈ A.orientedRoute state,
      arrive state oriented.2 = (oriented.1, state) ∧
      passageSwitch oriented = p / 3 ∧
      (x = oriented.1 ∨ x = oriented.2) := by
  obtain ⟨oriented, horiented, horient⟩ :=
    A.support_passage_on_orientedRoute state hpath hold
  have holdGroove := hpaths path hpath old hold
  have horientedGroove :
      arrive state oriented.2 = (oriented.1, state) := by
    rcases horient with hsame | hreverse
    · simpa [hsame] using holdGroove
    · simpa [hreverse] using groove_forward holdGroove
  have hOldSwitch : old.2 / 3 = passageSwitch old := by
    have hs := arrive_exit_switch state old.2
    rw [holdGroove] at hs
    exact hs.symm
  have horientedSwitch : passageSwitch oriented = p / 3 := by
    rcases horient with hsame | hreverse
    · simpa [hsame] using hswitch
    · simp only [hreverse, passageSwitch]
      rw [hOldSwitch]
      exact hswitch
  change oriented.1 / 3 = p / 3 at horientedSwitch
  exact ⟨oriented, horiented, horientedGroove, horientedSwitch,
    by grind [groove_forward, same_switch_passages_share_port]⟩

theorem pathGrooves_after_arrive_without_support_change
    {u v : Tongues} {p x : Nat} {paths : List (List Passage)}
    (harrive : arrive u p = (x, v))
    (hgrooves : PathGrooves paths u)
    (hquiet : ∀ path ∈ paths, ∀ old ∈ path,
      passageSwitch old = p / 3 → v (p / 3) = u (p / 3)) :
    PathGrooves paths v := by
  intro path hp old hold
  have hgroove := hgrooves path hp old hold
  have hexit : old.2 / 3 = passageSwitch old := by
    have hs := arrive_exit_switch u old.2
    rw [hgroove] at hs
    exact hs.symm
  apply groove_transfer hgroove
  by_cases hsame : passageSwitch old = p / 3
  · rw [hexit, hsame]
    exact hquiet path hp old hold hsame
  · apply arrive_preserves_other harrive
    rw [hexit]
    exact hsame
theorem same_groove_same_tongue
    {u v : Tongues} {old : Passage}
    (hu : arrive u old.2 = (old.1, u))
    (hv : arrive v old.2 = (old.1, v)) :
    u (passageSwitch old) = v (passageSwitch old) := by
  exact grooved_states_agree_on_passage (groove_forward hu) (groove_forward hv)

theorem PhysicalTrace.first_changed_support_passage
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage} {paths : List (List Passage)}
    (htrace : PhysicalTrace w start passages finish)
    (hbase : PathGrooves paths start.2)
    (hbroken : ¬ PathGrooves paths finish.2) :
    ∃ approach p x suffix u v path old,
      passages = approach ++ (p, x) :: suffix ∧
      PhysicalTrace w start approach (p, u) ∧
      PathGrooves paths u ∧
      arrive u p = (x, v) ∧
      path ∈ paths ∧ old ∈ path ∧
      passageSwitch old = p / 3 ∧
      v (p / 3) ≠ u (p / 3) := by
  induction htrace with
  | nil => exact (hbroken hbase).elim
  | @cons p x q u v rest finish harrive hlink tail ih =>
      by_cases hhead : ∃ path ∈ paths, ∃ old ∈ path,
          passageSwitch old = p / 3 ∧ v (p / 3) ≠ u (p / 3)
      · obtain ⟨path, hp, old, ho, hs, hc⟩ := hhead
        exact ⟨[], p, x, rest, u, v, path, old, rfl, PhysicalTrace.nil _,
          hbase, harrive, hp, ho, hs, hc⟩
      · have hnext := pathGrooves_after_arrive_without_support_change
          harrive hbase (by grind)
        obtain ⟨before, p', x', after, u', v', path, old, hs, ht, hg, ha, hp, ho, hj, hc⟩ :=
          ih hnext hbroken
        exact ⟨(p, x) :: before, p', x', after, u', v', path, old, by simp [hs],
          PhysicalTrace.cons harrive hlink ht, hg, ha, hp, ho, hj, hc⟩


theorem ManufacturedReflector.entryEdge
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    w.link e = some g := by
  cases A with
  | stay R => exact R.entryEdge
  | flip R => exact R.entryEdge



theorem contact_of_not_avoids_flip
    {paths : List (List Passage)} {k : Nat}
    (hnot : ¬ (LocalAction.flip k).Avoids paths) :
    ∃ path ∈ paths, ∃ passage ∈ path,
      passageSwitch passage = k := by
  simpa [LocalAction.Avoids] using hnot

theorem ManufacturedReflector.travel_pos
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    0 < A.toSupported.travel := by
  cases A with
  | stay R =>
      change 0 < 2 * R.runway.length + 2
      omega
  | flip R =>
      change 0 < 2 * R.runway.length + R.candy.length + 2
      omega

end GeneralN
