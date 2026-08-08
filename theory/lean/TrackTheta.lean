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
  unfold pin flipAt
  by_cases hjp : j = p / 3
  · subst j
    simp [hpk]
  · by_cases hjk : j = k
    · subst j
      simp [Ne.symm hpk]
    · simp [hjp, hjk]

/-- Flipping an unvisited switch commutes with one local lazy-point
traversal. -/
theorem arrive_flip_other {u v : Tongues} {p x k : Nat}
    (harrive : arrive u p = (x, v))
    (hpk : p / 3 ≠ k) :
    arrive (flipAt u k) p = (x, flipAt v k) := by
  unfold arrive at harrive ⊢
  by_cases hp : p % 3 = 0
  · rw [if_pos hp] at harrive ⊢
    injection harrive with hx hv
    subst x
    subst v
    simp [flipAt, hpk]
  · rw [if_neg hp] at harrive ⊢
    injection harrive with hx hv
    subst x
    rw [pin_flip_other hpk, hv]

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

/-- The trace-valued form of `run_grooved_passages`: following a linked
grooved path creates the advertised physical trace and changes no tongue. -/
theorem physicalTrace_grooved_passages
    (w : Wiring) (u : Tongues) (p x q : Nat)
    (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hfinal : w.link (lastPassageExit x rest) = some q) :
    PhysicalTrace w (p, u) ((p, x) :: rest) (q, u) := by
  induction rest generalizing p x with
  | nil =>
      have hforward := groove_forward
        (hgrooved (p, x) List.mem_cons_self)
      exact PhysicalTrace.cons hforward hfinal (PhysicalTrace.nil _)
  | cons passage rest ih =>
      rcases passage with ⟨r, y⟩
      have hxy : w.link x = some r := hlinked.1
      have htailLinked : LinkedPassages w ((r, y) :: rest) := hlinked.2
      have htailGrooved : PassagesGrooved u ((r, y) :: rest) := by
        intro passage hp
        exact hgrooved passage (List.mem_cons_of_mem _ hp)
      have htailFinal : w.link (lastPassageExit y rest) = some q := by
        simpa [lastPassageExit] using hfinal
      have htail := ih r y htailLinked htailGrooved htailFinal
      have hforward := groove_forward
        (hgrooved (p, x) List.mem_cons_self)
      exact PhysicalTrace.cons hforward hxy htail

/-- Passage list for traversing a stored path in the opposite direction. -/
def reversePassages : List Passage → List Passage
  | [] => []
  | passage :: rest =>
      reversePassages rest ++ [(passage.2, passage.1)]

theorem reversePassages_length (passages : List Passage) :
    (reversePassages passages).length = passages.length := by
  induction passages with
  | nil => rfl
  | cons passage rest ih =>
      simp [reversePassages, ih]

theorem reversePassages_append (left right : List Passage) :
    reversePassages (left ++ right) =
      reversePassages right ++ reversePassages left := by
  induction left with
  | nil => simp [reversePassages]
  | cons passage left ih =>
      simp [reversePassages, ih, List.append_assoc]

private theorem mem_reverse_nat {x : Nat} {xs : List Nat} :
    x ∈ xs.reverse ↔ x ∈ xs := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      simp [ih, or_comm]

private theorem nodup_reverse_nat {xs : List Nat}
    (hnd : xs.Nodup) : xs.reverse.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.reverse_cons]
      apply List.nodup_append.mpr
      refine ⟨ih hnd.2, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro hax
      apply hnd.1
      rw [← hax]
      exact mem_reverse_nat.mp ha

private theorem nodup_prefix_head_reverse_tail
    {pre tail : List Nat} {head : Nat}
    (hnd : (pre ++ head :: tail).Nodup) :
    (pre ++ head :: tail.reverse).Nodup := by
  have hparts := List.nodup_append.mp hnd
  have hheadTail := hparts.2.1
  rw [List.nodup_cons] at hheadTail
  apply List.nodup_append.mpr
  refine ⟨hparts.1, ?_, ?_⟩
  · rw [List.nodup_cons]
    constructor
    · intro hmem
      apply hheadTail.1
      exact mem_reverse_nat.mp hmem
    · exact nodup_reverse_nat hheadTail.2
  · intro a ha b hb
    rcases List.mem_cons.mp hb with hbh | hbt
    · subst b
      exact hparts.2.2 a ha head List.mem_cons_self
    · exact hparts.2.2 a ha b
        (List.mem_cons_of_mem _ (mem_reverse_nat.mp hbt))

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
  induction htrace with
  | nil => rfl
  | @cons p x q u v passages finish harrive hlink tail ih =>
      have hs := arrive_exit_switch u p
      rw [harrive] at hs
      simp [reversePassages, List.map_append, ih,
        passageSwitch, hs]

/-- Trace-valued arbitrary-path retrace.  This strengthens the existing
`retrace_linked_passages` endpoint theorem by retaining the reversed passage
list, which lets the theta proof locate its first mouth contact. -/
theorem physicalTrace_retrace_linked_passages
    (w : Wiring) (u : Tongues) (p x ell : Nat)
    (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hentry : w.link ell = some p) :
    PhysicalTrace w (lastPassageExit x rest, u)
      (reversePassages ((p, x) :: rest)) (ell, u) := by
  induction rest generalizing p x ell with
  | nil =>
      have hback : w.link p = some ell := w.symm _ _ hentry
      have hgroove := hgrooved (p, x) List.mem_cons_self
      exact PhysicalTrace.cons hgroove hback (PhysicalTrace.nil _)
  | cons passage rest ih =>
      rcases passage with ⟨q, y⟩
      have hxy : w.link x = some q := hlinked.1
      have htailLinked : LinkedPassages w ((q, y) :: rest) := hlinked.2
      have htailGrooved : PassagesGrooved u ((q, y) :: rest) := by
        intro passage hp
        exact hgrooved passage (List.mem_cons_of_mem _ hp)
      have htail := ih q y x htailLinked htailGrooved hxy
      have hback : w.link p = some ell := w.symm _ _ hentry
      have hheadGroove := hgrooved (p, x) List.mem_cons_self
      have hhead : PhysicalTrace w (x, u) [(x, p)] (ell, u) :=
        PhysicalTrace.cons hheadGroove hback (PhysicalTrace.nil _)
      exact htail.append hhead

theorem linked_prefix_of_append {w : Wiring}
    {left right : List Passage}
    (hlinked : LinkedPassages w (left ++ right)) :
    LinkedPassages w left := by
  induction left with
  | nil => trivial
  | cons a tail ih =>
      cases tail with
      | nil => trivial
      | cons b rest =>
          change w.link a.2 = some b.1 ∧
            LinkedPassages w (b :: rest) at ⊢
          change w.link a.2 = some b.1 ∧
            LinkedPassages w ((b :: rest) ++ right) at hlinked
          exact ⟨hlinked.1, ih hlinked.2⟩

theorem linked_boundary_of_append {w : Wiring}
    {g a p x : Nat} {before after : List Passage}
    (hlinked : LinkedPassages w
      (((g, a) :: before) ++ (p, x) :: after)) :
    w.link (lastPassageExit a before) = some p := by
  induction before generalizing g a with
  | nil =>
      exact hlinked.1
  | cons passage before ih =>
      rcases passage with ⟨r, y⟩
      have htail : LinkedPassages w
          (((r, y) :: before) ++ (p, x) :: after) := hlinked.2
      simpa [lastPassageExit] using ih htail

theorem linked_after_occurrence {w : Wiring}
    {p x q y : Nat} {before after : List Passage}
    (hlinked : LinkedPassages w
      (before ++ (p, x) :: (q, y) :: after)) :
    w.link x = some q := by
  induction before with
  | nil => exact hlinked.1
  | cons passage before ih =>
      rcases passage with ⟨r, s⟩
      cases before with
      | nil => exact hlinked.2.1
      | cons passage before => exact ih hlinked.2

theorem lastPassageExit_append_cons
    (z p x : Nat) (before after : List Passage) :
    lastPassageExit z (before ++ (p, x) :: after) =
      lastPassageExit x after := by
  induction before generalizing z with
  | nil => rfl
  | cons passage before ih =>
      simpa [lastPassageExit] using ih passage.2

/-- A nonempty prefix before an occurrence in a simple grooved path reaches
that occurrence without changing tongues, and does not visit its switch. -/
theorem simple_grooved_prefix_to_occurrence
    {w : Wiring} {u : Tongues}
    {g a p x : Nat} {before after : List Passage}
    (hlinked : LinkedPassages w
      (((g, a) :: before) ++ (p, x) :: after))
    (hgrooved : PassagesGrooved u
      (((g, a) :: before) ++ (p, x) :: after))
    (hsimple : SwitchSimple
      (((g, a) :: before) ++ (p, x) :: after)) :
    PhysicalTrace w (g, u) ((g, a) :: before) (p, u) ∧
      (∀ passage ∈ (g, a) :: before,
        passageSwitch passage ≠ passageSwitch (p, x)) := by
  have hprefixLinked : LinkedPassages w ((g, a) :: before) :=
    linked_prefix_of_append hlinked
  have hprefixGrooved : PassagesGrooved u ((g, a) :: before) := by
    intro passage hp
    exact hgrooved passage (List.mem_append_left _ hp)
  have hboundary : w.link (lastPassageExit a before) = some p :=
    linked_boundary_of_append hlinked
  have htrace := physicalTrace_grooved_passages w u g a p before
    hprefixLinked hprefixGrooved hboundary
  have hforeign : ∀ passage ∈ (g, a) :: before,
      passageSwitch passage ≠ passageSwitch (p, x) := by
    unfold SwitchSimple at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    have hparts := List.nodup_append.mp hsimple
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (p, x)) (by simp)
    exact hne hEq
  exact ⟨htrace, hforeign⟩

/-- Empty-prefix wrapper around `simple_grooved_prefix_to_occurrence`.  A
static trace supplies the path's starting port; the returned trace is rebased
to any tongue vector under which the path is grooved. -/
theorem simple_grooved_trace_prefix_to_occurrence
    {w : Wiring} {e : Nat} {base u : Tongues}
    {path before after : List Passage} {p x : Nat}
    {finish : Nat × Tongues}
    (hstatic : PhysicalTrace w (e, base) path finish)
    (hoccurs : path = before ++ (p, x) :: after)
    (hgrooved : PassagesGrooved u path)
    (hsimple : SwitchSimple path) :
    PhysicalTrace w (e, u) before (p, u) ∧
      (∀ passage ∈ before,
        passageSwitch passage ≠ passageSwitch (p, x)) := by
  have hlinked : LinkedPassages w
      (before ++ (p, x) :: after) := by
    rw [← hoccurs]
    exact hstatic.linked
  have hgrooved' : PassagesGrooved u
      (before ++ (p, x) :: after) := by
    rwa [← hoccurs]
  have hsimple' : SwitchSimple
      (before ++ (p, x) :: after) := by
    rwa [← hoccurs]
  cases before with
  | nil =>
      have htrace := hstatic
      rw [hoccurs] at htrace
      have hstart : e = p := htrace.head_arrive.1
      constructor
      · simpa [hstart] using (PhysicalTrace.nil (e, u))
      · intro passage hp
        cases hp
  | cons passage before =>
      rcases passage with ⟨g, a⟩
      have hdata := simple_grooved_prefix_to_occurrence
        hlinked hgrooved' hsimple'
      have htrace := hstatic
      rw [hoccurs] at htrace
      have hstart : e = g := htrace.head_arrive.1
      constructor
      · simpa [hstart] using hdata.1
      · exact hdata.2

/-! ## One deliberately broken groove -/

/-- If a grooved passage is entered trailing-first after its switch has been
flipped, the trailing move repairs the tongue and follows the old passage.
This is the self-healing half of the theta case. -/
theorem flipped_passage_forward_trailing
    {u : Tongues} {p x : Nat}
    (hforward : arrive u p = (x, u))
    (hpbranch : p % 3 ≠ 0) :
    arrive (flipAt u (p / 3)) p = (x, u) := by
  unfold arrive at hforward
  rw [if_neg hpbranch] at hforward
  injection hforward with hx hpin
  have hu : u (p / 3) = bval p := by
    simpa [pin] using (congrFun hpin (p / 3)).symm
  have hrestore : pin (flipAt u (p / 3)) p = u := by
    funext j
    unfold pin flipAt
    by_cases hj : j = p / 3
    · subst j
      simp [hu]
    · simp [hj]
  simp [arrive, hpbranch, hrestore, hx]

/-- If the same flipped groove is entered facing-first, the train cannot
follow the old passage: it leaves through the switch's other branch.  This
is the diversion half of the theta case. -/
theorem flipped_passage_forward_facing
    {u : Tongues} {p x : Nat}
    (hforward : arrive u p = (x, u))
    (hpstem : p % 3 = 0) :
    let other := branchPort (p / 3) (!(u (p / 3)))
    arrive (flipAt u (p / 3)) p =
        (other, flipAt u (p / 3)) ∧
      other ≠ x := by
  have hforward' := hforward
  unfold arrive at hforward'
  rw [if_pos hpstem] at hforward'
  injection hforward' with hx _
  have harrive :
      arrive (flipAt u (p / 3)) p =
        (branchPort (p / 3) (!(u (p / 3))),
          flipAt u (p / 3)) := by
    simp [arrive, hpstem, flipAt]
  dsimp only
  refine ⟨harrive, ?_⟩
  rw [← hx]
  cases u (p / 3) <;> simp [branchPort]

/-! ## Capture by the older lobe -/

/-- Entering the mouth of a manufactured nondegenerate lobe in the state
obtained by flipping that mouth switch traverses the candy, cancels the flip,
retraces the old runway, and emerges at the runway's far edge.  This is the
dynamic heart of the theta case; unlike `SupportedReflector.run`, it starts
at the *core mouth* rather than at the front of the sandwich. -/
theorem crossed_revisit_capture_from_mouth
    (w : Wiring) {g e p x q : Nat}
    {base u₀ u v : Tongues} {runway path : List Passage}
    (hrunway : PhysicalTrace w (g, base) runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hrepeat : arrive u q = (p, v))
    (hxq : x ≠ q)
    (hentry : w.link e = some g)
    (state : Tongues)
    (hrunwayGrooved : PassagesGrooved state runway)
    (hpathGrooved : PassagesGrooved state path) :
    stepN w (path.length + 2 + runway.length)
      (p, flipAt state (p / 3)) = some (e, state) := by
  have hsimpleExcursion : SwitchSimple ((p, x) :: path) := by
    unfold SwitchSimple at hsimple ⊢
    simp only [List.map_append] at hsimple
    exact (List.nodup_append.mp hsimple).2.1
  have hsimpleExcursion' := hsimpleExcursion
  unfold SwitchSimple at hsimpleExcursion'
  simp only [List.map_cons, List.nodup_cons] at hsimpleExcursion'
  have hpathForeign : ∀ passage ∈ path,
      passageSwitch passage ≠ p / 3 := by
    intro passage hp hEq
    apply hsimpleExcursion'.1
    apply List.mem_map.mpr
    exact ⟨passage, hp, hEq⟩
  have hpathFlipped :
      PassagesGrooved (flipAt state (p / 3)) path :=
    grooved_after_flip_other hpathGrooved hpathForeign
  cases runway with
  | nil =>
      cases hrunway
      have hmouth : w.link g = some e := w.symm _ _ hentry
      have hcore := crossed_excursion_core_reflector w hexcursion
        hsimpleExcursion hrepeat hxq hmouth
      obtain ⟨hstep, _⟩ := hcore (flipAt state (g / 3)) hpathFlipped
      simpa [flipAt_flipAt] using hstep
  | cons passage rest =>
      rcases passage with ⟨a, b⟩
      have hg : g = a := hrunway.head_arrive.1
      have hlast : w.link (lastPassageExit b rest) = some p :=
        hrunway.last_link
      have hmouth : w.link p = some (lastPassageExit b rest) :=
        w.symm _ _ hlast
      have hcore := crossed_excursion_core_reflector w hexcursion
        hsimpleExcursion hrepeat hxq hmouth
      obtain ⟨hstep, _⟩ := hcore (flipAt state (p / 3)) hpathFlipped
      have hback := retrace_linked_passages w state a b e rest
        hrunway.linked hrunwayGrooved (by simpa [hg] using hentry)
      rw [stepN_add, hstep]
      simpa [flipAt_flipAt] using hback

/-! ## Splicing a first contact into the capture -/

/-- A trace prefix which does not visit `k` is unchanged by flipping `k`;
if its endpoint is the old lobe's mouth, append the mouth-capture and obtain
an exact return to the prefix's starting port. -/
theorem theta_capture_after_unvisited_prefix
    {w : Wiring} {e p k cap : Nat} {u : Tongues}
    {before : List Passage}
    (hprefix : PhysicalTrace w (e, u) before (p, u))
    (hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ k)
    (hcapture : stepN w cap (p, flipAt u k) = some (e, u)) :
    stepN w (before.length + cap) (e, flipAt u k) =
      some (e, u) := by
  have hprefixFlip := hprefix.flip_unvisited hforeign
  rw [stepN_add, hprefixFlip.sound]
  exact hcapture

/-- The other branch of the first-contact dichotomy.  If the broken passage
is met trailing-first, it repairs the foreign flip and the exact old suffix
replays. -/
theorem flipped_trace_trailing_repairs
    {w : Wiring} {e p x q k : Nat}
    {u : Tongues} {before after : List Passage}
    {finish : Nat × Tongues}
    (hprefix : PhysicalTrace w (e, u) before (p, u))
    (hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ k)
    (hk : p / 3 = k)
    (hpbranch : p % 3 ≠ 0)
    (hgroove : arrive u p = (x, u))
    (hlink : w.link x = some q)
    (htail : PhysicalTrace w (q, u) after finish) :
    stepN w (before ++ (p, x) :: after).length
      (e, flipAt u k) = some finish := by
  have hprefixFlip := hprefix.flip_unvisited hforeign
  have hrepair : arrive (flipAt u k) p = (x, u) := by
    rw [← hk]
    exact flipped_passage_forward_trailing hgroove hpbranch
  have hfull := hprefixFlip.append
    (PhysicalTrace.cons hrepair hlink htail)
  exact hfull.sound

/-- Step-count version of `flipped_trace_trailing_repairs`, convenient when
the deterministic suffix is known by decomposing a reflector run rather than
by retaining its passage list. -/
theorem flipped_prefix_trailing_then
    {w : Wiring} {e p x q k tailSteps : Nat}
    {u : Tongues} {before : List Passage}
    {finish : Nat × Tongues}
    (hprefix : PhysicalTrace w (e, u) before (p, u))
    (hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ k)
    (hk : p / 3 = k)
    (hpbranch : p % 3 ≠ 0)
    (hgroove : arrive u p = (x, u))
    (hlink : w.link x = some q)
    (hsuffix : stepN w tailSteps (q, u) = some finish) :
    stepN w (before.length + 1 + tailSteps)
      (e, flipAt u k) = some finish := by
  have hprefixFlip := hprefix.flip_unvisited hforeign
  have hrepair : arrive (flipAt u k) p = (x, u) := by
    rw [← hk]
    exact flipped_passage_forward_trailing hgroove hpbranch
  have hone : stepN w 1 (p, flipAt u k) = some (q, u) := by
    simp [stepN, step, hrepair, hlink]
  have hlen : before.length + 1 + tailSteps =
      before.length + (1 + tailSteps) := by omega
  rw [hlen]
  rw [stepN_add, hprefixFlip.sound]
  simp only [Option.bind_some]
  rw [stepN_add, hone]
  exact hsuffix

theorem suffix_after_physical_prefix
    {w : Wiring} {start middle finish : Nat × Tongues}
    {passages : List Passage} {total tail : Nat}
    (hprefix : PhysicalTrace w start passages middle)
    (hlen : total = passages.length + tail)
    (hfull : stepN w total start = some finish) :
    stepN w tail middle = some finish := by
  rw [hlen, stepN_add, hprefix.sound] at hfull
  exact hfull

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

/-- The mouth of every nondegenerate manufactured reflector is the stem of
its switch. -/
theorem ManufacturedFlipReflector.mouth_is_stem
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    A.mouth % 3 = 0 := by
  obtain ⟨oldAfter, hold⟩ := A.candyTrace.head_arrive.2
  have holdStem := arrive_stem_endpoint A.mouthState A.mouth
  rw [hold] at holdStem
  have hnewStem := arrive_stem_endpoint A.returnState A.secondArm
  rw [A.crossed] at hnewStem
  have hfirstSwitch := arrive_exit_switch A.mouthState A.mouth
  rw [hold] at hfirstSwitch
  have hsecondSwitch :=
    arrive_exit_switch A.returnState A.secondArm
  rw [A.crossed] at hsecondSwitch
  by_cases hp : A.mouth % 3 = 0
  · exact hp
  · exfalso
    have hpne : A.mouth ≠ 3 * (A.mouth / 3) := by omega
    rcases holdStem with hpOld | hxStem
    · exact hpne hpOld
    · rcases hnewStem with hqStem | hpNew
      · apply A.arms_ne
        omega
      · apply hpne
        omega

theorem ManufacturedFlipReflector.firstArm_switch
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    A.firstArm / 3 = A.actionSwitch := by
  obtain ⟨after, hhead⟩ := A.candyTrace.head_arrive.2
  have hs := arrive_exit_switch A.mouthState A.mouth
  rw [hhead] at hs
  simpa [ManufacturedFlipReflector.actionSwitch] using hs

theorem ManufacturedFlipReflector.secondArm_switch
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    A.secondArm / 3 = A.actionSwitch := by
  have hs := arrive_exit_switch A.returnState A.secondArm
  rw [A.crossed] at hs
  simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm

theorem ManufacturedFlipReflector.firstArm_branch
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    A.firstArm % 3 ≠ 0 := by
  intro hstem
  have hne := arrive_exit_ne A.mouthState A.mouth
  obtain ⟨after, hhead⟩ := A.candyTrace.head_arrive.2
  rw [hhead] at hne
  have hm := A.mouth_is_stem
  have hs := A.firstArm_switch
  unfold ManufacturedFlipReflector.actionSwitch at hs
  apply hne
  omega

theorem ManufacturedFlipReflector.secondArm_branch
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    A.secondArm % 3 ≠ 0 := by
  intro hstem
  have hne := arrive_exit_ne A.returnState A.secondArm
  rw [A.crossed] at hne
  have hm := A.mouth_is_stem
  have hs := A.secondArm_switch
  unfold ManufacturedFlipReflector.actionSwitch at hs
  apply hne
  omega

theorem ManufacturedFlipReflector.selected_arm
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
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
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hgrooved : PassagesGrooved state A.runway) :
    PhysicalTrace w (g, state) A.runway (A.mouth, state) := by
  cases hrunway : A.runway with
  | nil =>
      have htrace := A.runwayTrace
      rw [hrunway] at htrace
      have hs : (g, A.base) = (A.mouth, A.mouthState) := by
        simpa [stepN] using htrace.sound
      have hgm : g = A.mouth := congrArg Prod.fst hs
      simpa [hrunway, hgm] using (PhysicalTrace.nil (g, state))
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have htrace := A.runwayTrace
      rw [hrunway] at htrace
      have hgrooved' :
          PassagesGrooved state ((p, x) :: rest) := by
        simpa [hrunway] using hgrooved
      have hstart : g = p := htrace.head_arrive.1
      have htrace := physicalTrace_grooved_passages w state p x
        A.mouth rest htrace.linked hgrooved' htrace.last_link
      simpa [hrunway, hstart] using htrace

/-- Candy traversal in its recorded direction, before the mouth switch is
pinned on the return arm. -/
theorem ManufacturedFlipReflector.candy_forward_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hselected : state A.actionSwitch = bval A.firstArm)
    (hgrooved : PassagesGrooved state A.candy) :
    PhysicalTrace w (A.mouth, state)
      ((A.mouth, A.firstArm) :: A.candy)
      (A.secondArm, state) := by
  have hfirstSwitch := A.firstArm_switch
  have hfirstBranch := A.firstArm_branch
  have hstem : 3 * (A.firstArm / 3) = A.mouth := by
    have hm := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch at hfirstSwitch
    omega
  have hagree : state (A.firstArm / 3) = bval A.firstArm := by
    rw [hfirstSwitch]
    exact hselected
  have hpin : pin state A.firstArm = state := pin_of_agrees hagree
  have hheadGroove :
      arrive state A.firstArm = (A.mouth, state) := by
    simp [arrive, hfirstBranch, hstem, hpin]
  have hallGrooved :
      PassagesGrooved state ((A.mouth, A.firstArm) :: A.candy) := by
    intro passage hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadGroove
    · exact hgrooved passage htail
  exact physicalTrace_grooved_passages w state A.mouth A.firstArm
    A.secondArm A.candy A.candyTrace.linked hallGrooved
    A.candyTrace.last_link

/-- Candy traversal in the opposite direction, with the reverse passage
list retained explicitly. -/
theorem ManufacturedFlipReflector.candy_reverse_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hselected : state A.actionSwitch = bval A.secondArm)
    (hgrooved : PassagesGrooved state A.candy) :
    PhysicalTrace w (A.mouth, state)
      ((A.mouth, A.secondArm) :: reversePassages A.candy)
      (A.firstArm, state) := by
  have hsecondSwitch := A.secondArm_switch
  have hsecondBranch := A.secondArm_branch
  have hstem : 3 * (A.secondArm / 3) = A.mouth := by
    have hm := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch at hsecondSwitch
    omega
  have hagree : state (A.secondArm / 3) = bval A.secondArm := by
    rw [hsecondSwitch]
    exact hselected
  have hpin : pin state A.secondArm = state := pin_of_agrees hagree
  have hsecondGroove :
      arrive state A.secondArm = (A.mouth, state) := by
    simp [arrive, hsecondBranch, hstem, hpin]
  have hmouthForward := groove_forward hsecondGroove
  cases hcandy : A.candy with
  | nil =>
      have htrace := A.candyTrace
      rw [hcandy] at htrace
      have hlast := htrace.last_link
      have hback : w.link A.secondArm = some A.firstArm :=
        w.symm _ _ (by simpa [lastPassageExit] using hlast)
      simpa [hcandy, reversePassages] using
        (PhysicalTrace.cons hmouthForward hback (PhysicalTrace.nil _))
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have htrace := A.candyTrace
      rw [hcandy] at htrace
      have hgrooved' : PassagesGrooved state ((p, x) :: rest) := by
        simpa [hcandy] using hgrooved
      have hfirstLink : w.link A.firstArm = some p :=
        htrace.linked.1
      have hlast :
          w.link (lastPassageExit x rest) = some A.secondArm := by
        simpa [lastPassageExit] using htrace.last_link
      have hback :
          w.link A.secondArm = some (lastPassageExit x rest) :=
        w.symm _ _ hlast
      have hhead : PhysicalTrace w (A.mouth, state)
          [(A.mouth, A.secondArm)]
          (lastPassageExit x rest, state) :=
        PhysicalTrace.cons hmouthForward hback (PhysicalTrace.nil _)
      have hreverse := physicalTrace_retrace_linked_passages w state
        p x A.firstArm rest htrace.linked.2
        hgrooved' hfirstLink
      simpa [hcandy, reversePassages] using hhead.append hreverse

theorem ManufacturedFlipReflector.reverse_support_simple
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
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

/-- No-change prefix reaching a recorded-direction candy occurrence. -/
theorem ManufacturedFlipReflector.forward_prefix_to_candy_occurrence
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hpaths : PathGrooves [A.runway, A.candy] state)
    (hselected : state A.actionSwitch = bval A.firstArm)
    {before after : List Passage} {p x : Nat}
    (hoccurs : A.candy = before ++ (p, x) :: after) :
    PhysicalTrace w (g, state)
      (A.runway ++ (A.mouth, A.firstArm) :: before) (p, state) ∧
      (∀ passage ∈
          A.runway ++ (A.mouth, A.firstArm) :: before,
        passageSwitch passage ≠ passageSwitch (p, x)) := by
  have hp := pathGrooves_pair.mp hpaths
  have hrun := A.runway_trace state hp.1
  have hcandy := A.candy_forward_trace state hselected hp.2
  have hfull := hrun.append hcandy
  have hgrooved := hfull.grooved_of_switchSimple A.simple
  have hsplit :
      A.runway ++ (A.mouth, A.firstArm) :: A.candy =
        (A.runway ++ (A.mouth, A.firstArm) :: before) ++
          (p, x) :: after := by
    rw [hoccurs]
    simp [List.append_assoc]
  exact simple_grooved_trace_prefix_to_occurrence
    hfull hsplit hgrooved A.simple

/-- No-change prefix reaching the same candy occurrence when the candy is
traversed in the opposite direction. -/
theorem ManufacturedFlipReflector.reverse_prefix_to_candy_occurrence
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hpaths : PathGrooves [A.runway, A.candy] state)
    (hselected : state A.actionSwitch = bval A.secondArm)
    {before after : List Passage} {p x : Nat}
    (hoccurs : A.candy = before ++ (p, x) :: after) :
    PhysicalTrace w (g, state)
      (A.runway ++
        (A.mouth, A.secondArm) :: reversePassages after)
      (x, state) ∧
      (∀ passage ∈
          A.runway ++
            (A.mouth, A.secondArm) :: reversePassages after,
        passageSwitch passage ≠ passageSwitch (x, p)) := by
  have hp := pathGrooves_pair.mp hpaths
  have hrun := A.runway_trace state hp.1
  have hcandy := A.candy_reverse_trace state hselected hp.2
  have hfull := hrun.append hcandy
  have hsimple := A.reverse_support_simple
  have hgrooved := hfull.grooved_of_switchSimple hsimple
  have hreverse : reversePassages A.candy =
      reversePassages after ++ (x, p) :: reversePassages before := by
    rw [hoccurs, reversePassages_append]
    simp [reversePassages, List.append_assoc]
  have hsplit :
      A.runway ++
          (A.mouth, A.secondArm) :: reversePassages A.candy =
        (A.runway ++
          (A.mouth, A.secondArm) :: reversePassages after) ++
            (x, p) :: reversePassages before := by
    rw [hreverse]
    simp [List.append_assoc]
  exact simple_grooved_trace_prefix_to_occurrence
    hfull hsplit hgrooved hsimple

/-- The lobe mouth is absent from both support paths; its flip is therefore
the unique possible support fault seen by another reflector. -/
theorem ManufacturedFlipReflector.support_foreign
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    ∀ path ∈ [A.runway, A.candy], ∀ passage ∈ path,
      passageSwitch passage ≠ A.actionSwitch := by
  intro path hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · intro passage hpassage hEq
    have hsimple := A.simple
    unfold SwitchSimple at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    have hparts := List.nodup_append.mp hsimple
    have hcross := hparts.2.2
    have hne := hcross (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hpassage, rfl⟩)
      A.actionSwitch (by simp [ManufacturedFlipReflector.actionSwitch,
        passageSwitch])
    exact hne hEq
  · intro passage hpassage hEq
    have hsimpleCandy :
        SwitchSimple ((A.mouth, A.firstArm) :: A.candy) := by
      have hsimple := A.simple
      unfold SwitchSimple at hsimple ⊢
      simp only [List.map_append] at hsimple
      exact (List.nodup_append.mp hsimple).2.1
    unfold SwitchSimple at hsimpleCandy
    simp only [List.map_cons, List.nodup_cons] at hsimpleCandy
    apply hsimpleCandy.1
    apply List.mem_map.mpr
    exact ⟨passage, hpassage, hEq⟩

/-- Core capture, packaged on the retained manufactured-reflector data. -/
theorem ManufacturedFlipReflector.capture_from_mouth
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hrunway : PassagesGrooved state A.runway)
    (hcandy : PassagesGrooved state A.candy) :
    stepN w (A.candy.length + 2 + A.runway.length)
      (A.mouth, flipAt state A.actionSwitch) = some (e, state) := by
  exact crossed_revisit_capture_from_mouth w A.runwayTrace A.candyTrace
    A.simple A.crossed A.arms_ne A.entryEdge state hrunway hcandy

/-- Degenerate first-revisit reflector: a grooved arm is linked to itself.
The train traverses the arm out and back, then retraces the runway; its local
action is the identity. -/
structure ManufacturedStayReflector (w : Wiring) (g e : Nat) where
  base : Tongues
  mouthState : Tongues
  runway : List Passage
  mouth : Nat
  arm : Nat
  runwayTrace :
    PhysicalTrace w (g, base) runway (mouth, mouthState)
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
    have hcoreAt (outside : Nat)
        (hmouth : w.link A.mouth = some outside) :=
      self_edge_groove_isReflector w A.selfLink hmouth
    cases hrunway : A.runway with
    | nil =>
        have htrace := A.runwayTrace
        rw [hrunway] at htrace
        have hs : (g, A.base) = (A.mouth, A.mouthState) := by
          simpa [stepN] using htrace.sound
        have hgm : g = A.mouth := congrArg Prod.fst hs
        have hmouth : w.link A.mouth = some e := by
          apply w.symm
          simpa [hgm] using A.entryEdge
        have hcore := hcoreAt e hmouth
        intro state hpaths
        have hp := pathGrooves_pair.mp hpaths
        obtain ⟨hstep, hnext⟩ := hcore state
          (passagesGrooved_singleton.mp hp.2)
        constructor
        · simpa [hrunway, hgm, LocalAction.apply] using hstep
        · exact pathGrooves_pair.mpr
            ⟨(by intro passage hmem; cases hmem),
              passagesGrooved_singleton.mpr hnext⟩
    | cons passage rest =>
        rcases passage with ⟨p, x⟩
        have htrace := A.runwayTrace
        rw [hrunway] at htrace
        have hstart : g = p := htrace.head_arrive.1
        have hlast :
            w.link (lastPassageExit x rest) = some A.mouth :=
          htrace.last_link
        have hmouth :
            w.link A.mouth = some (lastPassageExit x rest) :=
          w.symm _ _ hlast
        have hcore := hcoreAt (lastPassageExit x rest) hmouth
        have hsandwich := sandwich_nonempty_reflector w htrace.linked
          hlast (by simpa [hstart] using A.entryEdge) hcore
          (fun _ hg => hg)
        have hlen :
            (((p, x) :: rest).length + 2 +
                ((p, x) :: rest).length) =
              2 * ((p, x) :: rest).length + 2 := by omega
        rw [hlen] at hsandwich
        intro state hpaths
        have hp := pathGrooves_pair.mp hpaths
        obtain ⟨hstep, hnext⟩ := hsandwich state
          ⟨hp.1, passagesGrooved_singleton.mp hp.2⟩
        constructor
        · simpa [hrunway, hstart, LocalAction.apply] using hstep
        · exact pathGrooves_pair.mpr
            ⟨hnext.1, passagesGrooved_singleton.mpr hnext.2⟩

theorem ManufacturedStayReflector.runway_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedStayReflector w g e)
    (state : Tongues)
    (hgrooved : PassagesGrooved state A.runway) :
    PhysicalTrace w (g, state) A.runway (A.mouth, state) := by
  cases hrunway : A.runway with
  | nil =>
      have htrace := A.runwayTrace
      rw [hrunway] at htrace
      have hs : (g, A.base) = (A.mouth, A.mouthState) := by
        simpa [stepN] using htrace.sound
      have hgm : g = A.mouth := congrArg Prod.fst hs
      simpa [hrunway, hgm] using (PhysicalTrace.nil (g, state))
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have htrace := A.runwayTrace
      rw [hrunway] at htrace
      have hgrooved' :
          PassagesGrooved state ((p, x) :: rest) := by
        simpa [hrunway] using hgrooved
      have hstart : g = p := htrace.head_arrive.1
      have hrebased := physicalTrace_grooved_passages w state p x
        A.mouth rest htrace.linked hgrooved' htrace.last_link
      simpa [hrunway, hstart] using hrebased

theorem ManufacturedStayReflector.runway_foreign
    {w : Wiring} {g e : Nat}
    (A : ManufacturedStayReflector w g e) :
    ∀ passage ∈ A.runway,
      passageSwitch passage ≠ passageSwitch (A.mouth, A.arm) := by
  have hs := A.simple
  unfold SwitchSimple at hs
  simp only [List.map_append, List.map_cons, List.map_nil] at hs
  have hparts := List.nodup_append.mp hs
  intro passage hp hEq
  have hne := hparts.2.2 (passageSwitch passage)
    (List.mem_map.mpr ⟨passage, hp, rfl⟩)
    (passageSwitch (A.mouth, A.arm)) (by simp)
  exact hne hEq

/-- First revisits also have a degenerate identity-reflector case.  We retain
the rich data only for the flip case, since an identity action can never
damage another support. -/
inductive ManufacturedReflector (w : Wiring) (g e : Nat) where
  | stay (A : ManufacturedStayReflector w g e)
  | flip (A : ManufacturedFlipReflector w g e)

def ManufacturedReflector.toSupported
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : SupportedReflector w g e :=
  match A with
  | .stay R => R.toSupported
  | .flip R => R.toSupported

theorem ManufacturedReflector.action_is_stay_or_flip
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    A.toSupported.action = .stay ∨
      ∃ R : ManufacturedFlipReflector w g e,
        A = .flip R ∧
        A.toSupported.action = .flip R.actionSwitch := by
  cases A with
  | stay R => exact Or.inl rfl
  | flip R => exact Or.inr ⟨R, rfl, rfl⟩

/-- Rich first-revisit normal form.  This is the same physical case split as
`first_revisit_cycle_or_supported_reflector`, but the crossed case retains
the construction witness required by the theta-intersection theorem. -/
theorem first_revisit_cycle_or_manufactured_reflector
    (w : Wiring) {start : Nat × Tongues}
    {runway path : List Passage}
    {p x q y e : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hsw : p / 3 = q / 3)
    (hrepeat : arrive u q = (y, v))
    (hentry : w.link e = some start.1) :
    SettlesOnSimpleCycle w (q, u) ∨
      Nonempty (ManufacturedReflector w start.1 e) := by
  have hsimpleExcursion : SwitchSimple ((p, x) :: path) := by
    unfold SwitchSimple at hsimple ⊢
    simp only [List.map_append] at hsimple
    exact (List.nodup_append.mp hsimple).2.1
  have holdStem :
      p = 3 * passageSwitch (p, x) ∨
        x = 3 * passageSwitch (p, x) :=
    hexcursion.passage_stem_endpoint (p, x) List.mem_cons_self
  have hrepeatStem :
      q = 3 * passageSwitch (q, y) ∨
        y = 3 * passageSwitch (q, y) := by
    have hs := arrive_stem_endpoint u q
    rw [hrepeat] at hs
    exact hs
  have hsw' : passageSwitch (p, x) = passageSwitch (q, y) := by
    simpa [passageSwitch] using hsw
  have hshare : p = q ∨ p = y ∨ x = q ∨ x = y :=
    recorded_passages_share_port holdStem hrepeatStem hsw'
  rcases hshare with hpq | hpy | hxq | hxy
  · subst q
    left
    have hp := hexcursion.simple_return_period hsimpleExcursion
    exact ⟨((p, x) :: path).length, u, by simp, hp, hp⟩
  · subst y
    by_cases hxq : x = q
    · subst q
      right
      have hpathNil := same_exit_excursion_path_nil
        hexcursion hsimpleExcursion
      subst path
      have hself : w.link x = some x := by
        simpa [lastPassageExit] using hexcursion.last_link
      refine ⟨.stay {
        base := start.2
        mouthState := u₀
        runway := runway
        mouth := p
        arm := x
        runwayTrace := ?_
        simple := hsimple
        stemEndpoint := hexcursion.passage_stem_endpoint
          (p, x) List.mem_cons_self
        selfLink := hself
        entryEdge := hentry
      }⟩
      simpa using hrunway
    · right
      refine ⟨.flip {
        base := start.2
        mouthState := u₀
        returnState := u
        afterReturn := v
        runway := runway
        candy := path
        mouth := p
        firstArm := x
        secondArm := q
        runwayTrace := ?_
        candyTrace := hexcursion
        simple := hsimple
        crossed := hrepeat
        arms_ne := hxq
        entryEdge := hentry
      }⟩
      simpa using hrunway
  · subst q
    right
    have hpathNil := same_exit_excursion_path_nil
      hexcursion hsimpleExcursion
    subst path
    have hself : w.link x = some x := by
      simpa [lastPassageExit] using hexcursion.last_link
    refine ⟨.stay {
      base := start.2
      mouthState := u₀
      runway := runway
      mouth := p
      arm := x
      runwayTrace := ?_
      simple := hsimple
      stemEndpoint := hexcursion.passage_stem_endpoint
        (p, x) List.mem_cons_self
      selfLink := hself
      entryEdge := hentry
    }⟩
    simpa using hrunway
  · subst y
    left
    have hcycle := hexcursion.simple_same_exit_enters_period
      hsimpleExcursion hrepeat
    exact ⟨((q, x) :: path).length, v, by simp,
      hcycle.1, hcycle.2⟩

/-! ## The first theta contact: runway case -/

/-- If the old reflector's mouth occurs on the new reflector's runway, the
first old reflection breaks exactly that runway groove.  Because the mouth
is a stem, the new traversal is diverted into the old candy; mouth capture
then cancels the flip and returns to the new reflector's starting port.

The theorem deliberately returns the exact dynamic fact needed by the global
composition proof, without a planarity or embedding hypothesis. -/
theorem manufactured_runway_theta_capture
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    {before after : List Passage} {x : Nat}
    (hoccurs :
      B.runway = before ++ (A.mouth, x) :: after) :
    ∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
  have hAcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  have hlinked : LinkedPassages w
      (before ++ (A.mouth, x) :: after) := by
    rw [← hoccurs]
    exact B.runwayTrace.linked
  have hgrooved : PassagesGrooved state
      (before ++ (A.mouth, x) :: after) := by
    rw [← hoccurs]
    exact (pathGrooves_pair.mp hB).1
  have hsimpleRunway : SwitchSimple B.runway := by
    have hs := B.simple
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hsimple : SwitchSimple
      (before ++ (A.mouth, x) :: after) := by
    rwa [← hoccurs]
  cases before with
  | nil =>
      have htrace := B.runwayTrace
      rw [hoccurs] at htrace
      have hstart : e = A.mouth := htrace.head_arrive.1
      refine ⟨A.candy.length + 2 + A.runway.length, ?_⟩
      simpa [hstart] using hAcapture
  | cons passage before =>
      rcases passage with ⟨r, y⟩
      have hprefixData := simple_grooved_prefix_to_occurrence
        hlinked hgrooved hsimple
      have htrace := B.runwayTrace
      rw [hoccurs] at htrace
      have hstart : e = r := htrace.head_arrive.1
      have hprefix :
          PhysicalTrace w (e, state) ((r, y) :: before)
            (A.mouth, state) := by
        simpa [hstart] using hprefixData.1
      have hforeign : ∀ passage ∈ (r, y) :: before,
          passageSwitch passage ≠ A.actionSwitch := by
        intro passage hp
        have hne := hprefixData.2 passage hp
        simpa [passageSwitch,
          ManufacturedFlipReflector.actionSwitch] using hne
      refine ⟨((r, y) :: before).length +
        (A.candy.length + 2 + A.runway.length), ?_⟩
      exact theta_capture_after_unvisited_prefix hprefix hforeign hAcapture

/-- If the same mouth occurrence is oriented the other way on the new
runway, it is met trailing-first.  The passage then repairs the old flip and
the new reflector completes exactly as it would have from the unflipped
state. -/
theorem manufactured_runway_theta_repairs
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hB : PathGrooves [B.runway, B.candy] state)
    {before after : List Passage} {p : Nat}
    (hoccurs :
      B.runway = before ++ (p, A.mouth) :: after) :
    stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, flipAt state A.actionSwitch) =
        some (g, flipAt state B.actionSwitch) := by
  have hsimpleRunway : SwitchSimple B.runway := by
    have hs := B.simple
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hrunwayGrooved : PassagesGrooved state B.runway :=
    (pathGrooves_pair.mp hB).1
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    B.runwayTrace hoccurs hrunwayGrooved hsimpleRunway
  have hmem : (p, A.mouth) ∈ B.runway := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hgrooveBack : arrive state A.mouth = (p, state) :=
    hrunwayGrooved (p, A.mouth) hmem
  have hforward : arrive state p = (A.mouth, state) :=
    groove_forward hgrooveBack
  have hpk : p / 3 = A.actionSwitch := by
    have hs := arrive_exit_switch state p
    rw [hforward] at hs
    simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm
  have hpbranch : p % 3 ≠ 0 := by
    intro hp
    have hne := arrive_exit_ne state p
    rw [hforward] at hne
    have hmouthStem := A.mouth_is_stem
    have hpk' : p / 3 = A.mouth / 3 := by
      simpa [ManufacturedFlipReflector.actionSwitch] using hpk
    apply hne
    omega
  have hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch, hpk] using hne
  have hlinked : LinkedPassages w
      (before ++ (p, A.mouth) :: after) := by
    rw [← hoccurs]
    exact B.runwayTrace.linked
  obtain ⟨q, hlink⟩ : ∃ q, w.link A.mouth = some q := by
    cases after with
    | nil =>
        have htrace := B.runwayTrace
        rw [hoccurs] at htrace
        obtain ⟨middle, hbeforeTrace, htargetTrace⟩ :=
          htrace.split_append
        have hlast := htargetTrace.last_link
        exact ⟨B.mouth, by simpa [lastPassageExit] using hlast⟩
    | cons passage rest =>
        rcases passage with ⟨q, y⟩
        exact ⟨q, linked_after_occurrence hlinked⟩
  have htarget :
      PhysicalTrace w (p, state) [(p, A.mouth)] (q, state) :=
    PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
  have hprefixTarget := hprefixData.1.append htarget
  have hprefixSound :
      stepN w (before.length + 1) (e, state) = some (q, state) := by
    simpa using hprefixTarget.sound
  have hBfull := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBfull
  have hRlen : B.runway.length =
      before.length + 1 + after.length := by
    rw [hoccurs]
    simp only [List.length_append, List.length_cons]
    omega
  let tailSteps := after.length + B.candy.length + 2 + B.runway.length
  have hlen : 2 * B.runway.length + B.candy.length + 2 =
      (before.length + 1) + tailSteps := by
    dsimp [tailSteps]
    omega
  have hsuffix :
      stepN w tailSteps (q, state) =
        some (g, flipAt state B.actionSwitch) := by
    rw [hlen, stepN_add, hprefixSound] at hBfull
    exact hBfull
  have hrepair := flipped_prefix_trailing_then hprefixData.1 hforeign
    hpk hpbranch hforward hlink hsuffix
  simpa [tailSteps, hlen] using hrepair

/-- Orientation-free runway contact.  A visit to the old mouth switch on the
new runway is necessarily either the captured facing case or the self-healing
trailing case; degree three leaves no third possibility. -/
theorem manufactured_runway_fault_dichotomy
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (passage : Passage)
    (hmem : passage ∈ B.runway)
    (hsw : passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w (2 * B.runway.length + B.candy.length + 2)
        (e, flipAt state A.actionSwitch) =
          some (g, flipAt state B.actionSwitch) := by
  rcases passage with ⟨p, x⟩
  obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
  have hstem := B.runwayTrace.passage_stem_endpoint (p, x) hmem
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  change p / 3 = A.actionSwitch at hsw
  have hmouth : A.mouth = 3 * A.actionSwitch := by
    have hs := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch
    omega
  rcases hstem with hp | hx
  · have hpMouth : p = A.mouth := by
      omega
    subst p
    left
    exact manufactured_runway_theta_capture A B state hA hB hoccurs
  · have hxMouth : x = A.mouth := by
      omega
    right
    exact manufactured_runway_theta_repairs A B state hB
      (by simpa [hxMouth] using hoccurs)

/-! ## The first theta contact: candy case -/

theorem manufactured_candy_forward_theta_capture
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.firstArm)
    {before after : List Passage} {x : Nat}
    (hoccurs : B.candy = before ++ (A.mouth, x) :: after) :
    ∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
  have hprefixData := B.forward_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hforeign : ∀ passage ∈
      B.runway ++ (B.mouth, B.firstArm) :: before,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hne
  have hcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  refine ⟨(B.runway ++
      (B.mouth, B.firstArm) :: before).length +
        (A.candy.length + 2 + A.runway.length), ?_⟩
  exact theta_capture_after_unvisited_prefix hprefixData.1
    hforeign hcapture

theorem manufactured_candy_reverse_theta_capture
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.secondArm)
    {before after : List Passage} {p : Nat}
    (hoccurs : B.candy = before ++ (p, A.mouth) :: after) :
    ∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
  have hprefixData := B.reverse_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hforeign : ∀ passage ∈
      B.runway ++
        (B.mouth, B.secondArm) :: reversePassages after,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hne
  have hcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  refine ⟨(B.runway ++
      (B.mouth, B.secondArm) :: reversePassages after).length +
        (A.candy.length + 2 + A.runway.length), ?_⟩
  exact theta_capture_after_unvisited_prefix hprefixData.1
    hforeign hcapture

theorem manufactured_candy_forward_theta_repairs
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.firstArm)
    {before after : List Passage} {p : Nat}
    (hoccurs : B.candy = before ++ (p, A.mouth) :: after) :
    stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, flipAt state A.actionSwitch) =
        some (g, flipAt state B.actionSwitch) := by
  let pre := B.runway ++ (B.mouth, B.firstArm) :: before
  have hprefixData := B.forward_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hmem : (p, A.mouth) ∈ B.candy := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hgrooveBack : arrive state A.mouth = (p, state) :=
    (pathGrooves_pair.mp hB).2 (p, A.mouth) hmem
  have hforward : arrive state p = (A.mouth, state) :=
    groove_forward hgrooveBack
  have hpk : p / 3 = A.actionSwitch := by
    have hs := arrive_exit_switch state p
    rw [hforward] at hs
    simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm
  have hpbranch : p % 3 ≠ 0 := by
    intro hp
    have hne := arrive_exit_ne state p
    rw [hforward] at hne
    have hm := A.mouth_is_stem
    have hpk' : p / 3 = A.mouth / 3 := by
      simpa [ManufacturedFlipReflector.actionSwitch] using hpk
    apply hne
    omega
  have hforeign : ∀ passage ∈ pre,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [pre, passageSwitch, hpk] using hne
  obtain ⟨q, hlink⟩ : ∃ q, w.link A.mouth = some q := by
    cases after with
    | nil =>
        have hlast := B.candyTrace.last_link
        rw [hoccurs, lastPassageExit_append_cons] at hlast
        exact ⟨B.secondArm, hlast⟩
    | cons passage rest =>
        rcases passage with ⟨q, y⟩
        have hcandyLinked : LinkedPassages w B.candy := by
          have htrace := B.candyTrace
          cases htrace with
          | cons harrive hheadLink candyTail =>
              exact candyTail.linked
        rw [hoccurs] at hcandyLinked
        exact ⟨q, linked_after_occurrence hcandyLinked⟩
  have htarget : PhysicalTrace w (p, state)
      [(p, A.mouth)] (q, state) :=
    PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
  have hprefixTarget := hprefixData.1.append htarget
  let tailSteps := after.length + 1 + B.runway.length
  have hClen : B.candy.length =
      before.length + 1 + after.length := by
    rw [hoccurs]
    simp only [List.length_append, List.length_cons]
    omega
  have hlen : 2 * B.runway.length + B.candy.length + 2 =
      (pre ++ [(p, A.mouth)]).length + tailSteps := by
    dsimp [pre, tailSteps]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hBfull := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBfull
  have hsuffix : stepN w tailSteps (q, state) =
      some (g, flipAt state B.actionSwitch) :=
    suffix_after_physical_prefix hprefixTarget hlen hBfull
  have hrepair := flipped_prefix_trailing_then hprefixData.1 hforeign
    hpk hpbranch hforward hlink hsuffix
  have hrepairLen : pre.length + 1 + tailSteps =
      2 * B.runway.length + B.candy.length + 2 := by
    dsimp [pre, tailSteps]
    simp only [List.length_append, List.length_cons]
    omega
  rwa [hrepairLen] at hrepair

theorem manufactured_candy_reverse_theta_repairs
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.secondArm)
    {before after : List Passage} {x : Nat}
    (hoccurs : B.candy = before ++ (A.mouth, x) :: after) :
    stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, flipAt state A.actionSwitch) =
        some (g, flipAt state B.actionSwitch) := by
  let pre := B.runway ++
    (B.mouth, B.secondArm) :: reversePassages after
  have hprefixData := B.reverse_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hmem : (A.mouth, x) ∈ B.candy := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hgroove : arrive state x = (A.mouth, state) :=
    (pathGrooves_pair.mp hB).2 (A.mouth, x) hmem
  have hxk : x / 3 = A.actionSwitch := by
    have hs := arrive_exit_switch state x
    rw [hgroove] at hs
    simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm
  have hxbranch : x % 3 ≠ 0 := by
    intro hx
    have hne := arrive_exit_ne state x
    rw [hgroove] at hne
    have hm := A.mouth_is_stem
    have hxk' : x / 3 = A.mouth / 3 := by
      simpa [ManufacturedFlipReflector.actionSwitch] using hxk
    apply hne
    omega
  have hforeign : ∀ passage ∈ pre,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [pre, passageSwitch, hxk] using hne
  have hcandyLinked : LinkedPassages w B.candy := by
    have htrace := B.candyTrace
    cases htrace with
    | cons harrive hheadLink candyTail => exact candyTail.linked
  obtain ⟨q, hlink⟩ : ∃ q, w.link A.mouth = some q := by
    cases before with
    | nil =>
        have htrace := B.candyTrace
        rw [hoccurs] at htrace
        cases htrace with
        | @cons p₀ x₀ q₀ u₀ v₀ passages finish
            harrive hheadLink candyTail =>
            have hstart : q₀ = A.mouth := candyTail.head_arrive.1
            rw [hstart] at hheadLink
            exact ⟨B.firstArm, w.symm _ _ hheadLink⟩
    | cons passage rest =>
        rcases passage with ⟨r, y⟩
        have hcandyLinked' := hcandyLinked
        rw [hoccurs] at hcandyLinked'
        have hboundary := linked_boundary_of_append hcandyLinked'
        exact ⟨lastPassageExit y rest, w.symm _ _ hboundary⟩
  have htarget : PhysicalTrace w (x, state)
      [(x, A.mouth)] (q, state) :=
    PhysicalTrace.cons hgroove hlink (PhysicalTrace.nil _)
  have hprefixTarget := hprefixData.1.append htarget
  let tailSteps := before.length + 1 + B.runway.length
  have hClen : B.candy.length =
      before.length + 1 + after.length := by
    rw [hoccurs]
    simp only [List.length_append, List.length_cons]
    omega
  have hlen : 2 * B.runway.length + B.candy.length + 2 =
      (pre ++ [(x, A.mouth)]).length + tailSteps := by
    dsimp [pre, tailSteps]
    simp only [List.length_append, List.length_cons, List.length_nil,
      reversePassages_length]
    omega
  have hBfull := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBfull
  have hsuffix : stepN w tailSteps (q, state) =
      some (g, flipAt state B.actionSwitch) :=
    suffix_after_physical_prefix hprefixTarget hlen hBfull
  have hrepair := flipped_prefix_trailing_then hprefixData.1 hforeign
    hxk hxbranch hgroove hlink hsuffix
  have hrepairLen : pre.length + 1 + tailSteps =
      2 * B.runway.length + B.candy.length + 2 := by
    dsimp [pre, tailSteps]
    simp only [List.length_append, List.length_cons,
      reversePassages_length]
    omega
  rwa [hrepairLen] at hrepair

/-- Orientation-free candy contact.  The selected candy arm determines
whether the recorded path is traversed forward or backward; in either
direction degree three again leaves exactly capture or self-repair. -/
theorem manufactured_candy_fault_dichotomy
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (passage : Passage)
    (hmem : passage ∈ B.candy)
    (hsw : passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w (2 * B.runway.length + B.candy.length + 2)
        (e, flipAt state A.actionSwitch) =
          some (g, flipAt state B.actionSwitch) := by
  rcases passage with ⟨p, x⟩
  obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
  have hstem := B.candyTrace.passage_stem_endpoint (p, x)
    (List.mem_cons_of_mem _ hmem)
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  change p / 3 = A.actionSwitch at hsw
  have hmouth : A.mouth = 3 * A.actionSwitch := by
    have hs := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch
    omega
  rcases B.selected_arm state with hforward | hreverse
  · rcases hstem with hp | hx
    · have hpMouth : p = A.mouth := by omega
      subst p
      left
      exact manufactured_candy_forward_theta_capture A B state
        hA hB hforward hoccurs
    · have hxMouth : x = A.mouth := by omega
      right
      exact manufactured_candy_forward_theta_repairs A B state
        hB hforward (by simpa [hxMouth] using hoccurs)
  · rcases hstem with hp | hx
    · have hpMouth : p = A.mouth := by omega
      right
      exact manufactured_candy_reverse_theta_repairs A B state
        hB hreverse (by simpa [hpMouth] using hoccurs)
    · have hxMouth : x = A.mouth := by omega
      left
      exact manufactured_candy_reverse_theta_capture A B state
        hA hB hreverse (by simpa [hxMouth] using hoccurs)

theorem manufactured_support_fault_dichotomy
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w (2 * B.runway.length + B.candy.length + 2)
        (e, flipAt state A.actionSwitch) =
          some (g, flipAt state B.actionSwitch) := by
  obtain ⟨path, hp, passage, hmem, hsw⟩ := hcontact
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact manufactured_runway_fault_dichotomy A B state hA hB
      passage hmem hsw
  · exact manufactured_candy_fault_dichotomy A B state hA hB
      passage hmem hsw

/-- One complete macro-step in the one-sided theta case.  Whether the new
reflector self-repairs or is captured, starting at the old reflector's front
returns to that same front with exactly the new reflector's action applied.
-/
theorem manufactured_theta_half
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    ∃ travel, 0 < travel ∧
      stepN w travel (g, state) =
        some (g, flipAt state B.actionSwitch) := by
  have hArun := (A.toSupported.run state hA).1
  have hBrun := (B.toSupported.run state hB).1
  change stepN w (2 * A.runway.length + A.candy.length + 2)
      (g, state) = some (e, flipAt state A.actionSwitch) at hArun
  change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBrun
  have hfault := manufactured_support_fault_dichotomy
    A B state hA hB hcontact
  rcases hfault with hcapture | hrepair
  · obtain ⟨captureTravel, hcapture⟩ := hcapture
    refine ⟨(2 * A.runway.length + A.candy.length + 2) +
      captureTravel +
        (2 * B.runway.length + B.candy.length + 2), by omega, ?_⟩
    have hlen :
        (2 * A.runway.length + A.candy.length + 2) +
            captureTravel +
              (2 * B.runway.length + B.candy.length + 2) =
          (2 * A.runway.length + A.candy.length + 2) +
            (captureTravel +
              (2 * B.runway.length + B.candy.length + 2)) := by omega
    rw [hlen, stepN_add, hArun]
    simp only [Option.bind_some]
    rw [stepN_add, hcapture]
    exact hBrun
  · refine ⟨(2 * A.runway.length + A.candy.length + 2) +
      (2 * B.runway.length + B.candy.length + 2), by omega, ?_⟩
    rw [stepN_add, hArun]
    exact hrepair

/-- If only `A`'s mouth lies on `B`'s support, the theta macro-step can be
run twice.  `B`'s local action preserves `A`'s support, and its second
application restores the original tongue vector. -/
theorem manufactured_one_sided_theta_period
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch)
    (hBA : (LocalAction.flip B.actionSwitch).Avoids
      [A.runway, A.candy]) :
    ∃ travel, 0 < travel ∧
      stepN w travel (g, state) = some (g, state) := by
  obtain ⟨firstTravel, hfirstPos, hfirst⟩ :=
    manufactured_theta_half A B state hA hB hcontact
  have hA' : PathGrooves [A.runway, A.candy]
      (flipAt state B.actionSwitch) :=
    hA.after_avoiding_action hBA
  have hB' : PathGrooves [B.runway, B.candy]
      (flipAt state B.actionSwitch) :=
    (B.toSupported.run state hB).2
  obtain ⟨secondTravel, hsecondPos, hsecond⟩ :=
    manufactured_theta_half A B
      (flipAt state B.actionSwitch) hA' hB' hcontact
  refine ⟨firstTravel + secondTravel, by omega, ?_⟩
  rw [stepN_add, hfirst]
  simp only [Option.bind_some]
  rw [hsecond, flipAt_flipAt]

/-- If both lobe mouths lie on the opposite support, the first macro-step
reaches `flip B state`; from there the symmetric theta fault and the original
one form a closed cycle.  Thus mutual intersection is not a third dynamical
component: it is absorbed after one macro-step. -/
theorem manufactured_two_sided_theta_settles
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hAB : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch)
    (hBA : ∃ path ∈ [A.runway, A.candy],
      ∃ passage ∈ path,
        passageSwitch passage = B.actionSwitch) :
    ∃ lead period, 0 < period ∧
      stepN w lead (g, state) =
        some (g, flipAt state B.actionSwitch) ∧
      stepN w period (g, flipAt state B.actionSwitch) =
        some (g, flipAt state B.actionSwitch) := by
  obtain ⟨lead, hleadPos, hlead⟩ :=
    manufactured_theta_half A B state hA hB hAB
  have hreverseFault := manufactured_support_fault_dichotomy
    B A state hB hA hBA
  have hforwardFault := manufactured_support_fault_dichotomy
    A B state hA hB hAB
  have hBrun := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBrun
  rcases hreverseFault with hreverseCapture | hreverseRepair
  · obtain ⟨reverseTravel, hreverseCapture⟩ := hreverseCapture
    refine ⟨lead, reverseTravel + lead, by omega, hlead, ?_⟩
    rw [stepN_add, hreverseCapture]
    exact hlead
  · rcases hforwardFault with hforwardCapture | hforwardRepair
    · obtain ⟨forwardTravel, hforwardCapture⟩ := hforwardCapture
      refine ⟨lead,
        (2 * A.runway.length + A.candy.length + 2) +
        forwardTravel +
          (2 * B.runway.length + B.candy.length + 2), by omega,
            hlead, ?_⟩
      have hlen :
          (2 * A.runway.length + A.candy.length + 2) +
                forwardTravel +
                  (2 * B.runway.length + B.candy.length + 2) =
            (2 * A.runway.length + A.candy.length + 2) +
              (forwardTravel +
                (2 * B.runway.length + B.candy.length + 2)) := by omega
      rw [hlen, stepN_add, hreverseRepair]
      simp only [Option.bind_some]
      rw [stepN_add, hforwardCapture]
      exact hBrun
    · refine ⟨lead,
        (2 * A.runway.length + A.candy.length + 2) +
          (2 * B.runway.length + B.candy.length + 2), by omega,
            hlead, ?_⟩
      rw [stepN_add, hreverseRepair]
      exact hforwardRepair

/-! ## Degenerate identity reflector intersections -/

/-- Generic runway-fault engine.  It isolates the only data used by the
runway proofs above, so the same theta argument applies to the outward leg of
an identity reflector. -/
theorem runway_fault_dichotomy_general
    {w : Wiring} {g e total tailSteps : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    {base : Tongues} {runway : List Passage}
    {newFinish finish : Nat × Tongues}
    (htrace : PhysicalTrace w (e, base) runway newFinish)
    (hgrooved : PassagesGrooved state runway)
    (hsimple : SwitchSimple runway)
    (passage : Passage)
    {before after : List Passage}
    (hoccurs : runway = before ++ passage :: after)
    (hsw : passageSwitch passage = A.actionSwitch)
    (hdecomp : total = before.length + 1 + tailSteps)
    (hnormal : stepN w total (e, state) = some finish) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w total (e, flipAt state A.actionSwitch) = some finish := by
  rcases passage with ⟨p, x⟩
  have hmem : (p, x) ∈ runway := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    htrace hoccurs hgrooved hsimple
  have hstem := htrace.passage_stem_endpoint (p, x) hmem
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  change p / 3 = A.actionSwitch at hsw
  have hmouth : A.mouth = 3 * A.actionSwitch := by
    have hs := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch
    omega
  rcases hstem with hp | hx
  · have hpMouth : p = A.mouth := by omega
    subst p
    left
    have hforeign : ∀ passage ∈ before,
        passageSwitch passage ≠ A.actionSwitch := by
      intro passage hp
      have hne := hprefixData.2 passage hp
      simpa [passageSwitch,
        ManufacturedFlipReflector.actionSwitch] using hne
    have hcapture := A.capture_from_mouth state
      (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
    refine ⟨before.length +
      (A.candy.length + 2 + A.runway.length), ?_⟩
    exact theta_capture_after_unvisited_prefix hprefixData.1
      hforeign hcapture
  · have hxMouth : x = A.mouth := by omega
    have htargetMem : (p, x) ∈ runway := hmem
    have hgrooveBack : arrive state x = (p, state) :=
      hgrooved (p, x) htargetMem
    have hforward : arrive state p = (x, state) :=
      groove_forward hgrooveBack
    have hpbranch : p % 3 ≠ 0 := by
      intro hpmod
      have hne := arrive_exit_ne state p
      rw [hforward] at hne
      apply hne
      omega
    have hforeign : ∀ prior ∈ before,
        passageSwitch prior ≠ A.actionSwitch := by
      intro prior hprior
      have hne := hprefixData.2 prior hprior
      simpa [passageSwitch, hsw] using hne
    obtain ⟨q, hlink⟩ : ∃ q, w.link x = some q := by
      cases after with
      | nil =>
          have htrace' := htrace
          rw [hoccurs] at htrace'
          obtain ⟨middle, hbeforeTrace, htargetTrace⟩ :=
            htrace'.split_append
          have hlast := htargetTrace.last_link
          exact ⟨newFinish.1,
            by simpa [lastPassageExit] using hlast⟩
      | cons next rest =>
          rcases next with ⟨q, y⟩
          have hlinked : LinkedPassages w
              (before ++ (p, x) :: (q, y) :: rest) := by
            rw [← hoccurs]
            exact htrace.linked
          exact ⟨q, linked_after_occurrence hlinked⟩
    have htarget : PhysicalTrace w (p, state)
        [(p, x)] (q, state) :=
      PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
    have hprefixTarget := hprefixData.1.append htarget
    have hlen := hdecomp
    have hsuffix : stepN w tailSteps (q, state) = some finish := by
      have hprefixLen :
          (before ++ [(p, x)]).length = before.length + 1 := by simp
      apply suffix_after_physical_prefix hprefixTarget
      · simpa [hprefixLen] using hlen
      · exact hnormal
    right
    have hrepair := flipped_prefix_trailing_then hprefixData.1 hforeign
      hsw hpbranch hforward hlink hsuffix
    rwa [← hlen] at hrepair

theorem manufactured_stay_support_fault_dichotomy
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedStayReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, [(B.mouth, B.arm)]] state)
    (hcontact : ∃ path ∈ [B.runway, [(B.mouth, B.arm)]],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w (2 * B.runway.length + 2)
        (e, flipAt state A.actionSwitch) = some (g, state) := by
  have hnormal := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + 2) (e, state) =
      some (g, state) at hnormal
  obtain ⟨path, hp, passage, hmem, hsw⟩ := hcontact
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
    have hsimpleRunway : SwitchSimple B.runway := by
      have hs := B.simple
      unfold SwitchSimple at hs ⊢
      simp only [List.map_append] at hs
      exact (List.nodup_append.mp hs).1
    have hRlen : B.runway.length =
        before.length + 1 + after.length := by
      rw [hoccurs]
      simp only [List.length_append, List.length_cons]
      omega
    let tailSteps := after.length + 2 + B.runway.length
    have hdecomp : 2 * B.runway.length + 2 =
        before.length + 1 + tailSteps := by
      dsimp [tailSteps]
      omega
    exact runway_fault_dichotomy_general
      (total := 2 * B.runway.length + 2)
      (tailSteps := tailSteps) A state hA B.runwayTrace
      (pathGrooves_pair.mp hB).1 hsimpleRunway passage
      hoccurs hsw hdecomp hnormal
  · simp only [List.mem_singleton] at hmem
    subst passage
    let route := B.runway ++ [(B.mouth, B.arm)]
    have hrun := B.runway_trace state (pathGrooves_pair.mp hB).1
    have hgrooveBack := passagesGrooved_singleton.mp
      (pathGrooves_pair.mp hB).2
    have hforward := groove_forward hgrooveBack
    have htarget : PhysicalTrace w (B.mouth, state)
        [(B.mouth, B.arm)] (B.arm, state) :=
      PhysicalTrace.cons hforward B.selfLink (PhysicalTrace.nil _)
    have hrouteTrace := hrun.append htarget
    have hrouteGrooved := hrouteTrace.grooved_of_switchSimple B.simple
    have hoccurs : route =
        B.runway ++ (B.mouth, B.arm) :: [] := by rfl
    have hdecomp : 2 * B.runway.length + 2 =
        B.runway.length + 1 + (B.runway.length + 1) := by omega
    exact runway_fault_dichotomy_general
      (total := 2 * B.runway.length + 2)
      (tailSteps := B.runway.length + 1) A state hA hrouteTrace
      hrouteGrooved B.simple (B.mouth, B.arm)
      hoccurs hsw hdecomp hnormal

/-- A flip reflector followed by a degenerate identity reflector always
closes after one theta macro-step, whether the supports are disjoint or meet.
-/
theorem manufactured_flip_then_stay_theta_period
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedStayReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, [(B.mouth, B.arm)]] state)
    (hcontact : ∃ path ∈ [B.runway, [(B.mouth, B.arm)]],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    ∃ travel, 0 < travel ∧
      stepN w travel (g, state) = some (g, state) := by
  have hArun := (A.toSupported.run state hA).1
  change stepN w (2 * A.runway.length + A.candy.length + 2)
      (g, state) = some (e, flipAt state A.actionSwitch) at hArun
  have hBrun := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + 2)
      (e, state) = some (g, state) at hBrun
  have hfault := manufactured_stay_support_fault_dichotomy
    A B state hA hB hcontact
  rcases hfault with hcapture | hrepair
  · obtain ⟨captureTravel, hcapture⟩ := hcapture
    refine ⟨(2 * A.runway.length + A.candy.length + 2) +
      captureTravel + (2 * B.runway.length + 2), by omega, ?_⟩
    have hlen :
        (2 * A.runway.length + A.candy.length + 2) +
              captureTravel + (2 * B.runway.length + 2) =
          (2 * A.runway.length + A.candy.length + 2) +
            (captureTravel + (2 * B.runway.length + 2)) := by omega
    rw [hlen, stepN_add, hArun]
    simp only [Option.bind_some]
    rw [stepN_add, hcapture]
    exact hBrun
  · refine ⟨(2 * A.runway.length + A.candy.length + 2) +
      (2 * B.runway.length + 2), by omega, ?_⟩
    rw [stepN_add, hArun]
    exact hrepair

/-! ## Complete composition of two manufactured reflectors -/

theorem contact_of_not_avoids_flip
    {paths : List (List Passage)} {k : Nat}
    (hnot : ¬ (LocalAction.flip k).Avoids paths) :
    ∃ path ∈ paths, ∃ passage ∈ path,
      passageSwitch passage = k := by
  classical
  by_cases hcontact : ∃ path ∈ paths, ∃ passage ∈ path,
      passageSwitch passage = k
  · exact hcontact
  · exfalso
    apply hnot
    intro path hp passage hpass hEq
    apply hcontact
    exact ⟨path, hp, passage, hpass, hEq⟩

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

/-- Eventual periodicity stated directly on raw train configurations. -/
def EventuallyPeriodic (w : Wiring) (start : Nat × Tongues) : Prop :=
  ∃ lead period settled,
    0 < period ∧
    stepN w lead start = some settled ∧
    stepN w period settled = some settled

theorem manufactured_pair_period_of_avoids
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths) :
    stepN w (2 * (A.toSupported.travel + B.toSupported.travel))
      (g, state) = some (g, state) :=
  A.toSupported.paired_period B.toSupported hAB hBA state hA hB

theorem eventuallyPeriodic_of_period
    {w : Wiring} {start : Nat × Tongues} {period : Nat}
    (hpos : 0 < period)
    (hperiod : stepN w period start = some start) :
    EventuallyPeriodic w start := by
  exact ⟨0, period, start, hpos, by simp [stepN], hperiod⟩

theorem manufactured_pair_eventuallyPeriodic_of_avoids
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths) :
    EventuallyPeriodic w (g, state) := by
  have hperiod := manufactured_pair_period_of_avoids
    A B state hA hB hAB hBA
  apply eventuallyPeriodic_of_period
    (period := 2 * (A.toSupported.travel + B.toSupported.travel))
  · have hAp := A.travel_pos
    have hBp := B.travel_pos
    omega
  · exact hperiod

/-- **Complete theta theorem for two first-revisit components.**  Any two
opposite manufactured reflectors—identity or one-switch flip, disjoint or
intersecting in either direction—lead to a genuine periodic raw train
configuration.  No planarity or small-`N` argument occurs. -/
theorem manufactured_pair_eventually_periodic
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state) :
    EventuallyPeriodic w (g, state) := by
  classical
  cases A with
  | stay SA =>
      cases B with
      | stay SB =>
          exact manufactured_pair_eventuallyPeriodic_of_avoids
            (.stay SA) (.stay SB) state hA hB (by trivial) (by trivial)
      | flip FB =>
          change PathGrooves [SA.runway, [(SA.mouth, SA.arm)]] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
              [SA.runway, [(SA.mouth, SA.arm)]]
          · exact manufactured_pair_eventuallyPeriodic_of_avoids
              (.stay SA) (.flip FB) state hA hB (by trivial) hBA
          · have hcontact := contact_of_not_avoids_flip hBA
            obtain ⟨period, hpos, hperiod⟩ :=
              manufactured_flip_then_stay_theta_period
                FB SA state hB hA hcontact
            have hlead := (SA.toSupported.run state hA).1
            change stepN w (2 * SA.runway.length + 2) (g, state) =
              some (e, state) at hlead
            exact ⟨2 * SA.runway.length + 2, period, (e, state),
              hpos, hlead, hperiod⟩
  | flip FA =>
      cases B with
      | stay SB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves [SB.runway, [(SB.mouth, SB.arm)]] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [SB.runway, [(SB.mouth, SB.arm)]]
          · exact manufactured_pair_eventuallyPeriodic_of_avoids
              (.flip FA) (.stay SB) state hA hB hAB (by trivial)
          · have hcontact := contact_of_not_avoids_flip hAB
            obtain ⟨period, hpos, hperiod⟩ :=
              manufactured_flip_then_stay_theta_period
                FA SB state hA hB hcontact
            exact eventuallyPeriodic_of_period hpos hperiod
      | flip FB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [FB.runway, FB.candy]
          · by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
                [FA.runway, FA.candy]
            · exact manufactured_pair_eventuallyPeriodic_of_avoids
                (.flip FA) (.flip FB) state hA hB hAB hBA
            · have hcontactBA := contact_of_not_avoids_flip hBA
              have hArun := (FA.toSupported.run state hA)
              have hA' : PathGrooves [FA.runway, FA.candy]
                  (flipAt state FA.actionSwitch) := hArun.2
              have hB' : PathGrooves [FB.runway, FB.candy]
                  (flipAt state FA.actionSwitch) :=
                hB.after_avoiding_action hAB
              obtain ⟨period, hpos, hperiod⟩ :=
                manufactured_one_sided_theta_period FB FA
                  (flipAt state FA.actionSwitch) hB' hA'
                  hcontactBA hAB
              have hArunResult := hArun.1
              change stepN w (2 * FA.runway.length + FA.candy.length + 2)
                  (g, state) =
                    some (e, flipAt state FA.actionSwitch) at hArunResult
              exact ⟨2 * FA.runway.length + FA.candy.length + 2,
                period, (e, flipAt state FA.actionSwitch),
                hpos, hArunResult, hperiod⟩
          · have hcontactAB := contact_of_not_avoids_flip hAB
            by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
                [FA.runway, FA.candy]
            · obtain ⟨period, hpos, hperiod⟩ :=
                manufactured_one_sided_theta_period FA FB state
                  hA hB hcontactAB hBA
              exact eventuallyPeriodic_of_period hpos hperiod
            · have hcontactBA := contact_of_not_avoids_flip hBA
              obtain ⟨lead, period, hpos, hlead, hperiod⟩ :=
                manufactured_two_sided_theta_settles FA FB state
                  hA hB hcontactAB hcontactBA
              exact ⟨lead, period,
                (g, flipAt state FB.actionSwitch),
                hpos, hlead, hperiod⟩

end GeneralN
