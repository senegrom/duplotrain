import TrackTrace

/-!
# Arbitrary-path lobe reflectors

The first-repeated-edge theorem in `TrackTrace` says that a crossed rejoin
creates a lobe.  This file proves the reusable dynamics of the nondegenerate
case: a stem is the mouth, its two branches are joined by an arbitrary simple
grooved path, and every visit through the mouth swaps the selected branch.

The result is a two-state reflector over the raw `Wiring/stepN` semantics.
It is the component needed to compose two lobes into the dumbbell Gray square.
-/

namespace GeneralN

/-- Pinning the other branch and then pinning `x` restores a state which was
already aligned with `x`. -/
theorem pin_other_then_restore {u : Tongues} {x q : Nat}
    (hsw : x / 3 = q / 3) (haligned : u (x / 3) = bval x) :
    pin (pin u q) x = u := by
  funext j
  unfold pin
  by_cases hj : j = x / 3
  · rw [if_pos hj, hj, haligned]
  · rw [if_neg hj]
    have hjq : j ≠ q / 3 := by
      rw [← hsw]
      exact hj
    rw [if_neg hjq]

/-- Changing the mouth switch preserves every groove on a switch-disjoint
interior path. -/
theorem grooved_after_pin_other
    {u : Tongues} {q : Nat} {path : List Passage}
    (hgrooved : PassagesGrooved u path)
    (hforeign : ∀ passage ∈ path,
      passageSwitch passage ≠ q / 3) :
    PassagesGrooved (pin u q) path := by
  intro passage hp
  have hold := hgrooved passage hp
  have hexitSwitch : passage.2 / 3 = passageSwitch passage := by
    have hs := arrive_exit_switch u passage.2
    rw [hold] at hs
    exact hs.symm
  apply groove_transfer hold
  unfold pin
  rw [if_neg (by
    rw [hexitSwitch]
    exact hforeign passage hp)]

/-- Flipping a switch preserves every groove on a switch-disjoint path. -/
theorem grooved_after_flip_other
    {u : Tongues} {k : Nat} {path : List Passage}
    (hgrooved : PassagesGrooved u path)
    (hforeign : ∀ passage ∈ path, passageSwitch passage ≠ k) :
    PassagesGrooved (flipAt u k) path := by
  intro passage hp
  have hold := hgrooved passage hp
  have hexitSwitch : passage.2 / 3 = passageSwitch passage := by
    have hs := arrive_exit_switch u passage.2
    rw [hold] at hs
    exact hs.symm
  apply groove_transfer hold
  unfold flipAt
  rw [if_neg (by
    rw [hexitSwitch]
    exact hforeign passage hp)]

/-- The two distinct branch ports of one switch encode opposite Booleans. -/
theorem branch_values_opposite {x q : Nat}
    (hxbranch : x % 3 ≠ 0) (hqbranch : q % 3 ≠ 0)
    (hsw : x / 3 = q / 3) (hne : x ≠ q) :
    bval q = !(bval x) := by grind [bval]

/-- Pinning a port whose value is opposite to the current tongue is exactly
`flipAt` on that switch. -/
theorem pin_eq_flipAt {u : Tongues} {q k : Nat}
    (hq : q / 3 = k) (hopposite : bval q = !(u k)) :
    pin u q = flipAt u k := by
  funext j
  unfold pin flipAt
  by_cases hj : j = k
  · rw [if_pos (by simpa [hq] using hj), if_pos hj, hj, hopposite]
  · rw [if_neg (by
      intro h
      apply hj
      simpa [hq] using h), if_neg hj]

/-- **Arbitrary mouth-avoiding lobe = two-state reflector.**

`p` is the stem/mouth, `x` and `q` are its two candy-side branches, and
`path` is a grooved path from the edge at `x` to the edge at `q` whose
interior passages avoid the mouth switch.
The stem edge leads to `outside`.  One reflection changes `u` to `pin u q`;
the next restores `u`, with the same exact travel time. -/
theorem stem_lobe_two_state_reflector_foreign
    (w : Wiring) {p x q outside : Nat} {u : Tongues}
    (path : List Passage)
    (hpstem : p % 3 = 0)
    (hxbranch : x % 3 ≠ 0) (hqbranch : q % 3 ≠ 0)
    (hpx : p / 3 = x / 3) (hpq : p / 3 = q / 3)
    (hpathForeign : ∀ passage ∈ path,
      passageSwitch passage ≠ q / 3)
    (hlinked : LinkedPassages w ((p, x) :: path))
    (hgrooved : PassagesGrooved u ((p, x) :: path))
    (hfinal : w.link (lastPassageExit x path) = some q)
    (hmouth : w.link p = some outside) :
    let u' := pin u q
    stepN w (path.length + 2) (p, u) = some (outside, u') ∧
      stepN w (path.length + 2) (p, u') = some (outside, u) := by
  let u' := pin u q
  have hpqStem : 3 * (q / 3) = p := by omega
  have hpxStem : 3 * (x / 3) = p := by omega
  have holdHead : arrive u x = (p, u) :=
    hgrooved (p, x) (by simp)
  have hualigned : u (x / 3) = bval x := by
    unfold arrive at holdHead
    rw [if_neg hxbranch] at holdHead
    injection holdHead with _ hpin
    have hpoint := congrFun hpin (x / 3)
    simpa [pin] using hpoint.symm
  have hrestore : pin u' x = u := by
    unfold u'
    exact pin_other_then_restore (hpx.symm.trans hpq) hualigned
  have hforward := run_grooved_passages w u p x q path
    hlinked hgrooved hfinal
  have hqArrive : arrive u q = (p, u') := by
    simp [arrive, hqbranch, hpqStem, u']
  have hqStep : stepN w 1 (q, u) = some (outside, u') := by
    simp [stepN, step, hqArrive, hmouth]
  have hfirstLen : path.length + 2 =
      ((p, x) :: path).length + 1 := by simp
  have hfirst : stepN w (path.length + 2) (p, u) =
      some (outside, u') := by
    rw [hfirstLen, stepN_add, hforward]
    simp only [Option.bind_some]
    exact hqStep

  have hqSelected : u' (p / 3) = bval q := by
    unfold u' pin
    rw [if_pos (by omega)]
  have hqBranch : branchPort (p / 3) (u' (p / 3)) = q := by
    rw [hqSelected]
    have hrecover := branchPort_bval hqbranch
    rw [hpq]
    exact hrecover
  have hpArrive : arrive u' p = (q, u') := by
    simp [arrive, hpstem, hqBranch]
  have hqBack : w.link q = some (lastPassageExit x path) :=
    w.symm _ _ hfinal
  have henterBack : stepN w 1 (p, u') =
      some (lastPassageExit x path, u') := by
    simp [stepN, step, hpArrive, hqBack]

  have hpathGroovedU' : PassagesGrooved u' path := by
    unfold u'
    exact grooved_after_pin_other
      (fun passage hp => hgrooved passage (List.mem_cons_of_mem _ hp))
      hpathForeign

  have hfinishBack :
      stepN w (path.length + 1)
        (lastPassageExit x path, u') = some (outside, u) := by
    cases path with
    | nil =>
        have hxArrive : arrive u' x = (p, u) := by
          simp [arrive, hxbranch, hpxStem, hrestore]
        simp [stepN, step, lastPassageExit, hxArrive, hmouth]
    | cons passage rest =>
        rcases passage with ⟨r, y⟩
        have hxr : w.link x = some r := hlinked.1
        have hrx : w.link r = some x := w.symm _ _ hxr
        have hpathLinked : LinkedPassages w ((r, y) :: rest) := hlinked.2
        have hbackPath := retrace_linked_passages_option w u' r y rest
          hpathLinked hpathGroovedU'
        rw [hrx] at hbackPath
        have hxArrive : arrive u' x = (p, u) := by
          simp [arrive, hxbranch, hpxStem, hrestore]
        have hxStep : stepN w 1 (x, u') = some (outside, u) := by
          simp [stepN, step, hxArrive, hmouth]
        have hbackPath' :
            stepN w ((r, y) :: rest).length
              (lastPassageExit x ((r, y) :: rest), u') = some (x, u') := by
          simpa [lastPassageExit] using hbackPath
        rw [stepN_add, hbackPath']
        simp only [Option.bind_some]
        exact hxStep
  have hsecond : stepN w (path.length + 2) (p, u') =
      some (outside, u) := by
    have hlen : path.length + 2 = 1 + (path.length + 1) := by omega
    rw [hlen, stepN_add, henterBack]
    simp only [Option.bind_some]
    exact hfinishBack
  exact ⟨hfirst, hsecond⟩

theorem stem_lobe_isReflector_foreign
    (w : Wiring) {p x q outside : Nat}
    (path : List Passage)
    (hpstem : p % 3 = 0)
    (hxbranch : x % 3 ≠ 0) (hqbranch : q % 3 ≠ 0)
    (hpx : p / 3 = x / 3) (hpq : p / 3 = q / 3)
    (hxq : x ≠ q)
    (hpathForeign : ∀ passage ∈ path,
      passageSwitch passage ≠ p / 3)
    (hlinked : LinkedPassages w ((p, x) :: path))
    (hfinal : w.link (lastPassageExit x path) = some q)
    (hmouth : w.link p = some outside) :
    IsReflector w p outside (path.length + 2)
      (fun u => PassagesGrooved u path)
      (fun u => flipAt u (p / 3)) := by
  have hxqsw : x / 3 = q / 3 := hpx.symm.trans hpq
  have hopp : bval q = !(bval x) :=
    branch_values_opposite hxbranch hqbranch hxqsw hxq
  intro state hpathGrooved
  let base := pin state x
  have hbaseAligned : base (x / 3) = bval x := by
    unfold base pin
    rw [if_pos rfl]
  have hbasePinX : pin base x = base :=
    pin_of_agrees hbaseAligned
  have hbaseHead : arrive base x = (p, base) := by
    have hstem : 3 * (x / 3) = p := by omega
    simp [arrive, hxbranch, hstem, hbasePinX]
  have hbasePathGrooved : PassagesGrooved base path := by
    unfold base
    apply grooved_after_pin_other hpathGrooved
    intro passage hp
    have hne := hpathForeign passage hp
    rw [← hpx]
    exact hne
  have hbaseGrooved : PassagesGrooved base ((p, x) :: path) := by
    intro passage hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hbaseHead
    · exact hbasePathGrooved passage htail
  have hpairs := stem_lobe_two_state_reflector_foreign w path
    hpstem hxbranch hqbranch hpx hpq
    (by
      intro passage hp hEq
      exact hpathForeign passage hp (hEq.trans hpq.symm))
    hlinked hbaseGrooved hfinal hmouth
  dsimp only at hpairs
  by_cases hsx : state (x / 3) = bval x
  · have hbaseEq : base = state := by
      unfold base
      exact pin_of_agrees hsx
    have hflipEq : pin base q = flipAt state (p / 3) := by
      rw [hbaseEq]
      apply pin_eq_flipAt
      · exact hpq.symm
      · have hsxp : state (p / 3) = bval x := by
          rw [hpx]
          exact hsx
        rw [hsxp]
        exact hopp
    have hflipState : pin state q = flipAt state (p / 3) := by
      exact (congrArg (fun z => pin z q) hbaseEq.symm).trans hflipEq
    constructor
    · have hstep := hpairs.1
      rw [hbaseEq, hflipState] at hstep
      exact hstep
    · change PassagesGrooved (flipAt state (p / 3)) path
      rw [← hflipState]
      apply grooved_after_pin_other hpathGrooved
      intro passage hp
      have hne := hpathForeign passage hp
      rw [← hpq]
      exact hne
  · have hsq : state (q / 3) = bval q := by
      have hstateOpp : state (x / 3) = !(bval x) := by
        cases hs : state (x / 3) <;> cases hb : bval x <;>
          simp_all
      rw [← hxqsw, hstateOpp]
      exact hopp.symm
    have hstateRestore : pin base q = state := by
      unfold base
      exact pin_other_then_restore hxqsw.symm hsq
    have hbaseFlip : base = flipAt state (p / 3) := by
      unfold base
      apply pin_eq_flipAt
      · exact hpx.symm
      · have : bval x = !(state (p / 3)) := by
          have hstateP : state (p / 3) = bval q := by
            rw [hpq]
            exact hsq
          rw [hstateP]
          cases hb : bval x <;> simp_all
        exact this
    constructor
    · have hstep := hpairs.2
      rw [hstateRestore, hbaseFlip] at hstep
      exact hstep
    · change PassagesGrooved (flipAt state (p / 3)) path
      rw [← hbaseFlip]
      exact hbasePathGrooved

/-- The switch-simple form of `stem_lobe_isReflector_foreign`. -/
theorem stem_lobe_isReflector
    (w : Wiring) {p x q outside : Nat}
    (path : List Passage)
    (hpstem : p % 3 = 0)
    (hxbranch : x % 3 ≠ 0) (hqbranch : q % 3 ≠ 0)
    (hpx : p / 3 = x / 3) (hpq : p / 3 = q / 3)
    (hxq : x ≠ q)
    (hsimple : SwitchSimple ((p, x) :: path))
    (hlinked : LinkedPassages w ((p, x) :: path))
    (hfinal : w.link (lastPassageExit x path) = some q)
    (hmouth : w.link p = some outside) :
    IsReflector w p outside (path.length + 2)
      (fun u => PassagesGrooved u path)
      (fun u => flipAt u (p / 3)) := by
  have hpathForeign : ∀ passage ∈ path,
      passageSwitch passage ≠ p / 3 := by
    unfold SwitchSimple at hsimple
    simp only [List.map_cons, List.nodup_cons] at hsimple
    intro passage hp hEq
    apply hsimple.1
    apply List.mem_map.mpr
    exact ⟨passage, hp, hEq⟩
  exact stem_lobe_isReflector_foreign w path
    hpstem hxbranch hqbranch hpx hpq hxq hpathForeign
    hlinked hfinal hmouth

/-- Extract the universal nondegenerate lobe reflector directly from a
crossed first-revisit excursion.  The stem/branch orientation is not assumed:
it follows from the two recorded passages and `x ≠ q`. -/
theorem crossed_excursion_core_reflector
    (w : Wiring) {p x q outside : Nat} {u₀ u v : Tongues}
    {path : List Passage}
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple ((p, x) :: path))
    (hrepeat : arrive u q = (p, v))
    (hxq : x ≠ q)
    (hmouth : w.link p = some outside) :
    IsReflector w p outside (path.length + 2)
      (fun state => PassagesGrooved state path)
      (fun state => flipAt state (p / 3)) := by
  obtain ⟨oldAfter, hold⟩ := hexcursion.head_arrive.2
  have hpx : p / 3 = x / 3 := by
    have hs := arrive_exit_switch u₀ p
    rw [hold] at hs
    exact hs.symm
  have hpq : p / 3 = q / 3 := by
    have hs := arrive_exit_switch u q
    rw [hrepeat] at hs
    exact hs
  have holdStem := arrive_stem_endpoint u₀ p
  rw [hold] at holdStem
  have hnewStem := arrive_stem_endpoint u q
  rw [hrepeat] at hnewStem
  have hpstem : p % 3 = 0 := by
    by_cases hp : p % 3 = 0
    · exact hp
    · exfalso
      have hpne : p ≠ 3 * (p / 3) := by omega
      rcases holdStem with hpOld | hxStem
      · exact hpne hpOld
      · rcases hnewStem with hqStem | hpNew
        · apply hxq
          omega
        · apply hpne
          omega
  have holdNe : x ≠ p := by
    have hn := arrive_exit_ne u₀ p
    rw [hold] at hn
    exact hn
  have hnewNe : p ≠ q := by
    have hn := arrive_exit_ne u q
    rw [hrepeat] at hn
    exact hn
  have hxbranch : x % 3 ≠ 0 := by
    intro hx
    apply holdNe
    omega
  have hqbranch : q % 3 ≠ 0 := by
    intro hq
    apply hnewNe
    omega
  exact stem_lobe_isReflector w path hpstem hxbranch hqbranch
    hpx hpq hxq hsimple hexcursion.linked hexcursion.last_link hmouth

/-- If a switch-simple excursion returns at exactly its old exit port, its
interior path is empty; the only possibility allowed by the raw `Wiring`
model is a self-linked physical edge. -/
theorem same_exit_excursion_path_nil
    {w : Wiring} {p x : Nat} {u₀ u : Tongues} {path : List Passage}
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (x, u))
    (hsimple : SwitchSimple ((p, x) :: path)) :
    path = [] := by
  cases path with
  | nil => rfl
  | cons passage rest =>
      rcases passage with ⟨r, y⟩
      exfalso
      have hlinked := hexcursion.linked
      have hxr : w.link x = some r := hlinked.1
      have hfinal : w.link (lastPassageExit y rest) = some x := by
        simpa [lastPassageExit] using hexcursion.last_link
      have hxlast : w.link x = some (lastPassageExit y rest) :=
        w.symm _ _ hfinal
      have hrequal : r = lastPassageExit y rest := by
        rw [hxr] at hxlast
        injection hxlast
      have htailSimple : SwitchSimple ((r, y) :: rest) := by
        unfold SwitchSimple at hsimple ⊢
        simp only [List.map_cons, List.nodup_cons] at hsimple ⊢
        exact hsimple.2
      cases hexcursion with
      | @cons _ _ q _ v _ _ harrive hlink tail =>
          cases tail with
          | cons harrive' hlink' restTrace =>
              have hne := (PhysicalTrace.cons harrive' hlink'
                restTrace).simple_last_exit_ne_first_entry htailSimple
              exact hne hrequal.symm

/-- A grooved passage whose exit edge is self-linked is an identity
reflector: it traverses the switch out and immediately back, then leaves over
the mouth edge. -/
theorem self_edge_groove_isReflector
    (w : Wiring) {p x outside : Nat}
    (hself : w.link x = some x) (hmouth : w.link p = some outside) :
    IsReflector w p outside 2
      (fun state => arrive state x = (p, state))
      (fun state => state) := by
  intro state hgroove
  have hforward := groove_forward hgroove
  have hone : stepN w 1 (p, state) = some (x, state) := by
    simp [stepN, step, hforward, hself]
  have htwo : stepN w 1 (x, state) = some (outside, state) := by
    simp [stepN, step, hgroove, hmouth]
  constructor
  · rw [show 2 = 1 + 1 by omega, stepN_add, hone]
    simp only [Option.bind_some]
    exact htwo
  · exact hgroove

/-- Sandwich a reflector behind a nonempty grooved runway.  The train walks
the runway forward, uses the core reflector, then retraces the runway and
emerges across the edge preceding `g`. -/
theorem sandwich_nonempty_reflector
    (w : Wiring) {g a p e k : Nat} {rest : List Passage}
    {S : Tongues → Prop} {τ : Tongues → Tongues}
    (hlinked : LinkedPassages w ((g, a) :: rest))
    (hfinal : w.link (lastPassageExit a rest) = some p)
    (hentry : w.link e = some g)
    (hcore : IsReflector w p (lastPassageExit a rest) k S τ)
    (hpreserve : ∀ u, PassagesGrooved u ((g, a) :: rest) →
      PassagesGrooved (τ u) ((g, a) :: rest)) :
    IsReflector w g e
      (((g, a) :: rest).length + k + ((g, a) :: rest).length)
      (fun u => PassagesGrooved u ((g, a) :: rest) ∧ S u) τ := by
  intro u hu
  have hforward := run_grooved_passages w u g a p rest
    hlinked hu.1 hfinal
  obtain ⟨hreflect, hSnext⟩ := hcore u hu.2
  have hgroovedNext := hpreserve u hu.1
  have hback := retrace_linked_passages w (τ u) g a e rest
    hlinked hgroovedNext hentry
  have hrun : (((g, a) :: rest).length + k +
      ((g, a) :: rest).length) =
      ((g, a) :: rest).length +
        (k + ((g, a) :: rest).length) := by omega
  constructor
  · rw [hrun, stepN_add, hforward]
    simp only [Option.bind_some]
    rw [stepN_add, hreflect]
    simp only [Option.bind_some]
    exact hback
  · exact ⟨hgroovedNext, hSnext⟩

/-- A nondegenerate crossed first revisit, together with the simple runway
before it, is a complete `flipAt` reflector from one side of the runway's
starting edge to the other.  The invariant is stated explicitly as the
grooves on the runway and candy interior. -/
theorem crossed_revisit_full_reflector
    (w : Wiring) {start : Nat × Tongues}
    {runway path : List Passage}
    {p x q e : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hrepeat : arrive u q = (p, v))
    (hxq : x ≠ q)
    (hentry : w.link e = some start.1) :
    IsReflector w start.1 e
      (2 * runway.length + path.length + 2)
      (fun state =>
        PassagesGrooved state runway ∧ PassagesGrooved state path)
      (fun state => flipAt state (p / 3)) := by
  have hsimpleExcursion : SwitchSimple ((p, x) :: path) := by
    unfold SwitchSimple at hsimple ⊢
    simp only [List.map_append] at hsimple
    exact (List.nodup_append.mp hsimple).2.1
  unfold SwitchSimple at hsimple
  simp only [List.map_append, List.map_cons] at hsimple
  have hparts := List.nodup_append.mp hsimple
  have hrunwayForeign : ∀ passage ∈ runway,
      passageSwitch passage ≠ p / 3 := by
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (p / 3)
      (by simp [passageSwitch])
    exact hne hEq
  cases runway with
  | nil =>
      cases hrunway
      have hmouth : w.link p = some e := w.symm _ _ hentry
      have hcore := crossed_excursion_core_reflector w hexcursion
        hsimpleExcursion hrepeat hxq hmouth
      intro state hs
      obtain ⟨hstep, hnext⟩ := hcore state hs.2
      constructor
      · simpa using hstep
      · exact ⟨(by
          intro passage hp
          cases hp), hnext⟩
  | cons passage rest =>
      rcases passage with ⟨g, a⟩
      have hstart : start.1 = g := hrunway.head_arrive.1
      have hlast : w.link (lastPassageExit a rest) = some p :=
        hrunway.last_link
      have hmouth : w.link p = some (lastPassageExit a rest) :=
        w.symm _ _ hlast
      have hcore := crossed_excursion_core_reflector w hexcursion
        hsimpleExcursion hrepeat hxq hmouth
      have hpreserve : ∀ state,
          PassagesGrooved state ((g, a) :: rest) →
          PassagesGrooved (flipAt state (p / 3)) ((g, a) :: rest) := by
        intro state hg
        apply grooved_after_flip_other hg
        intro pathPassage hp
        exact hrunwayForeign pathPassage hp
      have hsandwich := sandwich_nonempty_reflector w
        hrunway.linked hlast
        (by simpa [hstart] using hentry)
        hcore hpreserve
      have hlen :
          (((g, a) :: rest).length + (path.length + 2) +
              ((g, a) :: rest).length) =
          2 * ((g, a) :: rest).length + path.length + 2 := by omega
      rw [hlen] at hsandwich
      simpa only [hstart] using hsandwich


/-- Two opposite-facing exact reflectors with commuting involutive state maps
have a genuine four-corner (at most) Gray orbit. -/
theorem paired_reflectors_period
    (w : Wiring) {gA gB kA kB : Nat}
    {SA SB : Tongues → Prop} {τA τB : Tongues → Tongues}
    (hA : IsReflector w gA gB kA SA τA)
    (hB : IsReflector w gB gA kB SB τB)
    (hA_pres_B : ∀ u, SB u → SB (τA u))
    (hB_pres_A : ∀ u, SA u → SA (τB u))
    (hcomm : ∀ u, τA (τB u) = τB (τA u))
    (hinvA : ∀ u, τA (τA u) = u)
    (hinvB : ∀ u, τB (τB u) = u)
    (u : Tongues) (hSA : SA u) (hSB : SB u) :
    stepN w (2 * (kA + kB)) (gA, u) = some (gA, u) := by
  obtain ⟨hAu, hSA1⟩ := hA u hSA
  have hSB1 : SB (τA u) := hA_pres_B u hSB
  obtain ⟨hBu, hSB2⟩ := hB (τA u) hSB1
  have hSA2 : SA (τB (τA u)) :=
    hB_pres_A (τA u) hSA1
  obtain ⟨hAu2, hSA3⟩ := hA (τB (τA u)) hSA2
  have hSB3 : SB (τA (τB (τA u))) :=
    hA_pres_B (τB (τA u)) hSB2
  obtain ⟨hBu2, _⟩ := hB (τA (τB (τA u))) hSB3
  have hrestore : τB (τA (τB (τA u))) = u := by
    rw [hcomm (τA u), hinvA, hinvB]
  have hhalf : kA + kB + (kA + kB) = 2 * (kA + kB) := by omega
  rw [← hhalf, stepN_add, stepN_add, hAu]
  simp only [Option.bind_some]
  rw [hBu]
  simp only [Option.bind_some]
  rw [stepN_add, hAu2]
  simp only [Option.bind_some]
  rw [hBu2, hrestore]

end GeneralN
