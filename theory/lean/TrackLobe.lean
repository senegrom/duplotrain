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
  by_cases hj : j = x / 3 <;> simp [pin, hj, ← hsw, haligned]

/-- Changing the mouth switch preserves every groove on a switch-disjoint
interior path. -/
theorem grooved_after_pin_other
    {u : Tongues} {q : Nat} {path : List Passage}
    (hgrooved : PassagesGrooved u path)
    (hforeign : ∀ passage ∈ path,
      passageSwitch passage ≠ q / 3) :
    PassagesGrooved (pin u q) path := by
  apply hgrooved.transfer
  intro passage hp
  simp [pin, hforeign passage hp]

/-- Flipping a switch preserves every groove on a switch-disjoint path. -/
theorem grooved_after_flip_other
    {u : Tongues} {k : Nat} {path : List Passage}
    (hgrooved : PassagesGrooved u path)
    (hforeign : ∀ passage ∈ path, passageSwitch passage ≠ k) :
    PassagesGrooved (flipAt u k) path := by
  apply hgrooved.transfer
  intro passage hp
  simp [flipAt, hforeign passage hp]

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
  by_cases hj : j = k <;> simp [pin, flipAt, hq, hj, hopposite]

/-- A one-coordinate difference between Boolean vectors is identity or a flip. -/
theorem tongues_eq_or_eq_flipAt_of_changes_only
    {u v : Tongues} {k : Nat}
    (hchanges : ∀ j, v j ≠ u j → j = k) :
    u = v ∨ u = flipAt v k := by
  by_cases hkey : u k = v k
  · left; funext j; by_cases hj : j = k <;> grind
  · right
    funext j
    by_cases hj : j = k
    · subst j
      cases hu : u k <;> cases hv : v k <;> simp_all [flipAt]
    · simp only [flipAt, if_neg hj]
      grind

/-- In either mouth orientation, a lobe follows one grooved route and then
flips its mouth on the final arrival. This single spatial certificate supplies
both endpoint reflection and every intermediate state. -/
theorem stem_lobe_route
    (w : Wiring) {p x q : Nat} (path : List Passage)
    (hpstem : p % 3 = 0)
    (hxbranch : x % 3 ≠ 0) (hqbranch : q % 3 ≠ 0)
    (hpx : p / 3 = x / 3) (hpq : p / 3 = q / 3) (hxq : x ≠ q)
    (hforeign : ∀ passage ∈ path, passageSwitch passage ≠ p / 3)
    (hlinked : LinkedPassages w ((p, x) :: path))
    (hfinal : w.link (lastPassageExit x path) = some q)
    (state : Tongues) (hgrooved : PassagesGrooved state path) :
    ∃ route last, route.length = path.length + 1 ∧
      PhysicalTrace w (p, state) route (last, state) ∧
      PassagesGrooved state route ∧
      arrive state last = (p, flipAt state (p / 3)) := by
  let base := pin state x
  have hselected : base (x / 3) = bval x := by simp [base, pin]
  have hbaseHead : arrive base x = (p, base) := by
    simp [arrive, hxbranch, pin_of_agrees hselected, show 3 * (x / 3) = p by omega]
  have hbasePath := grooved_after_pin_other (q := x) hgrooved
    (fun passage hp => by simpa [← hpx] using hforeign passage hp)
  have hbaseGrooved : PassagesGrooved base ((p, x) :: path) := by
    intro passage hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hbaseHead
    · exact hbasePath passage hp
  have hforward := physicalTrace_grooved_passages w base p x q path
    hlinked hbaseGrooved hfinal
  have hflip : pin base q = flipAt base (p / 3) :=
    pin_eq_flipAt hpq.symm (by
      rw [hpx, hselected]
      exact branch_values_opposite hxbranch hqbranch (hpx.symm.trans hpq) hxq)
  have hcrossed : arrive base q = (p, flipAt base (p / 3)) := by
    simp [arrive, hqbranch, hflip, show 3 * (q / 3) = p by omega]
  have hrestore : arrive (flipAt base (p / 3)) x = (p, base) := by
    rw [← hflip]
    simp [arrive, hxbranch, pin_other_then_restore (hpx.symm.trans hpq) hselected,
      show 3 * (x / 3) = p by omega]
  have hback : arrive (flipAt base (p / 3)) p = (q, flipAt base (p / 3)) := by
    simpa only [hcrossed] using arrive_back base q
  have hpathFlip := grooved_after_flip_other hbasePath hforeign
  have hreverse : PhysicalTrace w (p, flipAt base (p / 3))
      ((p, q) :: reversePassages path) (x, flipAt base (p / 3)) := by
    cases hforward with
    | cons _ hlink tail =>
        exact physicalTrace_contact_retraces_prefix tail hpathFlip hlink hback
  have hreverseGrooved : PassagesGrooved (flipAt base (p / 3))
      ((p, q) :: reversePassages path) := by
    intro passage hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact groove_forward hback
    · exact reversePassages_grooved hpathFlip passage hp
  have hphases : state = base ∨ state = flipAt base (p / 3) :=
    tongues_eq_or_eq_flipAt_of_changes_only (by
      intro j hj
      by_cases heq : j = x / 3
      · omega
      · exact (hj (by simp [base, pin, heq])).elim)
  rcases hphases with heq | heq
  · exact ⟨(p, x) :: path, q, by simp, by simpa only [heq] using hforward,
      by simpa only [heq] using hbaseGrooved, by simpa only [heq] using hcrossed⟩
  · exact ⟨(p, q) :: reversePassages path, x, by simp [reversePassages_length],
      by simpa only [heq] using hreverse, by simpa only [heq] using hreverseGrooved,
      by simpa only [heq, flipAt_flipAt] using hrestore⟩

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
  intro state hg
  obtain ⟨route, last, hlen, htrace, _, hcontact⟩ := stem_lobe_route w path
    hpstem hxbranch hqbranch hpx hpq hxq hpathForeign hlinked hfinal state hg
  refine ⟨?_, grooved_after_flip_other hg hpathForeign⟩
  have hr := (htrace.append
    (PhysicalTrace.cons hcontact hmouth (PhysicalTrace.nil _))).sound
  simpa [List.length_append, hlen] using hr

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


end GeneralN
