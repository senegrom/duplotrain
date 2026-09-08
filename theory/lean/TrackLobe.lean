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

/-- A selected branch meets its stem without changing the tongue vector. -/
theorem stem_branch_groove {stem arm : Nat} {state : Tongues}
    (hstem : stem % 3 = 0) (hbranch : arm % 3 ≠ 0)
    (hswitch : arm / 3 = stem / 3) (hselected : state (arm / 3) = bval arm) :
    arrive state arm = (stem, state) := by
  simp [arrive, hbranch, pin_of_agrees hselected, show 3 * (arm / 3) = stem by omega]

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
      arrive state last = (p, flipAt state (p / 3)) ∧
      (route = (p, x) :: path ∨ route = (p, q) :: reversePassages path) := by
  let base := pin state x
  have hselected : base (x / 3) = bval x := by simp [base, pin]
  have hbaseHead : arrive base x = (p, base) := by
    simp [arrive, hxbranch, pin_of_agrees hselected, show 3 * (x / 3) = p by omega]
  have hbasePath : PassagesGrooved base path := by
    apply hgrooved.transfer
    intro passage hp
    have hne : passageSwitch passage ≠ x / 3 := by simpa [← hpx] using hforeign passage hp
    simp [base, pin, hne]
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
    have hsw : x / 3 = q / 3 := hpx.symm.trans hpq
    have hpinpin : pin (pin base q) x = base := by
      funext j
      by_cases hj : j = x / 3 <;> simp [pin, hj, ← hsw, hselected]
    simp [arrive, hxbranch, hpinpin, show 3 * (x / 3) = p by omega]
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
      by simpa only [heq] using hbaseGrooved, by simpa only [heq] using hcrossed,
      Or.inl rfl⟩
  · exact ⟨(p, q) :: reversePassages path, x, by simp [reversePassages_length],
      by simpa only [heq] using hreverse, by simpa only [heq] using hreverseGrooved,
      by simpa only [heq, flipAt_flipAt] using hrestore, Or.inr rfl⟩

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
  obtain ⟨route, last, hlen, htrace, _, hcontact, _⟩ := stem_lobe_route w path
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
  have hpathForeign : ∀ passage ∈ path, passageSwitch passage ≠ p / 3 := by
    grind [SwitchSimple, passageSwitch]
  exact stem_lobe_isReflector_foreign w path
    hpstem hxbranch hqbranch hpx hpq hxq hpathForeign
    hlinked hfinal hmouth

/-- Two distinct arms meeting across an arrival force a stem mouth. -/
theorem crossed_arrivals_geometry {p x q : Nat} {a b c d : Tongues}
    (hold : arrive a p = (x, b)) (hnew : arrive c q = (p, d)) (hne : x ≠ q) :
    p % 3 = 0 ∧ x % 3 ≠ 0 ∧ q % 3 ≠ 0 ∧ p / 3 = x / 3 ∧ p / 3 = q / 3 := by
  grind [arrive, branchPort]

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
      cases hexcursion with
      | @cons _ _ next _ _ _ _ _ hlink tail =>
          have hlast := w.symm _ _ tail.last_link
          have hne := tail.simple_last_exit_ne_first_entry (List.nodup_cons.mp hsimple).2
          exact (hne ((Option.some.inj (hlink.symm.trans hlast)).symm.trans
            tail.head_arrive.1)).elim

/-- A grooved runway transports any core reflector. Empty and nonempty
runways share this interface, so each reflector construction needs only its
core law and preservation of the runway grooves. -/
theorem PhysicalTrace.sandwich_reflector
    {w : Wiring} {start : Nat × Tongues} {p e k : Nat} {mouthState : Tongues}
    {runway : List Passage} {S : Tongues → Prop} {τ : Tongues → Tongues}
    (hrunway : PhysicalTrace w start runway (p, mouthState))
    (hentry : w.link e = some start.1)
    (hcore : ∀ outside, w.link p = some outside → IsReflector w p outside k S τ)
    (hpreserve : ∀ u, PassagesGrooved u runway → PassagesGrooved (τ u) runway) :
    IsReflector w start.1 e (2 * runway.length + k)
      (fun u => PassagesGrooved u runway ∧ S u) τ := by
  cases runway with
  | nil =>
      cases hrunway
      intro u hu
      obtain ⟨hr, hs⟩ := hcore e (w.symm _ _ hentry) u hu.2
      exact ⟨by simpa using hr, hpreserve u hu.1, hs⟩
  | cons passage rest =>
      rcases passage with ⟨g, a⟩
      intro u hu
      have hg := hpreserve u hu.1
      obtain ⟨hr, hs⟩ := hcore _ (w.symm _ _ hrunway.last_link) u hu.2
      have hforward := (hrunway.replay_grooved u hu.1).sound
      have hback := (hrunway.reverse_grooved hg hentry (w.symm _ _ hrunway.last_link)).sound
      refine ⟨?_, hg, hs⟩
      rw [show 2 * ((g, a) :: rest).length + k =
        ((g, a) :: rest).length + (k + ((g, a) :: rest).length) by omega,
        stepN_add, hforward]
      simp only [Option.bind_some]
      rw [stepN_add, hr]
      simpa [reversePassages_length] using hback

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
  have hexcursionSimple : SwitchSimple ((p, x) :: path) := by
    grind [SwitchSimple]
  have hforeign : ∀ passage ∈ runway, passageSwitch passage ≠ p / 3 := by
    grind [SwitchSimple, passageSwitch]
  simpa only [Nat.add_assoc] using hrunway.sandwich_reflector hentry
    (fun _ hmouth => by
      obtain ⟨_, hold⟩ := hexcursion.head_arrive.2
      obtain ⟨hp, hx, hq, hpx, hpq⟩ := crossed_arrivals_geometry hold hrepeat hxq
      exact stem_lobe_isReflector w _ hp hx hq hpx hpq hxq hexcursionSimple
        hexcursion.linked hexcursion.last_link hmouth)
    (fun _ hg => grooved_after_flip_other hg hforeign)

end GeneralN
