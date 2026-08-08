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

/-- **Arbitrary simple lobe = two-state reflector.**

`p` is the stem/mouth, `x` and `q` are its two candy-side branches, and
`path` is the simple grooved path from the edge at `x` to the edge at `q`.
The stem edge leads to `outside`.  One reflection changes `u` to `pin u q`;
the next restores `u`, with the same exact travel time. -/
theorem stem_lobe_two_state_reflector
    (w : Wiring) {p x q outside : Nat} {u : Tongues}
    (path : List Passage)
    (hpstem : p % 3 = 0)
    (hxbranch : x % 3 ≠ 0) (hqbranch : q % 3 ≠ 0)
    (hpx : p / 3 = x / 3) (hpq : p / 3 = q / 3)
    (hsimple : SwitchSimple ((p, x) :: path))
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

  unfold SwitchSimple at hsimple
  simp only [List.map_cons, List.nodup_cons] at hsimple
  have hpathForeign : ∀ passage ∈ path,
      passageSwitch passage ≠ q / 3 := by
    intro passage hp hEq
    apply hsimple.1
    apply List.mem_map.mpr
    refine ⟨passage, hp, ?_⟩
    change passageSwitch passage = p / 3
    exact hEq.trans hpq.symm
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

end GeneralN
