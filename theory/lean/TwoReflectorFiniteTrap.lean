import TwoReflectorEdgeTrap

/-!
# Finite-interval form of the two-reflector trap

Fixed-support epochs are finite.  This version assumes the two lobe edges stay
occupied only through an endpoint `J` and concludes the six-slot trap only up
to `J`.  It is the form needed for component-load arguments.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The support-edge start recurs every four steps as long as the complete
four-step block remains inside the occupied interval. -/
theorem two_reflector_edge_start_period_until
    (hrun : IsRun m e r0)
    {k J x a b : Nat}
    (hx : e k = x)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (haPartner : m.cellOf x = m.star (m.cellOf a))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hbPartner : m.cellOf (m.bar x) = m.star (m.cellOf b))
    (haOcc : ∀ q, k ≤ q → q ≤ J → Occupied m e r0 q a)
    (hbOcc : ∀ q, k ≤ q → q ≤ J → Occupied m e r0 q b) :
    ∀ n, k + 4*n ≤ J → e (k + 4*n) = x := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa using hx
  | succ n ih =>
      intro hbound
      let q := k + 4*n
      have hqk : k ≤ q := by dsimp [q]; omega
      have hqJ : q ≤ J := by dsimp [q]; omega
      have hq2J : q+2 ≤ J := by dsimp [q]; omega
      have hprevBound : k + 4*n ≤ J := by omega
      have hstart0 : e (k + 4*n) = x := ih hprevBound
      have hstart : e q = x := by simpa [q] using hstart0
      have hblock := two_reflector_edge_one_block
        m e r0 hrun (k := q) (x := x) (a := a) (b := b)
        hstart haLobe haPartner (haOcc q hqk hqJ)
        hbLobe hbPartner (hbOcc (q+2) (by omega) hq2J)
      have hidx : k + 4*(n+1) = q+4 := by dsimp [q]; omega
      rw [hidx]
      exact hblock.2.2.2

/-- **Finite six-slot trap.** -/
theorem two_reflector_edge_entries_until
    (hrun : IsRun m e r0)
    {k J x a b : Nat}
    (hx : e k = x)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (haPartner : m.cellOf x = m.star (m.cellOf a))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hbPartner : m.cellOf (m.bar x) = m.star (m.cellOf b))
    (haOcc : ∀ q, k ≤ q → q ≤ J → Occupied m e r0 q a)
    (hbOcc : ∀ q, k ≤ q → q ≤ J → Occupied m e r0 q b) :
    ∀ j, k ≤ j → j ≤ J →
      e j = x ∨ e j = m.bar x ∨
      e j = a ∨ e j = m.bar a ∨
      e j = b ∨ e j = m.bar b := by
  intro j hjk hjJ
  let d := j-k
  let n := d/4
  let r := d%4
  have hd : j = k+d := by dsimp [d]; omega
  have hrlt : r < 4 := by
    dsimp [r]
    exact Nat.mod_lt d (by omega)
  have hdecomp : d = 4*n+r := by
    dsimp [n, r]
    have h := Nat.mod_add_div d 4
    omega
  let q := k + 4*n
  have hqk : k ≤ q := by dsimp [q]; omega
  have hqj : q ≤ j := by dsimp [q]; omega
  have hqJ : q ≤ J := Nat.le_trans hqj hjJ
  have hstart : e q = x :=
    two_reflector_edge_start_period_until
      m e r0 hrun hx haLobe haPartner hbLobe hbPartner
      haOcc hbOcc n hqJ
  have haCurrent :
      m.cellOf (e q) = m.star (m.cellOf a) := by
    rw [hstart]
    exact haPartner
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hcases with hr0 | hr1 | hr2 | hr3
  · left
    have hidx : j = q := by dsimp [q] at *; omega
    rw [hidx]
    exact hstart
  · right; right
    have hnext := occupied_lobe_partner_next_endpoint
      m e r0 hrun haLobe haCurrent (haOcc q hqk hqJ)
    have hidx : j = q+1 := by dsimp [q] at *; omega
    rw [hidx]
    rcases hnext with ha | hbara
    · exact Or.inl ha
    · exact Or.inr (Or.inl hbara)
  · right; left
    have hbounce := occupied_lobe_partner_bounce
      m e r0 hrun haLobe haCurrent (haOcc q hqk hqJ)
    have hidx : j = q+2 := by dsimp [q] at *; omega
    rw [hidx]
    calc
      e (q+2) = m.bar (e q) := hbounce.2
      _ = m.bar x := by rw [hstart]
  · right; right; right; right
    have hq2J : q+2 ≤ J := by dsimp [q] at *; omega
    have haBounce := occupied_lobe_partner_bounce
      m e r0 hrun haLobe haCurrent (haOcc q hqk hqJ)
    have htwo : e (q+2) = m.bar x := by
      calc
        e (q+2) = m.bar (e q) := haBounce.2
        _ = m.bar x := by rw [hstart]
    have hbCurrent :
        m.cellOf (e (q+2)) = m.star (m.cellOf b) := by
      rw [htwo]
      exact hbPartner
    have hbNext := occupied_lobe_partner_next_endpoint
      m e r0 hrun hbLobe hbCurrent
        (hbOcc (q+2) (by omega) hq2J)
    have hidx : j = q+3 := by dsimp [q] at *; omega
    rw [hidx]
    simpa [Nat.add_assoc] using hbNext

end Echo
