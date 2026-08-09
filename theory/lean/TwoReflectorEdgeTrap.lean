import LobeToggle

/-!
# Two lobe reflectors across one support edge form a trap

Let `x` and `bar x` be the two endpoint slots of one occupied support edge.
Suppose the mouth partner of `cell x` carries an occupied lobe `a`, and the
mouth partner of `cell (bar x)` carries an occupied lobe `b`.  Entering `x`
then forces the pattern

    x,  a-or-bar-a,  bar x,  b-or-bar-b,  x, ...

The two lobe registers toggle, but the support-edge endpoints recur every four
steps.  As long as both lobe edges remain occupied, every later entry belongs
to the six displayed slots.  This is the non-adjacent-lobe generalisation of
the dogbone trap needed for component/lobe coupling.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- One four-step block between two lobe reflectors. -/
theorem two_reflector_edge_one_block
    (hrun : IsRun m e r0)
    {k x a b : Nat}
    (hx : e k = x)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (haPartner : m.cellOf x = m.star (m.cellOf a))
    (haOcc : Occupied m e r0 k a)
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hbPartner : m.cellOf (m.bar x) = m.star (m.cellOf b))
    (hbOcc : Occupied m e r0 (k+2) b) :
    (e (k+1) = a ∨ e (k+1) = m.bar a) ∧
      e (k+2) = m.bar x ∧
      (e (k+3) = b ∨ e (k+3) = m.bar b) ∧
      e (k+4) = x := by
  have haCurrent :
      m.cellOf (e k) = m.star (m.cellOf a) := by
    rw [hx]
    exact haPartner
  have haNext := occupied_lobe_partner_next_endpoint
    m e r0 hrun haLobe haCurrent haOcc
  have haBounce := occupied_lobe_partner_bounce
    m e r0 hrun haLobe haCurrent haOcc
  have htwo : e (k+2) = m.bar x := by
    calc
      e (k+2) = m.bar (e k) := haBounce.2
      _ = m.bar x := by rw [hx]
  have hbCurrent :
      m.cellOf (e (k+2)) = m.star (m.cellOf b) := by
    rw [htwo]
    exact hbPartner
  have hbNext := occupied_lobe_partner_next_endpoint
    m e r0 hrun hbLobe hbCurrent hbOcc
  have hbBounce := occupied_lobe_partner_bounce
    m e r0 hrun hbLobe hbCurrent hbOcc
  have hfour : e (k+4) = x := by
    calc
      e (k+4) = e ((k+2)+2) := by congr 1 <;> omega
      _ = m.bar (e (k+2)) := hbBounce.2
      _ = m.bar (m.bar x) := by rw [htwo]
      _ = x := m.bar_invol x
  refine ⟨haNext, htwo, ?_, hfour⟩
  simpa [Nat.add_assoc] using hbNext

/-- The support-edge entry `x` recurs every four steps. -/
theorem two_reflector_edge_start_period
    (hrun : IsRun m e r0)
    {k x a b : Nat}
    (hx : e k = x)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (haPartner : m.cellOf x = m.star (m.cellOf a))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hbPartner : m.cellOf (m.bar x) = m.star (m.cellOf b))
    (haOcc : ∀ q, k ≤ q → Occupied m e r0 q a)
    (hbOcc : ∀ q, k ≤ q → Occupied m e r0 q b) :
    ∀ n, e (k + 4*n) = x := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      let q := k + 4*n
      have hqk : k ≤ q := by dsimp [q]; omega
      have hblock := two_reflector_edge_one_block
        m e r0 hrun (k := q) (x := x) (a := a) (b := b)
        ih haLobe haPartner (haOcc q hqk)
        hbLobe hbPartner (hbOcc (q+2) (by omega))
      dsimp [q] at hblock ⊢
      have hidx : k + 4*(n+1) = k + 4*n + 4 := by omega
      rw [hidx]
      exact hblock.2.2.2

/-- Every four-step block has the same six-slot shape. -/
theorem two_reflector_edge_blocks
    (hrun : IsRun m e r0)
    {k x a b : Nat}
    (hx : e k = x)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (haPartner : m.cellOf x = m.star (m.cellOf a))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hbPartner : m.cellOf (m.bar x) = m.star (m.cellOf b))
    (haOcc : ∀ q, k ≤ q → Occupied m e r0 q a)
    (hbOcc : ∀ q, k ≤ q → Occupied m e r0 q b) :
    ∀ n,
      e (k + 4*n) = x ∧
      (e (k + 4*n + 1) = a ∨
        e (k + 4*n + 1) = m.bar a) ∧
      e (k + 4*n + 2) = m.bar x ∧
      (e (k + 4*n + 3) = b ∨
        e (k + 4*n + 3) = m.bar b) := by
  intro n
  have hstart := two_reflector_edge_start_period
    m e r0 hrun hx haLobe haPartner hbLobe hbPartner
    haOcc hbOcc n
  let q := k + 4*n
  have hqk : k ≤ q := by dsimp [q]; omega
  have hblock := two_reflector_edge_one_block
    m e r0 hrun (k := q) (x := x) (a := a) (b := b)
    hstart haLobe haPartner (haOcc q hqk)
    hbLobe hbPartner (hbOcc (q+2) (by omega))
  dsimp [q] at hblock
  exact ⟨hstart, hblock.1, hblock.2.1, hblock.2.2.1⟩

/-- **Six-slot trap.**  Every entry from `k` onward belongs to the support-edge
endpoints or one of the two lobe edges. -/
theorem two_reflector_edge_entries
    (hrun : IsRun m e r0)
    {k x a b : Nat}
    (hx : e k = x)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (haPartner : m.cellOf x = m.star (m.cellOf a))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hbPartner : m.cellOf (m.bar x) = m.star (m.cellOf b))
    (haOcc : ∀ q, k ≤ q → Occupied m e r0 q a)
    (hbOcc : ∀ q, k ≤ q → Occupied m e r0 q b) :
    ∀ j, k ≤ j →
      e j = x ∨ e j = m.bar x ∨
      e j = a ∨ e j = m.bar a ∨
      e j = b ∨ e j = m.bar b := by
  intro j hj
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
  have hblock := two_reflector_edge_blocks
    m e r0 hrun hx haLobe haPartner hbLobe hbPartner
    haOcc hbOcc n
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hcases with hr0 | hr1 | hr2 | hr3
  · left
    have hidx : j = k + 4*n := by omega
    rw [hidx]
    exact hblock.1
  · right; right
    have hidx : j = k + 4*n + 1 := by omega
    rw [hidx]
    rcases hblock.2.1 with ha | hbara
    · exact Or.inl ha
    · exact Or.inr (Or.inl hbara)
  · right; left
    have hidx : j = k + 4*n + 2 := by omega
    rw [hidx]
    exact hblock.2.2.1
  · right; right; right; right
    have hidx : j = k + 4*n + 3 := by omega
    rw [hidx]
    exact hblock.2.2.2

end Echo
