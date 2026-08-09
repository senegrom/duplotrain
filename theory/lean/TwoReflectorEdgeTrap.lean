import LobeToggle
import Periodicity

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
    rcases hblock.2.1 with ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
  · right; left
    have hidx : j = k + 4*n + 2 := by omega
    rw [hidx]
    exact hblock.2.2.1
  · right; right; right; right
    have hidx : j = k + 4*n + 3 := by omega
    rw [hidx]
    exact hblock.2.2.2

/-! ## Register dynamics inside the trap

When the two lobe cells and the two support-endpoint cells are distinct, one
four-step block toggles exactly the two lobe registers.  The support endpoint
registers are reset to their fixed endpoint slots and every other register is
untouched.  This is the snapshot-level form needed by the state-law argument;
the earlier entry theorem alone does not state it.
-/

/-- The four cells occurring in a separated two-reflector trap are pairwise
distinct. -/
def ReflectorCellsDistinct (A X Y B : Nat) : Prop :=
  A ≠ X ∧ A ≠ Y ∧ A ≠ B ∧ X ≠ Y ∧ X ≠ B ∧ Y ≠ B

/-- **One-block register law.**  A four-step reflector block toggles the two
lobe registers, fixes the two support endpoint registers, and changes no
other register. -/
theorem two_reflector_edge_register_block
    (hrun : IsRun m e r0)
    {k x a b : Nat}
    (hx : e k = x)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (haPartner : m.cellOf x = m.star (m.cellOf a))
    (haOcc : Occupied m e r0 k a)
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hbPartner : m.cellOf (m.bar x) = m.star (m.cellOf b))
    (hbOcc : Occupied m e r0 (k+2) b)
    (hdist : ReflectorCellsDistinct
      (m.cellOf a) (m.cellOf x) (m.cellOf (m.bar x)) (m.cellOf b)) :
    reg m e r0 (k+4) (m.cellOf a) =
        m.bar (reg m e r0 k (m.cellOf a)) ∧
    reg m e r0 (k+4) (m.cellOf x) = x ∧
    reg m e r0 (k+4) (m.cellOf (m.bar x)) = m.bar x ∧
    reg m e r0 (k+4) (m.cellOf b) =
        m.bar (reg m e r0 k (m.cellOf b)) ∧
    ∀ C, C ≠ m.cellOf a → C ≠ m.cellOf x →
      C ≠ m.cellOf (m.bar x) → C ≠ m.cellOf b →
      reg m e r0 (k+4) C = reg m e r0 k C := by
  rcases hdist with ⟨hAX, hAY, hAB, hXY, hXB, hYB⟩
  have hblock := two_reflector_edge_one_block
    m e r0 hrun hx haLobe haPartner haOcc hbLobe hbPartner hbOcc
  have hAcell : m.cellOf (e (k+1)) = m.cellOf a := by
    rcases hblock.1 with h | h
    · rw [h]
    · rw [h, haLobe]
  have hYcell : m.cellOf (e (k+2)) = m.cellOf (m.bar x) := by
    rw [hblock.2.1]
  have hBcell : m.cellOf (e (k+3)) = m.cellOf b := by
    rcases hblock.2.2.1 with h | h
    · rw [h]
    · rw [h, hbLobe]
  have hXcell : m.cellOf (e (k+4)) = m.cellOf x := by
    rw [hblock.2.2.2]
  have htoggleA := occupied_lobe_partner_toggle
    m e r0 hrun haLobe (by rw [hx]; exact haPartner) haOcc
  have htoggleB := occupied_lobe_partner_toggle
    m e r0 hrun hbLobe (by rw [hblock.2.1]; exact hbPartner) hbOcc
  have hA : reg m e r0 (k+4) (m.cellOf a) =
      m.bar (reg m e r0 k (m.cellOf a)) := by
    calc
      reg m e r0 (k+4) (m.cellOf a) =
          reg m e r0 (k+3) (m.cellOf a) :=
        reg_skip m e r0 (by rw [hXcell]; exact hAX.symm)
      _ = reg m e r0 (k+2) (m.cellOf a) :=
        reg_skip m e r0 (by rw [hBcell]; exact hAB.symm)
      _ = reg m e r0 (k+1) (m.cellOf a) :=
        reg_skip m e r0 (by rw [hYcell]; exact hAY.symm)
      _ = m.bar (reg m e r0 k (m.cellOf a)) := htoggleA
  have hX : reg m e r0 (k+4) (m.cellOf x) = x := by
    rw [reg_write m e r0 hXcell, hblock.2.2.2]
  have hY : reg m e r0 (k+4) (m.cellOf (m.bar x)) = m.bar x := by
    calc
      reg m e r0 (k+4) (m.cellOf (m.bar x)) =
          reg m e r0 (k+3) (m.cellOf (m.bar x)) :=
        reg_skip m e r0 (by rw [hXcell]; exact hXY)
      _ = reg m e r0 (k+2) (m.cellOf (m.bar x)) :=
        reg_skip m e r0 (by rw [hBcell]; exact hYB.symm)
      _ = e (k+2) := reg_write m e r0 hYcell
      _ = m.bar x := hblock.2.1
  have hBbefore : reg m e r0 (k+2) (m.cellOf b) =
      reg m e r0 k (m.cellOf b) := by
    calc
      reg m e r0 (k+2) (m.cellOf b) =
          reg m e r0 (k+1) (m.cellOf b) :=
        reg_skip m e r0 (by rw [hYcell]; exact hYB)
      _ = reg m e r0 k (m.cellOf b) :=
        reg_skip m e r0 (by rw [hAcell]; exact hAB)
  have hB : reg m e r0 (k+4) (m.cellOf b) =
      m.bar (reg m e r0 k (m.cellOf b)) := by
    calc
      reg m e r0 (k+4) (m.cellOf b) =
          reg m e r0 (k+3) (m.cellOf b) :=
        reg_skip m e r0 (by rw [hXcell]; exact hXB)
      _ = m.bar (reg m e r0 (k+2) (m.cellOf b)) := htoggleB
      _ = m.bar (reg m e r0 k (m.cellOf b)) := by rw [hBbefore]
  refine ⟨hA, hX, hY, hB, ?_⟩
  intro C hCA hCX hCY hCB
  calc
    reg m e r0 (k+4) C = reg m e r0 (k+3) C :=
      reg_skip m e r0 (by rw [hXcell]; exact fun h => hCX h.symm)
    _ = reg m e r0 (k+2) C :=
      reg_skip m e r0 (by rw [hBcell]; exact fun h => hCB h.symm)
    _ = reg m e r0 (k+1) C :=
      reg_skip m e r0 (by rw [hYcell]; exact fun h => hCY h.symm)
    _ = reg m e r0 k C :=
      reg_skip m e r0 (by rw [hAcell]; exact fun h => hCA h.symm)

/-- After the first block has initialized both support endpoints, every two
further four-step blocks restore every register exactly. -/
theorem two_reflector_edge_register_period_eight
    (hrun : IsRun m e r0)
    {k x a b : Nat}
    (hx : e k = x)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (haPartner : m.cellOf x = m.star (m.cellOf a))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hbPartner : m.cellOf (m.bar x) = m.star (m.cellOf b))
    (haOcc : ∀ q, k ≤ q → Occupied m e r0 q a)
    (hbOcc : ∀ q, k ≤ q → Occupied m e r0 q b)
    (hdist : ReflectorCellsDistinct
      (m.cellOf a) (m.cellOf x) (m.cellOf (m.bar x)) (m.cellOf b)) :
    ∀ C, reg m e r0 (k+12) C = reg m e r0 (k+4) C := by
  have hx4 : e (k+4) = x := by
    have h := two_reflector_edge_start_period m e r0 hrun hx
      haLobe haPartner hbLobe hbPartner haOcc hbOcc 1
    simpa using h
  have hx8 : e (k+8) = x := by
    have h := two_reflector_edge_start_period m e r0 hrun hx
      haLobe haPartner hbLobe hbPartner haOcc hbOcc 2
    simpa using h
  have h0 := two_reflector_edge_register_block m e r0 hrun hx
    haLobe haPartner (haOcc k (Nat.le_refl _))
    hbLobe hbPartner (hbOcc (k+2) (by omega)) hdist
  have h1 := two_reflector_edge_register_block m e r0 hrun hx4
    haLobe haPartner (haOcc (k+4) (by omega))
    hbLobe hbPartner (hbOcc (k+6) (by omega)) hdist
  have h2 := two_reflector_edge_register_block m e r0 hrun hx8
    haLobe haPartner (haOcc (k+8) (by omega))
    hbLobe hbPartner (hbOcc (k+10) (by omega)) hdist
  intro C
  by_cases hCA : C = m.cellOf a
  · subst C
    calc
      reg m e r0 (k+12) (m.cellOf a) =
          m.bar (reg m e r0 (k+8) (m.cellOf a)) := by
        simpa [Nat.add_assoc] using h2.1
      _ = m.bar (m.bar (reg m e r0 (k+4) (m.cellOf a))) := by rw [h1.1]
      _ = reg m e r0 (k+4) (m.cellOf a) := m.bar_invol _
  · by_cases hCX : C = m.cellOf x
    · subst C
      calc
        reg m e r0 (k+12) (m.cellOf x) = x := by
          simpa [Nat.add_assoc] using h2.2.1
        _ = reg m e r0 (k+4) (m.cellOf x) := h0.2.1.symm
    · by_cases hCY : C = m.cellOf (m.bar x)
      · subst C
        calc
          reg m e r0 (k+12) (m.cellOf (m.bar x)) = m.bar x := by
            simpa [Nat.add_assoc] using h2.2.2.1
          _ = reg m e r0 (k+4) (m.cellOf (m.bar x)) := h0.2.2.1.symm
      · by_cases hCB : C = m.cellOf b
        · subst C
          calc
            reg m e r0 (k+12) (m.cellOf b) =
                m.bar (reg m e r0 (k+8) (m.cellOf b)) := by
              simpa [Nat.add_assoc] using h2.2.2.2.1
            _ = m.bar (m.bar (reg m e r0 (k+4) (m.cellOf b))) := by
              rw [h1.2.2.2.1]
            _ = reg m e r0 (k+4) (m.cellOf b) := m.bar_invol _
        · calc
            reg m e r0 (k+12) C = reg m e r0 (k+8) C := by
              simpa [Nat.add_assoc] using h2.2.2.2.2 C hCA hCX hCY hCB
            _ = reg m e r0 (k+4) C := h1.2.2.2.2 C hCA hCX hCY hCB

/-- **Exact state period.**  A separated persistent two-reflector edge trap
returns to its complete machine state after eight steps. -/
theorem two_reflector_edge_state_period_eight
    (hrun : IsRun m e r0)
    (cells : List Nat)
    {k x a b : Nat}
    (hx : e k = x)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (haPartner : m.cellOf x = m.star (m.cellOf a))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hbPartner : m.cellOf (m.bar x) = m.star (m.cellOf b))
    (haOcc : ∀ q, k ≤ q → Occupied m e r0 q a)
    (hbOcc : ∀ q, k ≤ q → Occupied m e r0 q b)
    (hdist : ReflectorCellsDistinct
      (m.cellOf a) (m.cellOf x) (m.cellOf (m.bar x)) (m.cellOf b)) :
    stateCode m e r0 cells (k+12) = stateCode m e r0 cells (k+4) := by
  have hx4 : e (k+4) = x := by
    have h := two_reflector_edge_start_period m e r0 hrun hx
      haLobe haPartner hbLobe hbPartner haOcc hbOcc 1
    simpa using h
  have hx12 : e (k+12) = x := by
    have h := two_reflector_edge_start_period m e r0 hrun hx
      haLobe haPartner hbLobe hbPartner haOcc hbOcc 3
    simpa using h
  have hregs := two_reflector_edge_register_period_eight m e r0 hrun hx
    haLobe haPartner hbLobe hbPartner haOcc hbOcc hdist
  unfold stateCode snap
  have hmap : cells.map (reg m e r0 (k+12)) =
      cells.map (reg m e r0 (k+4)) := by
    apply List.map_congr_left
    intro C _
    exact hregs C
  rw [hx12, hx4, hmap]

private theorem nodup_subset_length_reflector
    {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l S : List α},
      l.Nodup → (∀ x ∈ l, x ∈ S) → l.length ≤ S.length := by
  intro l
  induction l with
  | nil => intro S _ _; exact Nat.zero_le _
  | cons x t ih =>
      intro S hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ t, y ∈ S.erase x := by
        intro y hy
        have hyS : y ∈ S := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hih := ih hnd.2 hsub'
      have hlen : (S.erase x).length = S.length - 1 :=
        List.length_erase_of_mem hx
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- **Four-snapshot tail.**  Once the first block has initialized the support
endpoints, the separated two-reflector trap has at most four distinct
register snapshots.  The full machine state has period eight because the
train position distinguishes the two visits to each snapshot. -/
theorem two_reflector_edge_snapshots_four
    (hrun : IsRun m e r0)
    (cells : List Nat)
    (hcells : ∀ t, m.star (m.cellOf (e t)) ∈ cells)
    {k x a b : Nat}
    (hx : e k = x)
    (haLobe : m.cellOf (m.bar a) = m.cellOf a)
    (haPartner : m.cellOf x = m.star (m.cellOf a))
    (hbLobe : m.cellOf (m.bar b) = m.cellOf b)
    (hbPartner : m.cellOf (m.bar x) = m.star (m.cellOf b))
    (haOcc : ∀ q, k ≤ q → Occupied m e r0 q a)
    (hbOcc : ∀ q, k ≤ q → Occupied m e r0 q b)
    (hdist : ReflectorCellsDistinct
      (m.cellOf a) (m.cellOf x) (m.cellOf (m.bar x)) (m.cellOf b))
    (ks : List Nat)
    (hks : ∀ j ∈ ks, k+4 ≤ j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ 4 := by
  have hd := hdist
  rcases hd with ⟨hAX, hAY, hAB, hXY, hXB, hYB⟩
  have hx4 : e (k+4) = x := by
    have h := two_reflector_edge_start_period m e r0 hrun hx
      haLobe haPartner hbLobe hbPartner haOcc hbOcc 1
    simpa using h
  have hx8 : e (k+8) = x := by
    have h := two_reflector_edge_start_period m e r0 hrun hx
      haLobe haPartner hbLobe hbPartner haOcc hbOcc 2
    simpa using h
  have hx12 : e (k+12) = x := by
    have h := two_reflector_edge_start_period m e r0 hrun hx
      haLobe haPartner hbLobe hbPartner haOcc hbOcc 3
    simpa using h
  have h0 := two_reflector_edge_register_block m e r0 hrun hx
    haLobe haPartner (haOcc k (Nat.le_refl _))
    hbLobe hbPartner (hbOcc (k+2) (by omega)) hdist
  have h1 := two_reflector_edge_register_block m e r0 hrun hx4
    haLobe haPartner (haOcc (k+4) (by omega))
    hbLobe hbPartner (hbOcc (k+6) (by omega)) hdist
  have hb1 := two_reflector_edge_one_block m e r0 hrun hx4
    haLobe haPartner (haOcc (k+4) (by omega))
    hbLobe hbPartner (hbOcc (k+6) (by omega))
  have hb2 := two_reflector_edge_one_block m e r0 hrun hx8
    haLobe haPartner (haOcc (k+8) (by omega))
    hbLobe hbPartner (hbOcc (k+10) (by omega))
  have hA5 : m.cellOf (e (k+5)) = m.cellOf a := by
    rcases hb1.1 with h | h
    · simpa [Nat.add_assoc] using congrArg m.cellOf h
    · have hc := congrArg m.cellOf h
      rw [haLobe] at hc
      simpa [Nat.add_assoc] using hc
  have hY6 : m.cellOf (e (k+6)) = m.cellOf (m.bar x) := by
    have h := congrArg m.cellOf hb1.2.1
    simpa [Nat.add_assoc] using h
  have hB7 : m.cellOf (e (k+7)) = m.cellOf b := by
    rcases hb1.2.2.1 with h | h
    · simpa [Nat.add_assoc] using congrArg m.cellOf h
    · have hc := congrArg m.cellOf h
      rw [hbLobe] at hc
      simpa [Nat.add_assoc] using hc
  have hA9 : m.cellOf (e (k+9)) = m.cellOf a := by
    rcases hb2.1 with h | h
    · simpa [Nat.add_assoc] using congrArg m.cellOf h
    · have hc := congrArg m.cellOf h
      rw [haLobe] at hc
      simpa [Nat.add_assoc] using hc
  have hY10 : m.cellOf (e (k+10)) = m.cellOf (m.bar x) := by
    have h := congrArg m.cellOf hb2.2.1
    simpa [Nat.add_assoc] using h
  have hB11 : m.cellOf (e (k+11)) = m.cellOf b := by
    rcases hb2.2.2.1 with h | h
    · simpa [Nat.add_assoc] using congrArg m.cellOf h
    · have hc := congrArg m.cellOf h
      rw [hbLobe] at hc
      simpa [Nat.add_assoc] using hc
  have hun6 : ¬ ProductiveStep m e r0 (k+5) := by
    intro hp
    apply hp
    have hreg : reg m e r0 (k+5) (m.cellOf (m.bar x)) = m.bar x := by
      calc
        reg m e r0 (k+5) (m.cellOf (m.bar x)) =
            reg m e r0 (k+4) (m.cellOf (m.bar x)) :=
          reg_skip m e r0 (by rw [hA5]; exact hAY)
        _ = m.bar x := h0.2.2.1
    have he : e (k+6) = m.bar x := by
      simpa [Nat.add_assoc] using hb1.2.1
    rw [he, hreg]
  have hun8 : ¬ ProductiveStep m e r0 (k+7) := by
    intro hp
    apply hp
    have hreg : reg m e r0 (k+7) (m.cellOf x) = x := by
      calc
        reg m e r0 (k+7) (m.cellOf x) = reg m e r0 (k+6) (m.cellOf x) :=
          reg_skip m e r0 (by rw [hB7]; exact hXB.symm)
        _ = reg m e r0 (k+5) (m.cellOf x) :=
          reg_skip m e r0 (by rw [hY6]; exact hXY.symm)
        _ = reg m e r0 (k+4) (m.cellOf x) :=
          reg_skip m e r0 (by rw [hA5]; exact hAX)
        _ = x := h0.2.1
    rw [hx8, hreg]
  have hun10 : ¬ ProductiveStep m e r0 (k+9) := by
    intro hp
    apply hp
    have hreg : reg m e r0 (k+9) (m.cellOf (m.bar x)) = m.bar x := by
      calc
        reg m e r0 (k+9) (m.cellOf (m.bar x)) =
            reg m e r0 (k+8) (m.cellOf (m.bar x)) :=
          reg_skip m e r0 (by rw [hA9]; exact hAY)
        _ = m.bar x := h1.2.2.1
    have he : e (k+10) = m.bar x := by
      simpa [Nat.add_assoc] using hb2.2.1
    rw [he, hreg]
  have hun12 : ¬ ProductiveStep m e r0 (k+11) := by
    intro hp
    apply hp
    have hreg : reg m e r0 (k+11) (m.cellOf x) = x := by
      calc
        reg m e r0 (k+11) (m.cellOf x) = reg m e r0 (k+10) (m.cellOf x) :=
          reg_skip m e r0 (by rw [hB11]; exact hXB.symm)
        _ = reg m e r0 (k+9) (m.cellOf x) :=
          reg_skip m e r0 (by rw [hY10]; exact hXY.symm)
        _ = reg m e r0 (k+8) (m.cellOf x) :=
          reg_skip m e r0 (by rw [hA9]; exact hAX)
        _ = x := h1.2.1
    rw [hx12, hreg]
  have hs6 := snap_stall m e r0 cells hun6
  have hs8 := snap_stall m e r0 cells hun8
  have hs10 := snap_stall m e r0 cells hun10
  have hs12 := snap_stall m e r0 cells hun12
  have hperiodState := two_reflector_edge_state_period_eight
    m e r0 hrun cells hx haLobe haPartner hbLobe hbPartner
      haOcc hbOcc hdist
  have hperiodSnap : snap m e r0 cells (k+12) =
      snap m e r0 cells (k+4) := by
    have h := congrArg List.tail hperiodState
    simpa [stateCode] using h
  have hs11 : snap m e r0 cells (k+11) =
      snap m e r0 cells (k+4) := hs12.symm.trans hperiodSnap
  have hperiod : stateCode m e r0 cells (k+4) =
      stateCode m e r0 cells (k+12) := hperiodState.symm
  have hshift := state_replay m e r0 hrun cells hcells hperiod
  have hiter : ∀ q r,
      stateCode m e r0 cells (k+4+r) =
        stateCode m e r0 cells (k+4+8*q+r) := by
    intro q r
    induction q with
    | zero => simp
    | succ n ih =>
        calc
          stateCode m e r0 cells (k+4+r) =
              stateCode m e r0 cells (k+4+8*n+r) := ih
          _ = stateCode m e r0 cells (k+12+(8*n+r)) :=
            by simpa [Nat.add_assoc] using hshift (8*n+r)
          _ = stateCode m e r0 cells (k+4+8*(n+1)+r) := by
            congr 1
            omega
  let S := [snap m e r0 cells (k+4), snap m e r0 cells (k+5),
    snap m e r0 cells (k+7), snap m e r0 cells (k+9)]
  have hcover : ∀ j, k+4 ≤ j → snap m e r0 cells j ∈ S := by
    intro j hj
    let d := j - (k+4)
    let q := d / 8
    let r := d % 8
    have hd : d = 8*q+r := by
      dsimp [q, r]
      have h := Nat.mod_add_div d 8
      omega
    have hr : r < 8 := by
      dsimp [r]
      exact Nat.mod_lt _ (by omega)
    have hj : j = k+4+8*q+r := by
      dsimp [d] at hd
      omega
    have hcode := hiter q r
    have hsnap : snap m e r0 cells j =
        snap m e r0 cells (k+4+r) := by
      rw [hj]
      have h := congrArg List.tail hcode
      simpa [stateCode] using h.symm
    have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨
        r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
    dsimp [S]
    simp only [List.mem_cons]
    rcases hcases with hr0 | hr1 | hr2 | hr3 | hr4 | hr5 | hr6 | hr7
    · rw [hr0] at hsnap
      exact Or.inl (by simpa using hsnap)
    · rw [hr1] at hsnap
      exact Or.inr (Or.inl (by simpa using hsnap))
    · rw [hr2] at hsnap
      right; left
      exact hsnap.trans (by simpa [Nat.add_assoc] using hs6)
    · rw [hr3] at hsnap
      exact Or.inr (Or.inr (Or.inl (by simpa using hsnap)))
    · rw [hr4] at hsnap
      right; right; left
      exact hsnap.trans (by simpa [Nat.add_assoc] using hs8)
    · rw [hr5] at hsnap
      exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hsnap))))
    · rw [hr6] at hsnap
      right; right; right; left
      exact hsnap.trans (by simpa [Nat.add_assoc] using hs10)
    · rw [hr7] at hsnap
      left
      exact hsnap.trans (by simpa [Nat.add_assoc] using hs11)
  have hsub : ∀ v ∈ ks.map (snap m e r0 cells), v ∈ S := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    exact hcover j (hks j hj)
  have hle := nodup_subset_length_reflector hnd hsub
  simpa [S] using hle

end Echo
