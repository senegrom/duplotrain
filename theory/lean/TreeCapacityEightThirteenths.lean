import TreeCapacityTwoThirds

/-!
# An eight-thirteenths bound from three reserved cells per component

After externally lobed leaves and degree-two router chains are removed, a
branching support component has at least three unreflected router cells.
For such a tree component the active-lobe count `a` and tree size `v` satisfy

    a + 3 ≤ v.

The exact static capacity remains `2^a * (v-1)`.  The convenient rational
estimate proved here is

    (2^a * (v-1))^13 ≤ 2^(8*(v+a)).

For a product of certified components this gives

    states^13 ≤ 2^(8*C),

hence exponential base `2^(8/13) ≈ 1.532`.  The missing structural theorem is
the canonical pruning of degree-zero, degree-one and degree-two router
components into bounded reflector tails.
-/

namespace Echo

/-- Thirteenth power as tenth times cube. -/
def treeThirteenth (x : Nat) : Nat := treeTenth x * treeCube x

private theorem treeThirteenth_mul (x y : Nat) :
    treeThirteenth (x*y) = treeThirteenth x * treeThirteenth y := by
  unfold treeThirteenth treeTenth treeFifth treeCube fourth
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Thirteenth power is monotone. -/
theorem treeThirteenth_mono {x y : Nat} (h : x ≤ y) :
    treeThirteenth x ≤ treeThirteenth y := by
  unfold treeThirteenth
  exact Nat.mul_le_mul (treeTenth_mono h) (treeCube_mono h)

private theorem treeThirteenth_two_pow (A : Nat) :
    treeThirteenth (2^A) = 2^(13*A) := by
  unfold treeThirteenth treeTenth treeFifth treeCube fourth
  simp only [← Nat.pow_add]
  congr 1
  omega

/-- From seven cells onward, increasing the marker size by one costs at most
three bits in thirteenth power. -/
private theorem marker_thirteenth_step
    {v : Nat} (hv : 7 ≤ v) :
    treeThirteenth v ≤ 8 * treeThirteenth (v-1) := by
  have hlin : 6*v ≤ 7*(v-1) := by omega
  have hp := treeThirteenth_mono hlin
  rw [treeThirteenth_mul, treeThirteenth_mul] at hp
  have hconst : treeThirteenth 7 ≤ 8 * treeThirteenth 6 := by
    decide
  have hscaled :
      treeThirteenth 6 * treeThirteenth v ≤
        treeThirteenth 6 * (8 * treeThirteenth (v-1)) := by
    calc
      treeThirteenth 6 * treeThirteenth v
          ≤ treeThirteenth 7 * treeThirteenth (v-1) := hp
      _ ≤ (8 * treeThirteenth 6) * treeThirteenth (v-1) :=
            Nat.mul_le_mul_right _ hconst
      _ = treeThirteenth 6 *
          (8 * treeThirteenth (v-1)) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hpos : 0 < treeThirteenth 6 := by decide
  exact Nat.le_of_mul_le_mul_left hscaled hpos

/-- Marker estimate from seven cells onward. -/
private theorem marker_thirteenth_seven_plus : ∀ d : Nat,
    treeThirteenth (6+d) ≤ 2^(3*(7+d)+15) := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      let v := 7+d
      have hv : 7 ≤ v := by
        dsimp [v]
        omega
      have hstep := marker_thirteenth_step hv
      have hold : treeThirteenth (v-1) ≤ 2^(3*v+15) := by
        have harg : v-1 = 6+d := by
          dsimp [v]
          omega
        have hexp : 3*v+15 = 3*(7+d)+15 := by
          dsimp [v]
        rw [harg, hexp]
        exact ih
      have h8 : 8 = 2^3 := by decide
      have hout : treeThirteenth v ≤ 2^(3*(v+1)+15) := by
        calc
          treeThirteenth v ≤ 8 * treeThirteenth (v-1) := hstep
          _ ≤ 8 * 2^(3*v+15) := Nat.mul_le_mul_left 8 hold
          _ = 2^(3*(v+1)+15) := by
                rw [h8, ← Nat.pow_add]
                congr 1
                omega
      have harg : 6+(d+1) = v := by
        dsimp [v]
        omega
      have hexp : 3*(7+(d+1))+15 = 3*(v+1)+15 := by
        dsimp [v]
        omega
      rw [harg, hexp]
      exact hout

/-- **Uniform thirteenth-power marker estimate.** -/
theorem tree_marker_thirteenth {v : Nat} (hv : 2 ≤ v) :
    treeThirteenth (v-1) ≤ 2^(3*v+15) := by
  obtain ⟨d, rfl⟩ : ∃ d, v = 2+d := ⟨v-2, by omega⟩
  cases d with
  | zero => decide
  | succ d =>
      cases d with
      | zero => decide
      | succ d =>
          cases d with
          | zero => decide
          | succ d =>
              cases d with
              | zero => decide
              | succ d =>
                  cases d with
                  | zero => decide
                  | succ d =>
                      simpa [Nat.add_assoc] using
                        marker_thirteenth_seven_plus d

/-- Component products inherit the marker estimate. -/
theorem treeCapacity_thirteenth
    (m : Machine) (e r0 : Nat → Nat)
    {times : Nat → Prop}
    (blocks : List (TreeBlockCert m e r0 times))
    (hsize : ∀ b ∈ blocks, b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ blocks, 2 ≤ b.cells.length) :
    treeThirteenth (treeCapacity m e r0 blocks) ≤
      2^(3 * treeCellCount m e r0 blocks + 15 * blocks.length) := by
  induction blocks with
  | nil =>
      simp [treeCapacity, treeCellCount, treeThirteenth,
        treeTenth, treeFifth, treeCube, fourth]
  | cons b rest ih =>
      have hbsize := hsize b List.mem_cons_self
      have hbmin := hmin b List.mem_cons_self
      have hbedge : b.edges.length = b.cells.length - 1 := by omega
      have hbcap : treeThirteenth b.edges.length ≤
          2^(3*b.cells.length+15) := by
        rw [hbedge]
        exact tree_marker_thirteenth hbmin
      have htail := ih
        (fun x hx => hsize x (List.mem_cons_of_mem _ hx))
        (fun x hx => hmin x (List.mem_cons_of_mem _ hx))
      unfold treeCapacity treeCellCount
      simp only [List.length_cons]
      calc
        treeThirteenth (b.edges.length * treeCapacity m e r0 rest)
            = treeThirteenth b.edges.length *
              treeThirteenth (treeCapacity m e r0 rest) :=
                treeThirteenth_mul _ _
        _ ≤ 2^(3*b.cells.length+15) *
              2^(3*treeCellCount m e r0 rest + 15*rest.length) :=
                Nat.mul_le_mul hbcap htail
        _ = 2^((3*b.cells.length+15) +
              (3*treeCellCount m e r0 rest + 15*rest.length)) :=
                (Nat.pow_add 2 _ _).symm
        _ = 2^(3*(b.cells.length + treeCellCount m e r0 rest) +
              15*(rest.length+1)) := by
                congr 1
                omega

/-- Arithmetic core of the `8/13` estimate. -/
theorem eight_thirteenths_reserved_bound
    (C L M A Q P : Nat)
    (hC : C = L + M)
    (hAL : A ≤ L)
    (hreserved : A + 3*Q ≤ M)
    (hP : treeThirteenth P ≤ 2^(3*M+15*Q)) :
    treeThirteenth (2^A * P) ≤ 2^(8*C) := by
  have hmul : treeThirteenth (2^A) * treeThirteenth P ≤
      2^(13*A) * 2^(3*M+15*Q) := by
    exact Nat.mul_le_mul
      (Nat.le_of_eq (treeThirteenth_two_pow A)) hP
  have hexp : 13*A + (3*M+15*Q) ≤ 8*C := by
    omega
  calc
    treeThirteenth (2^A * P) =
        treeThirteenth (2^A) * treeThirteenth P :=
          treeThirteenth_mul _ _
    _ ≤ 2^(13*A) * 2^(3*M+15*Q) := hmul
    _ = 2^(13*A + (3*M+15*Q)) :=
          (Nat.pow_add 2 _ _).symm
    _ ≤ 2^(8*C) := Nat.pow_le_pow_right (by omega) hexp

/-- **Certified mixed fixed-support bound with exponent `8/13`.** -/
theorem mixed_epoch_eight_thirteenths
    (m : Machine) (e r0 : Nat → Nat)
    {times : Nat → Prop}
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {I J : Nat} (hIJ : I ≤ J)
    (trees : List (TreeBlockCert m e r0 times))
    (lobes : List (SupportLobeForestEpoch m e r0 times))
    (fixed allCells ks : List Nat)
    (L : Nat)
    (htimes : ∀ k, I ≤ k → k ≤ J → times k)
    (hks : ∀ k ∈ ks, times k)
    (hwithin : ∀ k ∈ ks, I ≤ k ∧ k ≤ J)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfixed : ∀ i ∈ ks, ∀ j ∈ ks, ∀ c ∈ fixed,
      reg m e r0 i c = reg m e r0 j c)
    (hcover : ∀ c ∈ allCells,
      c ∈ treeCells m e r0 trees ∨
      c ∈ lobeForestCells m e r0 lobes ∨ c ∈ fixed)
    (hsize : ∀ b ∈ trees, b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ trees, 2 ≤ b.cells.length)
    (hC : allCells.length = L + treeCellCount m e r0 trees)
    (hAL : lobes.length ≤ L)
    (hreserved : lobes.length + 3*trees.length ≤
      treeCellCount m e r0 trees)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    treeThirteenth ks.length ≤ 2^(8*allCells.length) := by
  have hcount := mixed_epoch_count m e r0 hrun hr0 trees lobes
    fixed allCells ks hks hsupport hfixed hcover hnd
  have hcap := treeCapacity_thirteenth m e r0 trees hsize hmin
  have hmono : treeThirteenth ks.length ≤
      treeThirteenth (2^(lobes.length) * treeCapacity m e r0 trees) := by
    apply treeThirteenth_mono
    simpa [Nat.mul_comm] using hcount
  exact Nat.le_trans hmono
    (eight_thirteenths_reserved_bound allCells.length L
      (treeCellCount m e r0 trees) lobes.length trees.length
      (treeCapacity m e r0 trees)
      hC hAL hreserved hcap)

end Echo
