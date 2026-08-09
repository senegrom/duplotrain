import TreeCapacityTwoThirds

/-!
# A thirteen-twentieths bound from two reserved cells per component

For a tree component on `v` cells, the exact marker capacity is `v-1`.
The useful twentieth-power estimate is

    (v-1)^20 ≤ 2^(6*v + 14).

For `Q` tree components using `M` cells this multiplies to

    treeCapacity^20 ≤ 2^(6*M + 14*Q).

If `A` active lobe roots are assigned to those components and every variable
component has two further reserved cells, then

    A + 2*Q ≤ M.

Combining this with the `A` independent lobe bits gives

    states^20 ≤ 2^(13*C),

where `C` is the total represented cell count.  The resulting exponential
base is `2^(13/20) ≈ 1.56917`, improving the one-reserve `2^(2/3)` bound.
-/

namespace Echo

/-- Twentieth power, as a square of the existing tenth power. -/
def treeTwentieth (x : Nat) : Nat := treeTenth x * treeTenth x

private theorem treeTwentieth_mul (x y : Nat) :
    treeTwentieth (x*y) = treeTwentieth x * treeTwentieth y := by
  unfold treeTwentieth treeTenth treeFifth fourth
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Twentieth power is monotone. -/
theorem treeTwentieth_mono {x y : Nat} (h : x ≤ y) :
    treeTwentieth x ≤ treeTwentieth y := by
  unfold treeTwentieth
  exact Nat.mul_le_mul (treeTenth_mono h) (treeTenth_mono h)

private theorem treeTwentieth_two_pow (A : Nat) :
    treeTwentieth (2^A) = 2^(20*A) := by
  unfold treeTwentieth treeTenth treeFifth fourth
  simp only [← Nat.pow_add]
  congr 1
  omega

/-- From `v=6` onward, increasing the marker size by one costs at most six
bits in twentieth power. -/
private theorem marker_twentieth_step
    {v : Nat} (hv : 6 ≤ v) :
    treeTwentieth v ≤ 64 * treeTwentieth (v-1) := by
  have hlin : 5*v ≤ 6*(v-1) := by omega
  have hp := treeTwentieth_mono hlin
  rw [treeTwentieth_mul, treeTwentieth_mul] at hp
  have hconst : treeTwentieth 6 ≤ 64 * treeTwentieth 5 := by
    decide
  have hscaled :
      treeTwentieth 5 * treeTwentieth v ≤
        treeTwentieth 5 * (64 * treeTwentieth (v-1)) := by
    calc
      treeTwentieth 5 * treeTwentieth v
          ≤ treeTwentieth 6 * treeTwentieth (v-1) := hp
      _ ≤ (64 * treeTwentieth 5) * treeTwentieth (v-1) :=
            Nat.mul_le_mul_right _ hconst
      _ = treeTwentieth 5 *
          (64 * treeTwentieth (v-1)) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hpos : 0 < treeTwentieth 5 := by decide
  exact Nat.le_of_mul_le_mul_left hscaled hpos

/-- Marker estimate from six cells onward. -/
private theorem marker_twentieth_six_plus : ∀ d : Nat,
    treeTwentieth (5+d) ≤ 2^(6*(6+d)+14) := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      let v := 6+d
      have hv : 6 ≤ v := by
        dsimp [v]
        omega
      have hstep := marker_twentieth_step hv
      have hmul :
          64 * treeTwentieth (v-1) ≤
            64 * 2^(6*v+14) := by
        have hold : treeTwentieth (v-1) ≤ 2^(6*v+14) := by
          have hidx : v-1 = 5+d := by
            dsimp [v]
            omega
          have hexp : 6*v+14 = 6*(6+d)+14 := by
            dsimp [v]
          rw [hidx, hexp]
          exact ih
        exact Nat.mul_le_mul_left 64 hold
      have h64 : 64 = 2^6 := by decide
      have hout : treeTwentieth v ≤ 2^(6*(v+1)+14) := by
        calc
          treeTwentieth v ≤ 64 * treeTwentieth (v-1) := hstep
          _ ≤ 64 * 2^(6*v+14) := hmul
          _ = 2^(6*(v+1)+14) := by
                rw [h64, ← Nat.pow_add]
                congr 1
                omega
      have harg : 5+(d+1) = v := by
        dsimp [v]
        omega
      have hexp : 6*(6+(d+1))+14 = 6*(v+1)+14 := by
        dsimp [v]
        omega
      rw [harg, hexp]
      exact hout

/-- **Uniform twentieth-power marker estimate.** -/
theorem tree_marker_twentieth {v : Nat} (hv : 2 ≤ v) :
    treeTwentieth (v-1) ≤ 2^(6*v+14) := by
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
                  simpa [Nat.add_assoc] using
                    marker_twentieth_six_plus d

/-- Component products inherit the twentieth-power estimate. -/
theorem treeCapacity_twentieth
    (m : Machine) (e r0 : Nat → Nat)
    {times : Nat → Prop}
    (blocks : List (TreeBlockCert m e r0 times))
    (hsize : ∀ b ∈ blocks, b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ blocks, 2 ≤ b.cells.length) :
    treeTwentieth (treeCapacity m e r0 blocks) ≤
      2^(6 * treeCellCount m e r0 blocks + 14 * blocks.length) := by
  induction blocks with
  | nil =>
      simp [treeCapacity, treeCellCount, treeTwentieth,
        treeTenth, treeFifth, fourth]
  | cons b rest ih =>
      have hbsize := hsize b List.mem_cons_self
      have hbmin := hmin b List.mem_cons_self
      have hbedge : b.edges.length = b.cells.length - 1 := by omega
      have hbcap : treeTwentieth b.edges.length ≤
          2^(6*b.cells.length+14) := by
        rw [hbedge]
        exact tree_marker_twentieth hbmin
      have htail := ih
        (fun x hx => hsize x (List.mem_cons_of_mem _ hx))
        (fun x hx => hmin x (List.mem_cons_of_mem _ hx))
      unfold treeCapacity treeCellCount
      simp only [List.length_cons]
      calc
        treeTwentieth (b.edges.length * treeCapacity m e r0 rest)
            = treeTwentieth b.edges.length *
              treeTwentieth (treeCapacity m e r0 rest) :=
                treeTwentieth_mul _ _
        _ ≤ 2^(6*b.cells.length+14) *
              2^(6*treeCellCount m e r0 rest + 14*rest.length) :=
                Nat.mul_le_mul hbcap htail
        _ = 2^((6*b.cells.length+14) +
              (6*treeCellCount m e r0 rest + 14*rest.length)) :=
                (Nat.pow_add 2 _ _).symm
        _ = 2^(6*(b.cells.length + treeCellCount m e r0 rest) +
              14*(rest.length+1)) := by
                congr 1
                omega

/-- Arithmetic core of the `13/20` estimate. -/
theorem thirteen_twentieths_reserved_bound
    (C L M A Q P : Nat)
    (hC : C = L + M)
    (hAL : A ≤ L)
    (hreserved : A + 2*Q ≤ M)
    (hP : treeTwentieth P ≤ 2^(6*M+14*Q)) :
    treeTwentieth (2^A * P) ≤ 2^(13*C) := by
  have hmul : treeTwentieth (2^A) * treeTwentieth P ≤
      2^(20*A) * 2^(6*M+14*Q) := by
    exact Nat.mul_le_mul
      (Nat.le_of_eq (treeTwentieth_two_pow A)) hP
  have hexp : 20*A + (6*M+14*Q) ≤ 13*C := by
    omega
  calc
    treeTwentieth (2^A * P) =
        treeTwentieth (2^A) * treeTwentieth P :=
          treeTwentieth_mul _ _
    _ ≤ 2^(20*A) * 2^(6*M+14*Q) := hmul
    _ = 2^(20*A + (6*M+14*Q)) :=
          (Nat.pow_add 2 _ _).symm
    _ ≤ 2^(13*C) := Nat.pow_le_pow_right (by omega) hexp

/-- **Certified mixed fixed-support bound with exponent `13/20`.**

The extra structural input is `hreserved`: after assigning every active lobe
root to its mouth-partner tree cell, each variable tree component still has
two unused cells.  `PairedRouterRoundtrip` is the local obstruction intended
to establish this before the first bounded reflector tail. -/
theorem mixed_epoch_thirteen_twentieths
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
    (hreserved : lobes.length + 2*trees.length ≤
      treeCellCount m e r0 trees)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    treeTwentieth ks.length ≤ 2^(13*allCells.length) := by
  have hcount := mixed_epoch_count m e r0 hrun hr0 trees lobes
    fixed allCells ks hks hsupport hfixed hcover hnd
  have hcap := treeCapacity_twentieth m e r0 trees hsize hmin
  have hmono : treeTwentieth ks.length ≤
      treeTwentieth (2^(lobes.length) * treeCapacity m e r0 trees) := by
    apply treeTwentieth_mono
    simpa [Nat.mul_comm] using hcount
  exact Nat.le_trans hmono
    (thirteen_twentieths_reserved_bound allCells.length L
      (treeCellCount m e r0 trees) lobes.length trees.length
      (treeCapacity m e r0 trees)
      hC hAL hreserved hcap)

end Echo
