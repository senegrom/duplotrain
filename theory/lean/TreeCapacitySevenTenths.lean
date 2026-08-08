import MixedEpochBound

/-!
# Sharp component capacity and a seven-tenths epoch bound

The earlier component theorem used the convenient estimate

    (v - 1)^2 ≤ 2^v

for a tree component on `v` cells.  That loses exponential mass.  The exact
marker capacity is `v - 1`, and the optimal uniform rational estimate is

    (v - 1)^5 ≤ 2^(2*v).

It is sharp at `v = 5`, where a five-cell tree has four possible full-edge
markers.  Multiplying over tree components gives

    treeCapacity^5 ≤ 2^(2 * treeCells).

Combining this with one Boolean per varying lobe root and the existing
mouth-pair half-density theorem yields

    states^10 ≤ 2^(7 * cells),

that is, exponential base `2^(7/10)` rather than `2^(3/4)`.  This is the
strongest exponent obtainable from the present independent tree-marker plus
lobe-bit code: equality in the arithmetic is attained by five-cell tree
blocks paired with the same number of one-bit lobe coordinates.
-/

namespace Echo

/-- Fifth power, factored through the existing fourth-power definition. -/
def treeFifth (x : Nat) : Nat := fourth x * x

/-- Tenth power as a square of fifth powers. -/
def treeTenth (x : Nat) : Nat := treeFifth x * treeFifth x

private theorem treeFifth_mul (x y : Nat) :
    treeFifth (x * y) = treeFifth x * treeFifth y := by
  unfold treeFifth fourth
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem treeTenth_mul (x y : Nat) :
    treeTenth (x * y) = treeTenth x * treeTenth y := by
  unfold treeTenth
  rw [treeFifth_mul]
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Tenth power is monotone. -/
theorem treeTenth_mono {x y : Nat} (h : x ≤ y) :
    treeTenth x ≤ treeTenth y := by
  have h4 := fourth_mono h
  have h5 : treeFifth x ≤ treeFifth y := by
    unfold treeFifth
    exact Nat.mul_le_mul h4 h
  unfold treeTenth
  exact Nat.mul_le_mul h5 h5

private theorem treeTenth_two_pow (A : Nat) :
    treeTenth (2^A) =
      2^(A+A+A+A+A+A+A+A+A+A) := by
  unfold treeTenth treeFifth fourth
  simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- The standard sharp square estimate from four onward. -/
private theorem sharp_square_four_plus : ∀ d : Nat,
    (4+d)*(4+d) ≤ 2^(4+d) := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      let n := 4+d
      have hn : 3 ≤ n := by omega
      have hlin : 2*n + 1 ≤ n*n := by
        have h1 : 2*n + 1 ≤ 3*n := by omega
        have h2 : 3*n ≤ n*n := Nat.mul_le_mul_right n hn
        exact Nat.le_trans h1 h2
      have hexpand : (n+1)*(n+1) = n*n + (2*n+1) := by
        simp [Nat.add_mul, Nat.mul_add, Nat.two_mul]
        omega
      have hsquare : (n+1)*(n+1) ≤ 2*(n*n) := by
        rw [hexpand]
        have h := Nat.add_le_add_left hlin (n*n)
        simpa [Nat.two_mul] using h
      have hdouble : 2*(n*n) ≤ 2*(2^n) :=
        Nat.mul_le_mul_left 2 ih
      have hp : 2*(2^n) = 2^(n+1) := by
        rw [Nat.pow_add_one]
        exact Nat.mul_comm _ _
      have hnext : (n+1)*(n+1) ≤ 2^(n+1) := by
        rw [← hp]
        exact Nat.le_trans hsquare hdouble
      simpa [n, Nat.add_assoc] using hnext

/-- The companion cube estimate `n^3 ≤ 2^(n+2)` from `n = 4` onward. -/
private theorem sharp_cube_four_plus : ∀ d : Nat,
    (4+d)*(4+d)*(4+d) ≤ 2^((4+d)+2) := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      let n := 4+d
      have hn : 4 ≤ n := by omega
      have hsmall : 3*n + 1 ≤ n*n := by
        have h1 : 3*n + 1 ≤ 4*n := by omega
        have h2 : 4*n ≤ n*n := Nat.mul_le_mul_right n hn
        exact Nat.le_trans h1 h2
      have htail :
          3*(n*n) + (3*n+1) ≤ n*n*n := by
        have h1 := Nat.add_le_add_left hsmall (3*(n*n))
        have h4 : 4*(n*n) ≤ n*(n*n) :=
          Nat.mul_le_mul_right (n*n) hn
        calc
          3*(n*n) + (3*n+1) ≤ 3*(n*n) + n*n := h1
          _ = 4*(n*n) := by omega
          _ ≤ n*(n*n) := h4
          _ = n*n*n := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have hexpand :
          (n+1)*(n+1)*(n+1) =
            n*n*n + (3*(n*n) + (3*n+1)) := by
        simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm]
        omega
      have hcube : (n+1)*(n+1)*(n+1) ≤ 2*(n*n*n) := by
        rw [hexpand]
        have h := Nat.add_le_add_left htail (n*n*n)
        simpa [Nat.two_mul] using h
      have hdouble : 2*(n*n*n) ≤ 2*(2^(n+2)) :=
        Nat.mul_le_mul_left 2 ih
      have hp : 2*(2^(n+2)) = 2^((n+1)+2) := by
        have hidx : (n+1)+2 = (n+2)+1 := by omega
        rw [hidx, Nat.pow_add_one]
        exact Nat.mul_comm _ _
      have hnext : (n+1)*(n+1)*(n+1) ≤ 2^((n+1)+2) := by
        rw [← hp]
        exact Nat.le_trans hcube hdouble
      simpa [n, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnext

/-- **Sharp rational tree-marker estimate.**  A tree on `v` cells has
`v-1` marker choices, and five copies of that capacity fit into two bits per
cell.  The exponent `2/5` is optimal because equality holds at `v=5`. -/
theorem tree_marker_fifth {v : Nat} (hv : 2 ≤ v) :
    treeFifth (v-1) ≤ 2^(v+v) := by
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
              have hsquare := sharp_square_four_plus d
              have hcube := sharp_cube_four_plus d
              have hmul := Nat.mul_le_mul hsquare hcube
              have hleft : 2 + (d+1+1+1) - 1 = 4+d := by omega
              have hright : 2 + (d+1+1+1) = 5+d := by omega
              rw [hleft, hright]
              calc
                treeFifth (4+d)
                    = ((4+d)*(4+d)) *
                      ((4+d)*(4+d)*(4+d)) := by
                        unfold treeFifth fourth
                        simp only [Nat.mul_assoc, Nat.mul_left_comm,
                          Nat.mul_comm]
                _ ≤ 2^(4+d) * 2^((4+d)+2) := hmul
                _ = 2^((4+d)+((4+d)+2)) :=
                      (Nat.pow_add 2 _ _).symm
                _ = 2^((5+d)+(5+d)) := by
                      congr 1
                      omega

/-- Products of exact tree-marker capacities obey the sharp fifth-power
bound. -/
theorem treeCapacity_fifth
    (m : Machine) (e r0 : Nat → Nat)
    {times : Nat → Prop}
    (blocks : List (TreeBlockCert m e r0 times))
    (hsize : ∀ b ∈ blocks, b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ blocks, 2 ≤ b.cells.length) :
    treeFifth (treeCapacity m e r0 blocks) ≤
      2^(treeCellCount m e r0 blocks +
        treeCellCount m e r0 blocks) := by
  induction blocks with
  | nil =>
      simp [treeCapacity, treeCellCount, treeFifth, fourth]
  | cons b rest ih =>
      have hbsize := hsize b List.mem_cons_self
      have hbmin := hmin b List.mem_cons_self
      have hbedge : b.edges.length = b.cells.length - 1 := by omega
      have hbcap : treeFifth b.edges.length ≤
          2^(b.cells.length + b.cells.length) := by
        rw [hbedge]
        exact tree_marker_fifth hbmin
      have htail := ih
        (fun x hx => hsize x (List.mem_cons_of_mem _ hx))
        (fun x hx => hmin x (List.mem_cons_of_mem _ hx))
      unfold treeCapacity treeCellCount
      calc
        treeFifth (b.edges.length * treeCapacity m e r0 rest)
            = treeFifth b.edges.length *
              treeFifth (treeCapacity m e r0 rest) :=
                treeFifth_mul _ _
        _ ≤ 2^(b.cells.length + b.cells.length) *
              2^(treeCellCount m e r0 rest +
                treeCellCount m e r0 rest) :=
                Nat.mul_le_mul hbcap htail
        _ = 2^((b.cells.length + b.cells.length) +
              (treeCellCount m e r0 rest +
                treeCellCount m e r0 rest)) :=
                (Nat.pow_add 2 _ _).symm
        _ = 2^((b.cells.length + treeCellCount m e r0 rest) +
              (b.cells.length + treeCellCount m e r0 rest)) := by
                congr 1
                omega

/-- Arithmetic core of the `7/10` estimate. -/
theorem seven_tenths_star_pair_bound
    (C L M A P : Nat)
    (hC : C = L + M)
    (hAL : A ≤ L)
    (hhalf : 2*A ≤ C)
    (hP : treeFifth P ≤ 2^(M+M)) :
    treeTenth (2^A * P) ≤ 2^(7*C) := by
  have hP10 : treeTenth P ≤ 2^((M+M)+(M+M)) := by
    unfold treeTenth
    calc
      treeFifth P * treeFifth P ≤
          2^(M+M) * 2^(M+M) := Nat.mul_le_mul hP hP
      _ = 2^((M+M)+(M+M)) := (Nat.pow_add 2 _ _).symm
  have hmul : treeTenth (2^A) * treeTenth P ≤
      2^(A+A+A+A+A+A+A+A+A+A) *
        2^((M+M)+(M+M)) := by
    exact Nat.mul_le_mul
      (Nat.le_of_eq (treeTenth_two_pow A)) hP10
  have hexp :
      (A+A+A+A+A+A+A+A+A+A) +
        ((M+M)+(M+M)) ≤ 7*C := by
    omega
  calc
    treeTenth (2^A * P) =
        treeTenth (2^A) * treeTenth P := treeTenth_mul _ _
    _ ≤ 2^(A+A+A+A+A+A+A+A+A+A) *
          2^((M+M)+(M+M)) := hmul
    _ = 2^((A+A+A+A+A+A+A+A+A+A) +
          ((M+M)+(M+M))) := (Nat.pow_add 2 _ _).symm
    _ ≤ 2^(7*C) := Nat.pow_le_pow_right (by omega) hexp

/-- **Certified mixed fixed-support bound with exponent `7/10`.**

This has exactly the hypotheses of `mixed_epoch_three_quarter`; only the
component-capacity arithmetic is sharpened. -/
theorem mixed_epoch_seven_tenths
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
    (hrootsNodup : (lobeForestRoots m e r0 lobes).Nodup)
    (hrootsSub : ∀ c ∈ lobeForestRoots m e r0 lobes,
      c ∈ allCells)
    (hclosed : StarClosed m allCells)
    (hvar : ∀ B ∈ lobes,
      VariesOnInterval m e r0 I J (B.root m))
    (hnoGray : ∀ k, I < k → k ≤ J → ¬ GrayTail m e r0 k)
    (hsize : ∀ b ∈ trees, b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ trees, 2 ≤ b.cells.length)
    (hC : allCells.length = L + treeCellCount m e r0 trees)
    (hAL : lobes.length ≤ L)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    treeTenth ks.length ≤ 2^(7*allCells.length) := by
  have hcount := mixed_epoch_count m e r0 hrun hr0 trees lobes
    fixed allCells ks hks hsupport hfixed hcover hnd
  have hhalf : 2 * lobes.length ≤ allCells.length :=
    active_lobe_forests_half m e r0 hrun hr0 hIJ allCells lobes
      hrootsNodup hrootsSub hclosed htimes hvar hnoGray
  have hcap := treeCapacity_fifth m e r0 trees hsize hmin
  have hmono : treeTenth ks.length ≤
      treeTenth (2^(lobes.length) * treeCapacity m e r0 trees) := by
    apply treeTenth_mono
    simpa [Nat.mul_comm] using hcount
  exact Nat.le_trans hmono
    (seven_tenths_star_pair_bound allCells.length L
      (treeCellCount m e r0 trees) lobes.length
      (treeCapacity m e r0 trees)
      hC hAL hhalf hcap)

end Echo
