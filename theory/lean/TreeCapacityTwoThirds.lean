import TreeCapacitySevenTenths

/-!
# A two-thirds component bound from one reserved cell per tree block

The exact tree marker capacity of a tree block on `v` cells is `v-1`.
The sharp uniform cubic estimate is

    (v-1)^3 ≤ 2^(v+1).

Thus a list of `Q` tree blocks using `M` cells has

    treeCapacity^3 ≤ 2^(M+Q).

If `A` varying lobe roots are encoded by independent bits, the existing
mouth-pair separation gives `2*A ≤ C`.  A stronger, local no-trap statement
reserves one additional non-lobe cell per variable tree component:

    2*A + Q ≤ C.

Together these facts imply

    states^3 ≤ 2^(2*C),

so one fixed-support epoch has exponential base `2^(2/3) ≈ 1.5874`.
The final theorem below has exactly the hypotheses of
`mixed_epoch_seven_tenths`, with the stronger reserved-cell inequality in
place of the weaker half-density-only arithmetic.
-/

namespace Echo

/-- Third power. -/
def treeCube (x : Nat) : Nat := x * x * x

private theorem treeCube_mul (x y : Nat) :
    treeCube (x * y) = treeCube x * treeCube y := by
  unfold treeCube
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Cubing is monotone on naturals. -/
theorem treeCube_mono {x y : Nat} (h : x ≤ y) :
    treeCube x ≤ treeCube y := by
  unfold treeCube
  exact Nat.mul_le_mul (Nat.mul_le_mul h h) h

private theorem treeCube_two_pow (A : Nat) :
    treeCube (2^A) = 2^(A+A+A) := by
  unfold treeCube
  simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- The elementary cube estimate `n^3 ≤ 2^(n+2)` from `n=4` onward. -/
private theorem tree_cube_four_plus : ∀ d : Nat,
    treeCube (4+d) ≤ 2^((4+d)+2) := by
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
      simpa [treeCube, n, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnext

/-- **Sharp cubic tree-marker estimate.**  A tree on `v` cells has `v-1`
possible full-edge markers, and three copies of this capacity fit in `v+1`
bits.  Equality occurs at `v=5`: `4^3 = 2^6`. -/
theorem tree_marker_cube {v : Nat} (hv : 2 ≤ v) :
    treeCube (v-1) ≤ 2^(v+1) := by
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
              have h := tree_cube_four_plus d
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using h

/-- Products of exact tree-marker capacities obey the cubic component bound.
The extra `blocks.length` term is one reserved bit per component. -/
theorem treeCapacity_cube
    (m : Machine) (e r0 : Nat → Nat)
    {times : Nat → Prop}
    (blocks : List (TreeBlockCert m e r0 times))
    (hsize : ∀ b ∈ blocks, b.edges.length + 1 = b.cells.length)
    (hmin : ∀ b ∈ blocks, 2 ≤ b.cells.length) :
    treeCube (treeCapacity m e r0 blocks) ≤
      2^(treeCellCount m e r0 blocks + blocks.length) := by
  induction blocks with
  | nil =>
      simp [treeCapacity, treeCellCount, treeCube]
  | cons b rest ih =>
      have hbsize := hsize b List.mem_cons_self
      have hbmin := hmin b List.mem_cons_self
      have hbedge : b.edges.length = b.cells.length - 1 := by omega
      have hbcap : treeCube b.edges.length ≤
          2^(b.cells.length + 1) := by
        rw [hbedge]
        exact tree_marker_cube hbmin
      have htail := ih
        (fun x hx => hsize x (List.mem_cons_of_mem _ hx))
        (fun x hx => hmin x (List.mem_cons_of_mem _ hx))
      unfold treeCapacity treeCellCount
      simp only [List.length_cons]
      calc
        treeCube (b.edges.length * treeCapacity m e r0 rest)
            = treeCube b.edges.length *
              treeCube (treeCapacity m e r0 rest) :=
                treeCube_mul _ _
        _ ≤ 2^(b.cells.length + 1) *
              2^(treeCellCount m e r0 rest + rest.length) :=
                Nat.mul_le_mul hbcap htail
        _ = 2^((b.cells.length + 1) +
              (treeCellCount m e r0 rest + rest.length)) :=
                (Nat.pow_add 2 _ _).symm
        _ = 2^((b.cells.length + treeCellCount m e r0 rest) +
              (rest.length + 1)) := by
                congr 1
                omega

/-- Arithmetic core of the `2/3` estimate. -/
theorem two_thirds_reserved_component_bound
    (C L M A Q P : Nat)
    (hC : C = L + M)
    (hAL : A ≤ L)
    (hreserved : 2*A + Q ≤ C)
    (hP : treeCube P ≤ 2^(M+Q)) :
    treeCube (2^A * P) ≤ 2^(2*C) := by
  have hmul : treeCube (2^A) * treeCube P ≤
      2^(A+A+A) * 2^(M+Q) := by
    exact Nat.mul_le_mul
      (Nat.le_of_eq (treeCube_two_pow A)) hP
  have hexp : (A+A+A) + (M+Q) ≤ 2*C := by
    omega
  calc
    treeCube (2^A * P) =
        treeCube (2^A) * treeCube P := treeCube_mul _ _
    _ ≤ 2^(A+A+A) * 2^(M+Q) := hmul
    _ = 2^((A+A+A) + (M+Q)) :=
          (Nat.pow_add 2 _ _).symm
    _ ≤ 2^(2*C) := Nat.pow_le_pow_right (by omega) hexp

/-- **Certified mixed fixed-support bound with exponent `2/3`.**

Compared with `mixed_epoch_seven_tenths`, the sole extra input is
`hreserved`: besides the mouth partner required by every active lobe root,
each variable tree component has one further reserved cell.  The next
structural lemma is to derive this inequality from the absence of the
external-lobe reflector trap. -/
theorem mixed_epoch_two_thirds
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
    (hreserved : 2*lobes.length + trees.length ≤ allCells.length)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    treeCube ks.length ≤ 2^(2*allCells.length) := by
  have hcount := mixed_epoch_count m e r0 hrun hr0 trees lobes
    fixed allCells ks hks hsupport hfixed hcover hnd
  have hcap := treeCapacity_cube m e r0 trees hsize hmin
  have hmono : treeCube ks.length ≤
      treeCube (2^(lobes.length) * treeCapacity m e r0 trees) := by
    apply treeCube_mono
    simpa [Nat.mul_comm] using hcount
  exact Nat.le_trans hmono
    (two_thirds_reserved_component_bound allCells.length L
      (treeCellCount m e r0 trees) lobes.length trees.length
      (treeCapacity m e r0 trees)
      hC hAL hreserved hcap)

end Echo
