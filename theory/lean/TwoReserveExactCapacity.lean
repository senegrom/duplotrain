import TreeCapacityTwoThirds

/-!
# Exact capacity with two reserved cells per variable component

The paired-router trap suggests the next structural inequality:
for a tree component with `v` cells, at most `v-2` cells can be mouth partners
of independently varying lobe roots before a bounded tail begins.

For such a component with `a ≤ v-2` active lobe bits, the exact static code
capacity is

    2^a * (v-1).

This file proves the sharp convenient uniform estimate

    (2^a * (v-1))^10 ≤ 80^(v+a).

The extremal case is `v=6, a=4`, where the capacity is exactly `80` on ten
cells.  Consequently any product of such component codes has exponential base

    80^(1/10) ≈ 1.54992,

strictly better than `2^(2/3) ≈ 1.58740`.
-/

namespace Echo

private theorem reserveTenth_mul (x y : Nat) :
    treeTenth (x*y) = treeTenth x * treeTenth y := by
  unfold treeTenth treeFifth fourth
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem reserveTenth_two_pow (d : Nat) :
    treeTenth (2^d) = 2^(10*d) := by
  unfold treeTenth treeFifth fourth
  simp only [← Nat.pow_add]
  congr 1
  omega

/-- Capacity obtained by saturating the two-reserved-cell constraint. -/
def saturatedRouterCapacity (v : Nat) : Nat :=
  2^(v-2) * (v-1)

/-- Its corresponding saturated cell count. -/
def saturatedRouterCells (v : Nat) : Nat :=
  2*v - 2

/-- The capacity ratio from `v` to `v+1` is at most `12/5` from `v=6`
onward.  In tenth powers this is at most `6400 = 80^2`. -/
private theorem saturatedRouter_ratio
    {v : Nat} (hv : 6 ≤ v) :
    treeTenth (saturatedRouterCapacity (v+1)) ≤
      6400 * treeTenth (saturatedRouterCapacity v) := by
  have hidx : (v+1)-2 = (v-2)+1 := by omega
  have harith : 10*v ≤ 12*(v-1) := by omega
  have hlin :
      5 * saturatedRouterCapacity (v+1) ≤
        12 * saturatedRouterCapacity v := by
    unfold saturatedRouterCapacity
    rw [hidx, Nat.pow_succ]
    calc
      5 * (2^(v-2) * 2 * ((v+1)-1))
          = 2^(v-2) * (10*v) := by
              congr 1
              omega
      _ ≤ 2^(v-2) * (12*(v-1)) :=
            Nat.mul_le_mul_left _ harith
      _ = 12 * (2^(v-2) * (v-1)) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hp := treeTenth_mono hlin
  rw [reserveTenth_mul, reserveTenth_mul] at hp
  have hconst : treeTenth 12 ≤ 6400 * treeTenth 5 := by
    decide
  have hbound :
      treeTenth 5 * treeTenth (saturatedRouterCapacity (v+1)) ≤
        treeTenth 5 *
          (6400 * treeTenth (saturatedRouterCapacity v)) := by
    calc
      treeTenth 5 * treeTenth (saturatedRouterCapacity (v+1))
          ≤ treeTenth 12 * treeTenth (saturatedRouterCapacity v) := hp
      _ ≤ (6400 * treeTenth 5) *
          treeTenth (saturatedRouterCapacity v) :=
            Nat.mul_le_mul_right _ hconst
      _ = treeTenth 5 *
          (6400 * treeTenth (saturatedRouterCapacity v)) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hfive : treeTenth 5 = 9765625 := by decide
  rw [hfive] at hbound
  omega

/-- Saturated components from six cells onward obey the exact base-80 bound. -/
private theorem saturatedRouter_six_plus : ∀ d : Nat,
    treeTenth (saturatedRouterCapacity (6+d)) ≤
      80^(saturatedRouterCells (6+d)) := by
  intro d
  induction d with
  | zero => decide
  | succ d ih =>
      let v := 6+d
      have hv : 6 ≤ v := by
        dsimp [v]
        omega
      have hratio := saturatedRouter_ratio hv
      have hmul :
          6400 * treeTenth (saturatedRouterCapacity v) ≤
            6400 * 80^(saturatedRouterCells v) :=
        Nat.mul_le_mul_left 6400 ih
      have hstep :
          treeTenth (saturatedRouterCapacity (v+1)) ≤
            6400 * 80^(saturatedRouterCells v) :=
        Nat.le_trans hratio hmul
      have h6400 : 6400 = 80^2 := by decide
      have hcells : saturatedRouterCells (v+1) =
          saturatedRouterCells v + 2 := by
        unfold saturatedRouterCells
        omega
      rw [h6400, ← Nat.pow_add, ← hcells] at hstep
      simpa [v, Nat.add_assoc] using hstep

/-- Saturated capacity bound for every `v≥2`. -/
theorem saturatedRouter_tenth
    {v : Nat} (hv : 2 ≤ v) :
    treeTenth (saturatedRouterCapacity v) ≤
      80^(saturatedRouterCells v) := by
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
                    saturatedRouter_six_plus d

/-- Actual component capacity with `a` active lobe bits. -/
def twoReservePartCapacity (v a : Nat) : Nat :=
  2^a * (v-1)

/-- Actual number of cells charged to that component. -/
def twoReservePartCells (v a : Nat) : Nat := v+a

/-- **Exact one-component two-reserve bound.** -/
theorem twoReservePart_tenth
    (v a : Nat) (hv : 2 ≤ v) (ha : a + 2 ≤ v) :
    treeTenth (twoReservePartCapacity v a) ≤
      80^(twoReservePartCells v a) := by
  let d := (v-2)-a
  have had : a+d = v-2 := by
    dsimp [d]
    omega
  have hsatCells : saturatedRouterCells v =
      twoReservePartCells v a + d := by
    unfold saturatedRouterCells twoReservePartCells
    omega
  have hsatCap : saturatedRouterCapacity v =
      2^d * twoReservePartCapacity v a := by
    unfold saturatedRouterCapacity twoReservePartCapacity
    rw [← Nat.pow_add, had]
    simp only [Nat.mul_assoc]
  have hsat := saturatedRouter_tenth hv
  rw [hsatCap, reserveTenth_mul, hsatCells,
    Nat.pow_add] at hsat
  have h80two : 80^d ≤ treeTenth (2^d) := by
    rw [reserveTenth_two_pow]
    have hbase : 80 ≤ 2^10 := by decide
    exact Nat.pow_le_pow_left hbase d
  have hscaled :
      80^d * treeTenth (twoReservePartCapacity v a) ≤
        80^d * 80^(twoReservePartCells v a) := by
    calc
      80^d * treeTenth (twoReservePartCapacity v a)
          ≤ treeTenth (2^d) *
              treeTenth (twoReservePartCapacity v a) :=
            Nat.mul_le_mul_right _ h80two
      _ ≤ 80^(twoReservePartCells v a) * 80^d := hsat
      _ = 80^d * 80^(twoReservePartCells v a) := by
            exact Nat.mul_comm _ _
  have hpos : 0 < 80^d := Nat.pow_pos (by omega) _
  exact Nat.le_of_mul_le_mul_left hscaled hpos

/-- A profile stores `(tree cells, active lobe bits assigned to the component)`. -/
def twoReserveProfileCapacity : List (Nat × Nat) → Nat
  | [] => 1
  | p :: ps =>
      twoReservePartCapacity p.1 p.2 * twoReserveProfileCapacity ps

/-- Total charged cells of the profile. -/
def twoReserveProfileCells : List (Nat × Nat) → Nat
  | [] => 0
  | p :: ps =>
      twoReservePartCells p.1 p.2 + twoReserveProfileCells ps

/-- **Products of two-reserve components retain the exact base-80 bound.** -/
theorem twoReserveProfile_tenth
    (parts : List (Nat × Nat))
    (hvalid : ∀ p ∈ parts, 2 ≤ p.1 ∧ p.2 + 2 ≤ p.1) :
    treeTenth (twoReserveProfileCapacity parts) ≤
      80^(twoReserveProfileCells parts) := by
  induction parts with
  | nil =>
      simp [twoReserveProfileCapacity, twoReserveProfileCells,
        treeTenth, treeFifth, fourth]
  | cons p rest ih =>
      have hp := hvalid p List.mem_cons_self
      have hpart := twoReservePart_tenth p.1 p.2 hp.1 hp.2
      have htail := ih (fun q hq =>
        hvalid q (List.mem_cons_of_mem _ hq))
      unfold twoReserveProfileCapacity twoReserveProfileCells
      calc
        treeTenth
            (twoReservePartCapacity p.1 p.2 *
              twoReserveProfileCapacity rest)
            = treeTenth (twoReservePartCapacity p.1 p.2) *
              treeTenth (twoReserveProfileCapacity rest) :=
                reserveTenth_mul _ _
        _ ≤ 80^(twoReservePartCells p.1 p.2) *
              80^(twoReserveProfileCells rest) :=
                Nat.mul_le_mul hpart htail
        _ = 80^(twoReservePartCells p.1 p.2 +
              twoReserveProfileCells rest) :=
                (Nat.pow_add 80 _ _).symm

end Echo
