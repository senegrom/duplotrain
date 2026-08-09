import HiddenDichotomy
import SteeringLaw
import SupportWeightFibres

/-!
# Stationary recurrent tails

This file isolates the recurrent case in which the complete cell-level arrow
projection `nextCell` is stationary.  A stationary productive step which
preserves occupied support is a hidden lobe flip.  On a primitive periodic
cell orbit, the reversal identity reflects the orbit about the first such
flip.  A cyclic reflection has at most two flipped edges.  Consequently only
two registers can change, each by its `bar` involution, and the complete
register snapshot has at most four values.

The primitive-period and productive-anchor hypotheses are explicit.  They are
the finite-orbit hypotheses needed by the reflection argument; no global
injectivity of `nextCell` is assumed.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Cell occupied by the run `n` steps after `K`. -/
def tailCell (K n : Nat) : Nat :=
  m.cellOf (e (K + n))

/-- A positive period whose first period contains no repeated cell. -/
def PrimitiveCellPeriod (K q : Nat) : Prop :=
  0 < q ∧
  (∀ n, tailCell m e K (n + q) = tailCell m e K n) ∧
  ∀ i, i < q → ∀ j, j < q →
    tailCell m e K i = tailCell m e K j → i = j

/-- Stepwise stationarity makes the entire tail projection equal to its value
at the base time. -/
theorem nextCell_stationary_iter {K : Nat}
    (hstationary : ∀ t, K ≤ t → ∀ c,
      nextCell m e r0 (t+1) c = nextCell m e r0 t c) :
    ∀ n c, nextCell m e r0 (K+n) c = nextCell m e r0 K c := by
  intro n
  induction n with
  | zero =>
      intro c
      rfl
  | succ n ih =>
      intro c
      have harith : K + (n+1) = (K+n)+1 := by omega
      calc
        nextCell m e r0 (K + (n+1)) c =
            nextCell m e r0 ((K+n)+1) c := by rw [harith]
        _ = nextCell m e r0 (K+n) c :=
          hstationary (K+n) (Nat.le_add_right _ _) c
        _ = nextCell m e r0 K c := ih c

/-- The fixed projection advances the actual tail cell orbit. -/
theorem stationary_tail_step (hrun : IsRun m e r0) {K : Nat}
    (hstationary : ∀ t, K ≤ t → ∀ c,
      nextCell m e r0 (t+1) c = nextCell m e r0 t c)
    (n : Nat) :
    nextCell m e r0 K (tailCell m e K n) =
      tailCell m e K (n+1) := by
  calc
    nextCell m e r0 K (tailCell m e K n) =
        nextCell m e r0 (K+n) (m.cellOf (e (K+n))) := by
      rw [nextCell_stationary_iter m e r0 hstationary n]
      rfl
    _ = m.cellOf (e ((K+n)+1)) := cell_step m e r0 hrun (K+n)
    _ = tailCell m e K (n+1) := by
      unfold tailCell
      congr 2 <;> omega

/-- The fixed projection also carries the star of the next orbit cell back to
the star of the current one. -/
theorem stationary_tail_reversal (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {K : Nat}
    (hstationary : ∀ t, K ≤ t → ∀ c,
      nextCell m e r0 (t+1) c = nextCell m e r0 t c)
    (n : Nat) :
    nextCell m e r0 K (m.star (tailCell m e K (n+1))) =
      m.star (tailCell m e K n) := by
  calc
    nextCell m e r0 K (m.star (tailCell m e K (n+1))) =
        nextCell m e r0 (K+n+1)
          (m.star (m.cellOf (e (K+n+1)))) := by
      have h := (nextCell_stationary_iter m e r0 hstationary (n+1)
        (m.star (tailCell m e K (n+1)))).symm
      simpa [tailCell, Nat.add_assoc] using h
    _ = m.star (m.cellOf (e (K+n))) :=
      reversed_arrow m e r0 hrun hr0 (K+n)
    _ = m.star (tailCell m e K n) := by rfl

/-- Iterate one period to reduce every orbit index to its residue. -/
theorem tailCell_period_mul {K q : Nat}
    (hperiod : ∀ n,
      tailCell m e K (n+q) = tailCell m e K n) :
    ∀ a n, tailCell m e K (a + n*q) = tailCell m e K a := by
  intro a n
  induction n with
  | zero => simp
  | succ n ih =>
      have harith : a + (n+1)*q = (a+n*q)+q := by
        rw [Nat.succ_mul]
        omega
      calc
        tailCell m e K (a + (n+1)*q) =
            tailCell m e K ((a+n*q)+q) := by rw [harith]
        _ = tailCell m e K (a+n*q) := hperiod (a+n*q)
        _ = tailCell m e K a := ih

theorem tailCell_reduce {K q : Nat} (hq : 0 < q)
    (hperiod : ∀ n,
      tailCell m e K (n+q) = tailCell m e K n)
    (n : Nat) :
    tailCell m e K n = tailCell m e K (n % q) := by
  have hiter := tailCell_period_mul m e hperiod (n % q) (n / q)
  have harith : n % q + (n / q) * q = n := by
    calc
      n % q + (n / q) * q = n % q + q * (n / q) := by
        rw [Nat.mul_comm]
      _ = n := Nat.mod_add_div n q
  rw [harith] at hiter
  exact hiter

/-- Elementary arithmetic for the two fixed edges of a cyclic reflection. -/
theorem reflection_residue_two {q b : Nat} (hq : 0 < q) (hb : b < q)
    (hmod : (b+1) % q = (q+1-b) % q) :
    b = 0 ∨ 2*b = q := by
  by_cases hb0 : b = 0
  · exact Or.inl hb0
  have hbpos : 0 < b := by omega
  have hxle : b+1 ≤ q := by omega
  have hyle : q+1-b ≤ q := by omega
  by_cases hx : b+1 = q
  · by_cases hy : q+1-b = q
    · right
      omega
    · have hylt : q+1-b < q := by omega
      have hqmod : q % q = 0 := Nat.mod_self q
      have hymod : (q+1-b) % q = q+1-b := Nat.mod_eq_of_lt hylt
      rw [hx, hqmod, hymod] at hmod
      right
      omega
  · have hxlt : b+1 < q := by omega
    by_cases hy : q+1-b = q
    · have hxmod : (b+1) % q = b+1 := Nat.mod_eq_of_lt hxlt
      have hqmod : q % q = 0 := Nat.mod_self q
      rw [hy, hxmod, hqmod] at hmod
      right
      omega
    · have hylt : q+1-b < q := by omega
      rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hmod
      right
      omega

/-- A productive support-preserving stationary step is exactly a lobe flip. -/
theorem stationary_productive_flip (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {K t : Nat}
    (hKt : K ≤ t) (hp : ProductiveStep m e r0 t)
    (hstationary : ∀ u, K ≤ u → ∀ c,
      nextCell m e r0 (u+1) c = nextCell m e r0 u c)
    (hfixed : ∀ u, K ≤ u → SupportFixedStep m e r0 u) :
    e (t+1) = m.bar (reg m e r0 t (m.cellOf (e (t+1)))) ∧
    m.cellOf (e (t+1)) = m.star (m.cellOf (e t)) := by
  have h := hidden_fixed_is_lobe m e r0 hrun hr0 t hp
    (hstationary t hKt) (hfixed t hKt)
  exact ⟨h.1, h.2.2⟩

/-- The productive anchor reflects the whole primitive orbit. -/
theorem stationary_orbit_reflection (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {K q : Nat}
    (hq : 0 < q)
    (hperiod : ∀ n,
      tailCell m e K (n+q) = tailCell m e K n)
    (hstationary : ∀ t, K ≤ t → ∀ c,
      nextCell m e r0 (t+1) c = nextCell m e r0 t c)
    (hanchor : tailCell m e K 1 = m.star (tailCell m e K 0)) :
    ∀ n, n ≤ q →
      m.star (tailCell m e K (q-n)) = tailCell m e K (1+n) := by
  intro n hn
  induction n with
  | zero =>
      have hp0 := hperiod 0
      simp only [Nat.zero_add] at hp0
      rw [Nat.sub_zero, hp0]
      exact hanchor.symm
  | succ n ih =>
      have hnlt : n < q := by omega
      have hindex : q - (n+1) + 1 = q-n := by omega
      calc
        m.star (tailCell m e K (q-(n+1))) =
            nextCell m e r0 K
              (m.star (tailCell m e K (q-(n+1)+1))) := by
          exact (stationary_tail_reversal m e r0 hrun hr0
            hstationary (q-(n+1))).symm
        _ = nextCell m e r0 K
              (m.star (tailCell m e K (q-n))) := by rw [hindex]
        _ = nextCell m e r0 K (tailCell m e K (1+n)) := by
          rw [ih (by omega)]
        _ = tailCell m e K ((1+n)+1) :=
          stationary_tail_step m e r0 hrun hstationary (1+n)
        _ = tailCell m e K (1+(n+1)) := by
          have harith : (1+n)+1 = 1+(n+1) := by omega
          rw [harith]

/-- On a stationary primitive orbit based at a productive step, every later
productive write lands in one of at most two cells. -/
theorem stationary_productive_writers_two (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {K q : Nat}
    (hprimitive : PrimitiveCellPeriod m e K q)
    (hstationary : ∀ t, K ≤ t → ∀ c,
      nextCell m e r0 (t+1) c = nextCell m e r0 t c)
    (hfixed : ∀ t, K ≤ t → SupportFixedStep m e r0 t)
    (hanchor : ProductiveStep m e r0 K) :
    ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) = tailCell m e K 1 ∨
      m.cellOf (e (t+1)) = tailCell m e K (q/2+1) := by
  rcases hprimitive with ⟨hq, hperiod, hinj⟩
  have hanchorCell : tailCell m e K 1 = m.star (tailCell m e K 0) := by
    have h := stationary_productive_flip m e r0 hrun hr0
      (K := K) (t := K) (Nat.le_refl _) hanchor hstationary hfixed
    exact h.2
  have hreflect := stationary_orbit_reflection m e r0 hrun hr0 hq
    hperiod hstationary hanchorCell
  intro t hKt hp
  obtain ⟨d, rfl⟩ : ∃ d, t = K+d := ⟨t-K, by omega⟩
  let b := d % q
  have hb : b < q := Nat.mod_lt _ hq
  have hflipCell := (stationary_productive_flip m e r0 hrun hr0
    (K := K) (t := K+d) (Nat.le_add_right _ _) hp
    hstationary hfixed).2
  have hd0 := tailCell_reduce m e hq hperiod d
  have hd1 := tailCell_reduce m e hq hperiod (d+1)
  have hb1reduce := tailCell_reduce m e hq hperiod (b+1)
  have hsuccmod : (d+1) % q = (b+1) % q := by
    dsimp [b]
    rw [Nat.add_mod d 1 q, Nat.add_mod (d % q) 1 q,
      Nat.mod_mod]
  have hactive : tailCell m e K (b+1) =
      m.star (tailCell m e K b) := by
    have hflipTail : tailCell m e K (d+1) =
        m.star (tailCell m e K d) := by
      simpa [tailCell, Nat.add_assoc] using hflipCell
    calc
      tailCell m e K (b+1) = tailCell m e K ((b+1)%q) := hb1reduce
      _ = tailCell m e K ((d+1)%q) := by rw [hsuccmod]
      _ = tailCell m e K (d+1) := hd1.symm
      _ = m.star (tailCell m e K d) := hflipTail
      _ = m.star (tailCell m e K b) := by rw [hd0]
  have href := hreflect (q-b) (by omega)
  have hsub : q-(q-b) = b := by omega
  rw [hsub] at href
  have hcellEq : tailCell m e K (b+1) =
      tailCell m e K (q+1-b) := by
    have hidx : 1+(q-b) = q+1-b := by omega
    rw [hidx] at href
    exact hactive.trans href
  have hleft := tailCell_reduce m e hq hperiod (b+1)
  have hright := tailCell_reduce m e hq hperiod (q+1-b)
  have hresCell : tailCell m e K ((b+1)%q) =
      tailCell m e K ((q+1-b)%q) := by
    rw [← hleft, ← hright]
    exact hcellEq
  have hmod : (b+1)%q = (q+1-b)%q :=
    hinj _ (Nat.mod_lt _ hq) _ (Nat.mod_lt _ hq) hresCell
  rcases reflection_residue_two hq hb hmod with hb0 | hhalf
  · left
    have hwriter : m.cellOf (e (K+d+1)) = tailCell m e K (d+1) := by
      simp [tailCell, Nat.add_assoc]
    have hwriterReduce : m.cellOf (e (K+d+1)) =
        tailCell m e K (b+1) := by
      calc
        m.cellOf (e (K+d+1)) = tailCell m e K (d+1) := hwriter
        _ = tailCell m e K ((d+1)%q) := hd1
        _ = tailCell m e K ((b+1)%q) := by rw [hsuccmod]
        _ = tailCell m e K (b+1) := hb1reduce.symm
    simpa [hb0] using hwriterReduce
  · right
    have hbhalf : b = q/2 := by
      have hdiv : (2*b)/2 = b := by
        simpa [Nat.mul_comm] using Nat.mul_div_left b (by omega : 0 < 2)
      rw [hhalf] at hdiv
      exact hdiv.symm
    have hwriter : m.cellOf (e (K+d+1)) = tailCell m e K (d+1) := by
      simp [tailCell, Nat.add_assoc]
    have hwriterReduce : m.cellOf (e (K+d+1)) =
        tailCell m e K (b+1) := by
      calc
        m.cellOf (e (K+d+1)) = tailCell m e K (d+1) := hwriter
        _ = tailCell m e K ((d+1)%q) := hd1
        _ = tailCell m e K ((b+1)%q) := by rw [hsuccmod]
        _ = tailCell m e K (b+1) := hb1reduce.symm
    simpa [hbhalf] using hwriterReduce

/-- If every productive write into `C` is a bar-flip, then its register is
binary; unproductive arrivals merely rewrite the same value. -/
theorem productive_flip_lock {C K : Nat}
    (hflip : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) = C →
      e (t+1) = m.bar (reg m e r0 t C)) :
    ∀ d, reg m e r0 (K+d) C = reg m e r0 K C ∨
      reg m e r0 (K+d) C = m.bar (reg m e r0 K C) := by
  intro d
  induction d with
  | zero => exact Or.inl rfl
  | succ n ih =>
      by_cases hc : m.cellOf (e (K+n+1)) = C
      · have hw : reg m e r0 (K+n+1) C = e (K+n+1) :=
          reg_write m e r0 hc
        by_cases hp : ProductiveStep m e r0 (K+n)
        · have hf := hflip (K+n) (Nat.le_add_right _ _) hp hc
          rcases ih with hi | hi
          · right
            show reg m e r0 (K+n+1) C = m.bar (reg m e r0 K C)
            rw [hw, hf, hi]
          · left
            show reg m e r0 (K+n+1) C = reg m e r0 K C
            rw [hw, hf, hi, m.bar_invol]
        · have hun : e (K+n+1) = reg m e r0 (K+n) C := by
            unfold ProductiveStep at hp
            apply Classical.byContradiction
            intro hne
            apply hp
            simpa [hc] using hne
          rcases ih with hi | hi
          · left
            show reg m e r0 (K+n+1) C = reg m e r0 K C
            rw [hw, hun, hi]
          · right
            show reg m e r0 (K+n+1) C = m.bar (reg m e r0 K C)
            rw [hw, hun, hi]
      · rcases ih with hi | hi
        · left
          show reg m e r0 (K+n+1) C = reg m e r0 K C
          rw [reg_skip m e r0 hc]
          exact hi
        · right
          show reg m e r0 (K+n+1) C = m.bar (reg m e r0 K C)
          rw [reg_skip m e r0 hc]
          exact hi

private theorem nodup_subset_length_stationary
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

/-- **Stationary primitive recurrent tail: four snapshots.**

The base time is a productive point on a primitive periodic cell orbit.  The
projection and occupied support are stationary from that point onward.  Any
duplicate-free sample of later complete register snapshots has size at most
four. -/
theorem stationary_primitive_tail_four (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {K q : Nat}
    (hprimitive : PrimitiveCellPeriod m e K q)
    (hstationary : ∀ t, K ≤ t → ∀ c,
      nextCell m e r0 (t+1) c = nextCell m e r0 t c)
    (hfixed : ∀ t, K ≤ t → SupportFixedStep m e r0 t)
    (hanchor : ProductiveStep m e r0 K)
    (cells ks : List Nat)
    (hks : ∀ j ∈ ks, K ≤ j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ 4 := by
  let A := tailCell m e K 1
  let B := tailCell m e K (q/2+1)
  have hwriters : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) ∈ [A, B] := by
    intro t ht hp
    rcases stationary_productive_writers_two m e r0 hrun hr0
      hprimitive hstationary hfixed hanchor t ht hp with hA | hB
    · simp [A, hA]
    · simp [B, hB]
  have hflip : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      e (t+1) = m.bar (reg m e r0 t (m.cellOf (e (t+1)))) := by
    intro t ht hp
    exact (stationary_productive_flip m e r0 hrun hr0 ht hp
      hstationary hfixed).1
  have hlockA : ∀ d, reg m e r0 (K+d) A = reg m e r0 K A ∨
      reg m e r0 (K+d) A = m.bar (reg m e r0 K A) := by
    apply productive_flip_lock m e r0
    intro t ht hp hc
    simpa [hc] using hflip t ht hp
  have hlockB : ∀ d, reg m e r0 (K+d) B = reg m e r0 K B ∨
      reg m e r0 (K+d) B = m.bar (reg m e r0 K B) := by
    apply productive_flip_lock m e r0
    intro t ht hp hc
    simpa [hc] using hflip t ht hp
  let candidates : List (List Nat) :=
    [cells.map (fun c => if c = A then reg m e r0 K A
      else if c = B then reg m e r0 K B else reg m e r0 K c),
     cells.map (fun c => if c = A then reg m e r0 K A
      else if c = B then m.bar (reg m e r0 K B) else reg m e r0 K c),
     cells.map (fun c => if c = A then m.bar (reg m e r0 K A)
      else if c = B then reg m e r0 K B else reg m e r0 K c),
     cells.map (fun c => if c = A then m.bar (reg m e r0 K A)
      else if c = B then m.bar (reg m e r0 K B) else reg m e r0 K c)]
  have hmember : ∀ j, K ≤ j → snap m e r0 cells j ∈ candidates := by
    intro j hj
    obtain ⟨d, rfl⟩ : ∃ d, j = K+d := ⟨j-K, by omega⟩
    have hfrozen : ∀ c, c ≠ A → c ≠ B →
        reg m e r0 (K+d) c = reg m e r0 K c := by
      intro c hcA hcB
      exact writers_frozen_foreign m e r0 hwriters
        (W := c) (by simp [hcA, hcB]) (K+d) (Nat.le_add_right _ _)
    have hsnap : snap m e r0 cells (K+d) =
        cells.map (fun c => if c = A then reg m e r0 (K+d) A
          else if c = B then reg m e r0 (K+d) B
          else reg m e r0 K c) := by
      unfold snap
      apply List.map_congr_left
      intro c _
      by_cases hcA : c = A
      · rw [if_pos hcA, hcA]
      · rw [if_neg hcA]
        by_cases hcB : c = B
        · rw [if_pos hcB, hcB]
        · rw [if_neg hcB]
          exact hfrozen c hcA hcB
    rw [hsnap]
    rcases hlockA d with ha | ha <;> rcases hlockB d with hb | hb <;>
      rw [ha, hb]
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))
  have hle := nodup_subset_length_stationary hnd (fun v hv => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
    exact hmember j (hks j hj))
  rw [List.length_map] at hle
  simpa [candidates] using hle

/-- Register recurrence supplies the support-fixed hypothesis used above. -/
theorem support_fixed_of_register_period (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {K q : Nat} (hq : 0 < q)
    (hregperiod : ∀ t c, K ≤ t →
      reg m e r0 (t+q) c = reg m e r0 t c) :
    ∀ t, K ≤ t → SupportFixedStep m e r0 t := by
  intro t ht
  have hend : ∀ s, Occupied m e r0 t s ↔ Occupied m e r0 (t+q) s := by
    intro s
    unfold Occupied Confirmed
    rw [hregperiod t (m.cellOf s) ht,
      hregperiod t (m.cellOf (m.bar s)) ht]
  have hpaired := pairedSupportFixed_of_endpoint_eq m e r0 hrun hr0
    (lo := t) (hi := t+q) (Nat.le_add_right _ _) hend
  intro s
  exact (hpaired t (Nat.le_refl _) (by omega) s).symm

/-- Recurrent-tail wrapper: exact entry/register recurrence, a primitive cell
period, and a stationary projection imply the four-snapshot theorem when the
cycle is based at a productive step. -/
theorem stationary_recurrent_tail_four (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {K q : Nat}
    (hq : 0 < q)
    (hentryperiod : ∀ t, K ≤ t → e (t+q) = e t)
    (hregperiod : ∀ t c, K ≤ t →
      reg m e r0 (t+q) c = reg m e r0 t c)
    (hprimitive : ∀ i, i < q → ∀ j, j < q →
      tailCell m e K i = tailCell m e K j → i = j)
    (hstationary : ∀ t, K ≤ t → ∀ c,
      nextCell m e r0 (t+1) c = nextCell m e r0 t c)
    (hanchor : ProductiveStep m e r0 K)
    (cells ks : List Nat)
    (hks : ∀ j ∈ ks, K ≤ j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ 4 := by
  have hcellperiod : ∀ n,
      tailCell m e K (n+q) = tailCell m e K n := by
    intro n
    unfold tailCell
    have h := congrArg m.cellOf
      (hentryperiod (K+n) (Nat.le_add_right _ _))
    simpa only [Nat.add_assoc] using h
  exact stationary_primitive_tail_four m e r0 hrun hr0
    ⟨hq, hcellperiod, hprimitive⟩ hstationary
    (support_fixed_of_register_period m e r0 hrun hr0 hq hregperiod)
    hanchor cells ks hks hnd

end Echo
