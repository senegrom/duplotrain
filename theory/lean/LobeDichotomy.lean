import Periodicity

/-!
# The lobe dichotomy: every cycle cell is a Gray flipper or foreign-valued

Delivering a slot `v` into a cell requires its bar-partner to be *held*:
at every step, `bar (e (k+1))` is the current register of its own cell
(`partner_held`, a corollary of the witness theorem).  Two consequences:

* **Irreversibility** (`cross_stays_cross`): once a cell's register has
  its partner outside the cell, it can never again hold an
  inside-partnered (lobe) slot — delivering a lobe slot would require
  the cell itself to hold the slot's other end.
* **The lobe Gray lock** (`lobe_gray_lock`): while a cell is
  lobe-valued, *every* arrival is the Gray flip
  `reg := bar reg` — the delivered slot's partner is inside the cell,
  so it must equal the current register.  The register never leaves
  `{v₀, bar v₀}`: σ ≤ 2, with no hypothesis on writers, productivity,
  or `bar`-fixed-point-freeness.

On a periodic tail irreversibility becomes a dichotomy
(`lobe_or_cross`), and composed with the rho theorem
(`rho_gray_or_cross`): **on every run's eventual cycle, every cell is
a Gray flipper (register confined to a two-element bar-orbit) or its
register is foreign-partnered at every moment.**  Lemma B's remaining
work is confined to the foreign-valued cells.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Partner-held.**  At every step the bar of the arrival is the
current register of its own cell: a slot can only be delivered by
reading its partner out of that partner's cell. -/
theorem partner_held (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (k : Nat) :
    reg m e r0 k (m.cellOf (m.bar (e (k+1)))) = m.bar (e (k+1)) := by
  have hw := witness m e r0 hrun hr0 k
  rw [hw.1]
  exact hw.2

/-- **Irreversibility.**  A cell whose register is foreign-partnered
can never again hold a lobe slot: delivering an inside-partnered slot
would require the cell itself to hold its other end. -/
theorem cross_stays_cross (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {C t0 : Nat}
    (hcross : m.cellOf (m.bar (reg m e r0 t0 C)) ≠ C) :
    ∀ d, m.cellOf (m.bar (reg m e r0 (t0 + d) C)) ≠ C := by
  intro d
  induction d with
  | zero => exact hcross
  | succ n ih =>
      show m.cellOf (m.bar (reg m e r0 ((t0 + n) + 1) C)) ≠ C
      by_cases hc : m.cellOf (e (t0 + n + 1)) = C
      · intro hlobe
        have hw : reg m e r0 (t0 + n + 1) C = e (t0 + n + 1) :=
          reg_write m e r0 hc
        rw [hw] at hlobe
        have hheld := partner_held m e r0 hrun hr0 (t0 + n)
        rw [hlobe] at hheld
        apply ih
        rw [hheld, m.bar_invol, hc]
      · rw [reg_skip m e r0 hc]
        exact ih

private theorem reg_per_iter_from {K p : Nat}
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    {t : Nat} (ht : K ≤ t) :
    ∀ M c, reg m e r0 (t + M * p) c = reg m e r0 t c := by
  intro M c
  induction M with
  | zero => rw [Nat.zero_mul, Nat.add_zero]
  | succ n ih =>
      have h := hregper (t + n * p) c (by omega)
      have harith : t + (n + 1) * p = t + n * p + p := by
        rw [Nat.succ_mul]
        omega
      rw [harith, h]
      exact ih

/-- **The lobe dichotomy.**  On a periodic tail every cell is
lobe-valued at every moment or foreign-valued at every moment:
a lobe-to-foreign transition is irreversible, and periodicity forbids
irreversible transitions. -/
theorem lobe_or_cross (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {K p : Nat} (hp : 0 < p)
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    (C : Nat) :
    (∀ t, K ≤ t → m.cellOf (m.bar (reg m e r0 t C)) = C) ∨
    (∀ t, K ≤ t → m.cellOf (m.bar (reg m e r0 t C)) ≠ C) := by
  by_cases hex : ∃ t0, K ≤ t0 ∧
      m.cellOf (m.bar (reg m e r0 t0 C)) ≠ C
  · right
    obtain ⟨t0, ht0, hcross⟩ := hex
    intro t ht
    have hiter : reg m e r0 (t + t0 * p) C = reg m e r0 t C :=
      reg_per_iter_from m e r0 hregper ht t0 C
    have hbig : t0 ≤ t + t0 * p := by
      have h1 : t0 * 1 ≤ t0 * p := Nat.mul_le_mul_left _ hp
      omega
    obtain ⟨d, hd⟩ : ∃ d, t + t0 * p = t0 + d :=
      ⟨t + t0 * p - t0, by omega⟩
    have hc := cross_stays_cross m e r0 hrun hr0 hcross d
    rw [← hd] at hc
    rw [← hiter]
    exact hc
  · left
    intro t ht
    by_cases hl : m.cellOf (m.bar (reg m e r0 t C)) = C
    · exact hl
    · exact absurd ⟨t, ht, hl⟩ hex

/-- **The lobe Gray lock.**  A cell that is lobe-valued throughout
keeps its register in the two-element bar-orbit `{v₀, bar v₀}`:
delivering any slot requires its partner — here inside the cell — to
be the current register, so every arrival is the Gray flip.  σ ≤ 2,
unconditionally. -/
theorem lobe_gray_lock (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {C K : Nat}
    (hlobe : ∀ t, K ≤ t → m.cellOf (m.bar (reg m e r0 t C)) = C) :
    ∀ d, reg m e r0 (K + d) C = reg m e r0 K C ∨
      reg m e r0 (K + d) C = m.bar (reg m e r0 K C) := by
  intro d
  induction d with
  | zero => exact Or.inl rfl
  | succ n ih =>
      by_cases hc : m.cellOf (e (K + n + 1)) = C
      · have hv : reg m e r0 (K + n + 1) C = e (K + n + 1) :=
          reg_write m e r0 hc
        have hlnew : m.cellOf (m.bar (reg m e r0 (K + n + 1) C)) = C :=
          hlobe (K + n + 1) (by omega)
        rw [hv] at hlnew
        have hheld := partner_held m e r0 hrun hr0 (K + n)
        rw [hlnew] at hheld
        have hflip : reg m e r0 (K + n + 1) C
            = m.bar (reg m e r0 (K + n) C) := by
          rw [hv, hheld, m.bar_invol]
        rcases ih with h | h
        · right
          show reg m e r0 ((K + n) + 1) C = m.bar (reg m e r0 K C)
          rw [hflip, h]
        · left
          show reg m e r0 ((K + n) + 1) C = reg m e r0 K C
          rw [hflip, h, m.bar_invol]
      · rcases ih with h | h
        · left
          show reg m e r0 ((K + n) + 1) C = reg m e r0 K C
          rw [reg_skip m e r0 hc]
          exact h
        · right
          show reg m e r0 ((K + n) + 1) C = m.bar (reg m e r0 K C)
          rw [reg_skip m e r0 hc]
          exact h

/-- **Cross deliveries read foreign cells.**  Into a foreign-valued
cell, every arrival is fetched by reading a cell *other than* the
written cell itself: the delivered slot is the bar of a foreign
register.  For a two-writer tail this couples the cross cell entirely
to the other writer and the frozen rails. -/
theorem cross_delivery_reads_foreign (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {C K : Nat}
    (hcross : ∀ t, K ≤ t → m.cellOf (m.bar (reg m e r0 t C)) ≠ C)
    {t : Nat} (ht : K ≤ t) (hc : m.cellOf (e (t+1)) = C) :
    m.cellOf (m.bar (e (t+1))) ≠ C ∧
    e (t+1) = m.bar (reg m e r0 t (m.cellOf (m.bar (e (t+1))))) := by
  have hv : reg m e r0 (t+1) C = e (t+1) := reg_write m e r0 hc
  have hP : m.cellOf (m.bar (e (t+1))) ≠ C := by
    have h := hcross (t+1) (by omega)
    rw [hv] at h
    exact h
  refine ⟨hP, ?_⟩
  have hheld := partner_held m e r0 hrun hr0 t
  rw [hheld, m.bar_invol]

/-- **Every cycle cell is a Gray flipper or foreign-valued.**  On every
run's eventual cycle, each cell either keeps its register in the
two-element bar-orbit of its base value — the Gray pair, σ ≤ 2 — or
its register's partner lies outside the cell at every moment of the
tail.  Lemma B's remaining work is exactly the foreign-valued cells. -/
theorem rho_gray_or_cross (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat) (hnd : slots.Nodup)
    (hallcells : ∀ s, m.cellOf s ∈ cells)
    (hcells : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots) :
    ∃ K p, 0 < p ∧ K + p ≤ slots.length ^ (cells.length + 1) + 1 ∧
      (∀ t, K ≤ t → e (t + p) = e t) ∧
      ∀ C, (∀ t, K ≤ t →
          (reg m e r0 t C = reg m e r0 K C ∨
           reg m e r0 t C = m.bar (reg m e r0 K C))) ∨
        (∀ t, K ≤ t → m.cellOf (m.bar (reg m e r0 t C)) ≠ C) := by
  obtain ⟨K, p, hp, hbound, hper, hregper, _⟩ :=
    run_rho m e r0 hrun hr0 cells slots hnd hallcells hcells hregslots
  refine ⟨K, p, hp, hbound, hper, ?_⟩
  intro C
  rcases lobe_or_cross m e r0 hrun hr0 hp hregper C with hlobe | hcross
  · left
    intro t ht
    obtain ⟨d, rfl⟩ : ∃ d, t = K + d := ⟨t - K, by omega⟩
    exact lobe_gray_lock m e r0 hrun hr0 hlobe d
  · right
    exact hcross

end Echo
