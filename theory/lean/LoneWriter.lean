import Periodicity

/-!
# The lone writer freezes: m ≠ 1 on cycles

Suppose every productive step of a tail writes into a single cell `C`.
Then:

* every other cell's register is frozen (`lone_frozen_foreign`);
* after any visit to `C` the walk never stands at `C`'s mouth partner
  (`lone_no_partner`, by the retrace palindrome `lone_write_no_mouth`) —
  so the walk never *reads* `C`: a cell is read only from its partner;
* hence any two visits to `C` have identical futures (`lone_merge`):
  every read along the way is a frozen foreign register;
* on a periodic tail this forces all deliveries into `C` to agree
  (`lone_arrivals_agree`): the delivered slot is a period-length
  look-ahead of a merged future;
* so `C`'s own register is frozen too (`lone_register_freeze`,
  `lone_writer_freeze`) — and then nothing is productive at all
  (`lone_writer_quiet`).

Composed with `run_rho`, this yields the dynamic half of the one-mouth
theorem, machine-checked for every machine, every run, every `N`
(`rho_quiet_or_two_mouths`): **every eventual cycle is either
completely quiet or steered from at least two distinct cells.**
A cycle with exactly one active mouth is impossible.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- If every productive step from `K` on writes into `C`, every other
cell's register is frozen from `K` on. -/
theorem lone_frozen_foreign {C K : Nat}
    (hlone : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) = C)
    {W : Nat} (hW : W ≠ C) :
    ∀ t, K ≤ t → reg m e r0 t W = reg m e r0 K W := by
  intro t ht
  by_cases h : reg m e r0 t W = reg m e r0 K W
  · exact h
  · obtain ⟨s, hs1, _, hsp, hsc⟩ := change_has_productive_le m e r0 ht h
    have hcell := hlone s hs1 hsp
    rw [hsc] at hcell
    exact absurd hcell hW

/-- After any visit to `C`, the lone written cell, the walk never
stands at `C`'s mouth partner: the lone writer cannot fetch its own
variation. -/
theorem lone_no_partner (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (hbar : ∀ s, m.bar s ≠ s)
    {C K : Nat}
    (hlone : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) = C)
    {i : Nat} (hi : K ≤ i) (hC : m.cellOf (e i) = C) :
    ∀ q, m.cellOf (e (i + q)) ≠ m.star C := by
  intro q
  have hside : ∀ t, i ≤ t → t < i + q → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) = m.cellOf (e i) := by
    intro t ht1 _ hp
    rw [hC]
    exact hlone t (by omega) hp
  have h := lone_write_no_mouth m e r0 hrun hr0 hbar q i hside
  rw [hC] at h
  exact h

/-- **Merged futures.**  Any two visits to the lone written cell have
identical futures: every read along the way is a frozen foreign
register — reading `C` itself would put the walk at `star C`, which
`lone_no_partner` forbids. -/
theorem lone_merge (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (hbar : ∀ s, m.bar s ≠ s)
    {C K : Nat}
    (hlone : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) = C)
    {u1 u2 : Nat} (h1 : K ≤ u1) (h2 : K ≤ u2)
    (hc1 : m.cellOf (e u1) = C) (hc2 : m.cellOf (e u2) = C) :
    ∀ d, 1 ≤ d → e (u1 + d) = e (u2 + d) := by
  intro d
  induction d with
  | zero => intro h; omega
  | succ n ih =>
      intro _
      by_cases hn : 1 ≤ n
      · have hen := ih hn
        show e ((u1 + n) + 1) = e ((u2 + n) + 1)
        rw [hrun (u1 + n), hrun (u2 + n), hen]
        refine congrArg m.bar ?_
        have hread : m.star (m.cellOf (e (u2 + n))) ≠ C := by
          intro h
          have hcell : m.cellOf (e (u2 + n)) = m.star C := by
            rw [← h, m.star_invol]
          have hcell1 : m.cellOf (e (u1 + n)) = m.star C := by
            rw [hen]
            exact hcell
          exact lone_no_partner m e r0 hrun hr0 hbar hlone h1 hc1 n hcell1
        rw [lone_frozen_foreign m e r0 hlone hread (u1 + n) (by omega),
          lone_frozen_foreign m e r0 hlone hread (u2 + n) (by omega)]
      · have hn0 : n = 0 := by omega
        subst hn0
        show e (u1 + 1) = e (u2 + 1)
        rw [hrun u1, hrun u2, hc1, hc2]
        refine congrArg m.bar ?_
        rw [lone_frozen_foreign m e r0 hlone (m.star_ne C) u1 h1,
          lone_frozen_foreign m e r0 hlone (m.star_ne C) u2 h2]

/-- **All deliveries agree.**  On a periodic tail whose productive
steps all write into `C`, any two arrivals into `C` deliver the same
slot: the delivered value is a period-length look-ahead of a merged
future. -/
theorem lone_arrivals_agree (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (hbar : ∀ s, m.bar s ≠ s)
    {C K p : Nat} (hp : 0 < p)
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hlone : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) = C)
    {t1 t2 : Nat} (h1 : K ≤ t1) (h2 : K ≤ t2)
    (hc1 : m.cellOf (e (t1+1)) = C) (hc2 : m.cellOf (e (t2+1)) = C) :
    e (t1+1) = e (t2+1) := by
  have hm := lone_merge m e r0 hrun hr0 hbar hlone
    (show K ≤ t1+1 by omega) (show K ≤ t2+1 by omega) hc1 hc2 p hp
  rw [hper (t1+1) (by omega), hper (t2+1) (by omega)] at hm
  exact hm

private theorem reg_per_iter {K p : Nat}
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c) :
    ∀ M c, reg m e r0 (K + M * p) c = reg m e r0 K c := by
  intro M c
  induction M with
  | zero => rw [Nat.zero_mul, Nat.add_zero]
  | succ n ih =>
      have h := hregper (K + n * p) c (Nat.le_add_right _ _)
      have harith : K + (n + 1) * p = K + n * p + p := by
        rw [Nat.succ_mul]
        omega
      rw [harith, h]
      exact ih

/-- **The lone writer's register freezes.**  On a periodic tail whose
productive steps all write into `C`, even `C`'s register is constant:
all deliveries agree, and a periodic copy of the base register
identifies the delivered value with the base value. -/
theorem lone_register_freeze (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (hbar : ∀ s, m.bar s ≠ s)
    {C K p : Nat} (hp : 0 < p)
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    (hlone : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) = C) :
    ∀ d, reg m e r0 (K + d) C = reg m e r0 K C := by
  intro d
  induction d with
  | zero => rfl
  | succ n ih =>
      by_cases hc : m.cellOf (e (K + n + 1)) = C
      · have hwrite : reg m e r0 (K + n + 1) C = e (K + n + 1) :=
          reg_write m e r0 hc
        have hlock : ∀ s, reg m e r0 (K + n + 1 + s) C = e (K + n + 1) := by
          intro s
          induction s with
          | zero => exact hwrite
          | succ q ihq =>
              show reg m e r0 ((K + n + 1 + q) + 1) C = e (K + n + 1)
              by_cases hcq : m.cellOf (e (K + n + 1 + q + 1)) = C
              · rw [reg_write m e r0 hcq]
                exact (lone_arrivals_agree m e r0 hrun hr0 hbar hp hper
                  hlone (show K ≤ K + n by omega)
                  (show K ≤ K + n + 1 + q by omega) hc hcq).symm
              · rw [reg_skip m e r0 hcq]
                exact ihq
        have hbase : reg m e r0 (K + (n + 2) * p) C = reg m e r0 K C :=
          reg_per_iter m e r0 hregper (n + 2) C
        have hmul : (n + 2) * 1 ≤ (n + 2) * p := Nat.mul_le_mul_left _ hp
        have hfar : K + n + 1 ≤ K + (n + 2) * p := by omega
        obtain ⟨s0, hs0⟩ : ∃ s0, K + (n + 2) * p = K + n + 1 + s0 :=
          ⟨K + (n + 2) * p - (K + n + 1), by omega⟩
        have hend := hlock s0
        rw [← hs0] at hend
        have hval : e (K + n + 1) = reg m e r0 K C := by
          rw [← hend]
          exact hbase
        show reg m e r0 ((K + n) + 1) C = reg m e r0 K C
        rw [reg_write m e r0 hc]
        exact hval
      · show reg m e r0 ((K + n) + 1) C = reg m e r0 K C
        rw [reg_skip m e r0 hc]
        exact ih

/-- **Full freeze.**  On a lone-writer periodic tail every register of
every cell is constant. -/
theorem lone_writer_freeze (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (hbar : ∀ s, m.bar s ≠ s)
    {C K p : Nat} (hp : 0 < p)
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    (hlone : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) = C) :
    ∀ t c, K ≤ t → reg m e r0 t c = reg m e r0 K c := by
  intro t c ht
  by_cases hcC : c = C
  · subst hcC
    obtain ⟨d, rfl⟩ : ∃ d, t = K + d := ⟨t - K, by omega⟩
    exact lone_register_freeze m e r0 hrun hr0 hbar hp hper hregper hlone d
  · exact lone_frozen_foreign m e r0 hlone hcC t ht

/-- **The lone writer is silent.**  A periodic tail cannot have all its
productive steps writing a single cell: it then has no productive step
at all. -/
theorem lone_writer_quiet (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (hbar : ∀ s, m.bar s ≠ s)
    {C K p : Nat} (hp : 0 < p)
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    (hlone : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) = C) :
    ∀ t, K ≤ t → ¬ ProductiveStep m e r0 t := by
  intro t ht hprod
  have hcell := hlone t ht hprod
  have hw : reg m e r0 (t+1) C = e (t+1) := reg_write m e r0 hcell
  have h1 : reg m e r0 (t+1) C = reg m e r0 K C :=
    lone_writer_freeze m e r0 hrun hr0 hbar hp hper hregper hlone
      (t+1) C (by omega)
  have h2 : reg m e r0 t C = reg m e r0 K C :=
    lone_writer_freeze m e r0 hrun hr0 hbar hp hper hregper hlone t C ht
  apply hprod
  rw [hcell, ← hw, h1, ← h2]

/-- **Quiet or two mouths.**  Every run's eventual cycle either
contains no productive step at all — the machine froze — or its
productive steps write into at least two distinct cells.  A cycle
steered from a single cell is impossible: `m ≠ 1`, machine-checked for
every machine, every run, every `N`. -/
theorem rho_quiet_or_two_mouths (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (hbar : ∀ s, m.bar s ≠ s)
    (cells slots : List Nat) (hnd : slots.Nodup)
    (hallcells : ∀ s, m.cellOf s ∈ cells)
    (hcells : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots) :
    ∃ K p, 0 < p ∧ K + p ≤ slots.length ^ (cells.length + 1) + 1 ∧
      (∀ t, K ≤ t → e (t + p) = e t) ∧
      ((∀ t, K ≤ t → ¬ ProductiveStep m e r0 t) ∨
       (∃ t1 t2, K ≤ t1 ∧ K ≤ t2 ∧ ProductiveStep m e r0 t1 ∧
         ProductiveStep m e r0 t2 ∧
         m.cellOf (e (t1+1)) ≠ m.cellOf (e (t2+1)))) := by
  obtain ⟨K, p, hp, hbound, hper, hregper, _⟩ :=
    run_rho m e r0 hrun hr0 cells slots hnd hallcells hcells hregslots
  refine ⟨K, p, hp, hbound, hper, ?_⟩
  by_cases hex : ∃ t, K ≤ t ∧ ProductiveStep m e r0 t
  · obtain ⟨t0, ht0, hprod0⟩ := hex
    by_cases htwo : ∃ t1, K ≤ t1 ∧ ProductiveStep m e r0 t1 ∧
        m.cellOf (e (t1+1)) ≠ m.cellOf (e (t0+1))
    · obtain ⟨t1, h1, hp1, hne⟩ := htwo
      exact Or.inr ⟨t0, t1, ht0, h1, hprod0, hp1, fun h => hne h.symm⟩
    · exfalso
      have hlone : ∀ t, K ≤ t → ProductiveStep m e r0 t →
          m.cellOf (e (t+1)) = m.cellOf (e (t0+1)) := by
        intro t ht hpt
        by_cases hcc : m.cellOf (e (t+1)) = m.cellOf (e (t0+1))
        · exact hcc
        · exact absurd ⟨t, ht, hpt, hcc⟩ htwo
      exact lone_writer_quiet m e r0 hrun hr0 hbar hp hper hregper hlone
        t0 ht0 hprod0
  · refine Or.inl ?_
    intro t ht hpt
    exact hex ⟨t, ht, hpt⟩

end Echo
