import Periodicity

/-!
# The steering law: active cycles stand at active mouths

A cell is only ever *read* from its mouth partner: the step rule reads
the register of `star (cellOf (e t))`.  So if the walk never stands at
`star C` for any cell `C` of the writer set `S`, every read on the tail
is a frozen foreign register, any two same-cell visits have identical
futures (`no_stand_merge`), periodicity turns merged futures into equal
deliveries (`no_stand_arrivals_agree`), and every register — written or
not — freezes (`no_stand_freeze`); then nothing is productive at all
(`no_stand_quiet`).

Headline (`active_tail_stands_at_mouth`, composed with the rho theorem
in `rho_steering`): **every eventual cycle is completely quiet, or the
walk stands at the mouth partner of one of its active cells.**  For a
two-mouth cycle this says the walk physically visits `star C1` or
`star C2` — the mouth crossings of the dogbone bounce.  Unlike the
lone-writer theorem this needs neither the retrace palindrome nor
`bar`-fixed-point-freeness: the steering law is elementary; the
palindrome is only needed afterwards, to *kill* the stands when the
writer set is a single cell.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Registers of cells outside the writer set are frozen. -/
theorem writers_frozen_foreign {S : List Nat} {K : Nat}
    (hS : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) ∈ S)
    {W : Nat} (hW : W ∉ S) :
    ∀ t, K ≤ t → reg m e r0 t W = reg m e r0 K W := by
  intro t ht
  by_cases h : reg m e r0 t W = reg m e r0 K W
  · exact h
  · obtain ⟨s, hs1, _, hsp, hsc⟩ := change_has_productive_le m e r0 ht h
    have hcell := hS s hs1 hsp
    rw [hsc] at hcell
    exact absurd hcell hW

/-- **Merged futures without stands.**  If the walk never stands at the
mouth partner of a writer cell, any two same-cell visits have identical
futures: every read along the way is a frozen foreign register. -/
theorem no_stand_merge (hrun : IsRun m e r0)
    {S : List Nat} {K : Nat}
    (hS : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) ∈ S)
    (hnostand : ∀ v, K ≤ v → ∀ C ∈ S, m.cellOf (e v) ≠ m.star C)
    {u1 u2 : Nat} (h1 : K ≤ u1) (h2 : K ≤ u2)
    (hc : m.cellOf (e u1) = m.cellOf (e u2)) :
    ∀ d, 1 ≤ d → e (u1 + d) = e (u2 + d) := by
  have hRnotS : ∀ v, K ≤ v → m.star (m.cellOf (e v)) ∉ S := by
    intro v hv hmem
    have h := hnostand v hv _ hmem
    rw [m.star_invol] at h
    exact h rfl
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
        have hfor : m.star (m.cellOf (e (u2 + n))) ∉ S :=
          hRnotS (u2 + n) (by omega)
        rw [writers_frozen_foreign m e r0 hS hfor (u1 + n) (by omega),
          writers_frozen_foreign m e r0 hS hfor (u2 + n) (by omega)]
      · have hn0 : n = 0 := by omega
        subst hn0
        show e (u1 + 1) = e (u2 + 1)
        rw [hrun u1, hrun u2, hc]
        refine congrArg m.bar ?_
        have hfor : m.star (m.cellOf (e u2)) ∉ S := hRnotS u2 h2
        rw [writers_frozen_foreign m e r0 hS hfor u1 h1,
          writers_frozen_foreign m e r0 hS hfor u2 h2]

/-- **All same-cell deliveries agree without stands.**  On a periodic
stand-free tail, any two arrivals into the same cell deliver the same
slot. -/
theorem no_stand_arrivals_agree (hrun : IsRun m e r0)
    {S : List Nat} {K p : Nat} (hp : 0 < p)
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hS : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) ∈ S)
    (hnostand : ∀ v, K ≤ v → ∀ C ∈ S, m.cellOf (e v) ≠ m.star C)
    {t1 t2 : Nat} (h1 : K ≤ t1) (h2 : K ≤ t2)
    (hc : m.cellOf (e (t1+1)) = m.cellOf (e (t2+1))) :
    e (t1+1) = e (t2+1) := by
  have hm := no_stand_merge m e r0 hrun hS hnostand
    (show K ≤ t1+1 by omega) (show K ≤ t2+1 by omega) hc p hp
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

/-- **Every register freezes without stands** — written cells included:
each arrival is identified with the base register by a period-length
look-ahead. -/
theorem no_stand_register_freeze (hrun : IsRun m e r0)
    {S : List Nat} {K p : Nat} (hp : 0 < p)
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    (hS : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) ∈ S)
    (hnostand : ∀ v, K ≤ v → ∀ C ∈ S, m.cellOf (e v) ≠ m.star C) :
    ∀ (C : Nat) (d : Nat), reg m e r0 (K + d) C = reg m e r0 K C := by
  intro C d
  induction d with
  | zero => rfl
  | succ n ih =>
      by_cases hcell : m.cellOf (e (K + n + 1)) = C
      · have hwrite : reg m e r0 (K + n + 1) C = e (K + n + 1) :=
          reg_write m e r0 hcell
        have hlock : ∀ s, reg m e r0 (K + n + 1 + s) C = e (K + n + 1) := by
          intro s
          induction s with
          | zero => exact hwrite
          | succ q ihq =>
              show reg m e r0 ((K + n + 1 + q) + 1) C = e (K + n + 1)
              by_cases hcq : m.cellOf (e (K + n + 1 + q + 1)) = C
              · rw [reg_write m e r0 hcq]
                refine (no_stand_arrivals_agree m e r0 hrun hp hper hS
                  hnostand (show K ≤ K + n by omega)
                  (show K ≤ K + n + 1 + q by omega) ?_).symm
                rw [hcell, hcq]
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
        rw [reg_write m e r0 hcell]
        exact hval
      · show reg m e r0 ((K + n) + 1) C = reg m e r0 K C
        rw [reg_skip m e r0 hcell]
        exact ih

/-- Time-indexed form of the stand-free freeze. -/
theorem no_stand_freeze (hrun : IsRun m e r0)
    {S : List Nat} {K p : Nat} (hp : 0 < p)
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    (hS : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) ∈ S)
    (hnostand : ∀ v, K ≤ v → ∀ C ∈ S, m.cellOf (e v) ≠ m.star C) :
    ∀ t c, K ≤ t → reg m e r0 t c = reg m e r0 K c := by
  intro t c ht
  obtain ⟨d, rfl⟩ : ∃ d, t = K + d := ⟨t - K, by omega⟩
  exact no_stand_register_freeze m e r0 hrun hp hper hregper hS hnostand c d

/-- **A stand-free tail is silent.** -/
theorem no_stand_quiet (hrun : IsRun m e r0)
    {S : List Nat} {K p : Nat} (hp : 0 < p)
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    (hS : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) ∈ S)
    (hnostand : ∀ v, K ≤ v → ∀ C ∈ S, m.cellOf (e v) ≠ m.star C) :
    ∀ t, K ≤ t → ¬ ProductiveStep m e r0 t := by
  intro t ht hprod
  apply hprod
  have hw : reg m e r0 (t+1) (m.cellOf (e (t+1))) = e (t+1) :=
    reg_write m e r0 rfl
  have h1 := no_stand_freeze m e r0 hrun hp hper hregper hS hnostand
    (t+1) (m.cellOf (e (t+1))) (by omega)
  have h2 := no_stand_freeze m e r0 hrun hp hper hregper hS hnostand
    t (m.cellOf (e (t+1))) ht
  exact hw.symm.trans (h1.trans h2.symm)

/-- **The steering law.**  On a periodic tail whose productive steps all
write into cells of `S`: either there is no productive step at all, or
the walk stands at the mouth partner of some cell of `S`. -/
theorem active_tail_stands_at_mouth (hrun : IsRun m e r0)
    {S : List Nat} {K p : Nat} (hp : 0 < p)
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    (hS : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) ∈ S) :
    (∀ t, K ≤ t → ¬ ProductiveStep m e r0 t) ∨
    (∃ v C, K ≤ v ∧ C ∈ S ∧ m.cellOf (e v) = m.star C) := by
  by_cases hstand : ∃ v C, K ≤ v ∧ C ∈ S ∧ m.cellOf (e v) = m.star C
  · exact Or.inr hstand
  · refine Or.inl (no_stand_quiet m e r0 hrun hp hper hregper hS ?_)
    intro v hv C hC h
    exact hstand ⟨v, C, hv, hC, h⟩

/-- **The stand delivery.**  Standing at `star C`, the walk reads `C`
itself and jumps to the bar of its register: stands are exactly the
moments a writer cell's variation is fetched. -/
theorem stand_delivery (hrun : IsRun m e r0) {C v : Nat}
    (hstand : m.cellOf (e v) = m.star C) :
    e (v+1) = m.bar (reg m e r0 v C) := by
  rw [hrun v, hstand, m.star_invol]

/-- **Stand entries are frozen.**  If `star C` is not itself a writer
cell, every arrival at `star C` on the tail is unproductive and lands
on its frozen register: all stands at `star C` carry one fixed entry.
The cycle is rails between stands — and the stands all look alike;
only the delivery `bar (reg C)` varies. -/
theorem stand_entry_frozen {S : List Nat} {K : Nat}
    (hS : ∀ t, K ≤ t → ProductiveStep m e r0 t →
      m.cellOf (e (t+1)) ∈ S)
    {C : Nat} (hCS : m.star C ∉ S)
    {v : Nat} (hv : K + 1 ≤ v) (hstand : m.cellOf (e v) = m.star C) :
    e v = reg m e r0 K (m.star C) := by
  obtain ⟨u, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
  have hK : K ≤ u := by omega
  have hunprod : e (u+1) = reg m e r0 u (m.cellOf (e (u+1))) := by
    by_cases hq : e (u+1) = reg m e r0 u (m.cellOf (e (u+1)))
    · exact hq
    · exfalso
      have hmem := hS u hK hq
      rw [hstand] at hmem
      exact hCS hmem
  rw [hunprod, hstand]
  exact writers_frozen_foreign m e r0 hS hCS u hK

/-- **The stand flip.**  If the delivery fetched at a stand lands back
in the writer cell — the register is a lobe slot — the arrival is the
Gray move: `C`'s register flips to its bar. -/
theorem stand_flip (hrun : IsRun m e r0) {C v : Nat}
    (hstand : m.cellOf (e v) = m.star C)
    (hback : m.cellOf (m.bar (reg m e r0 v C)) = C) :
    reg m e r0 (v+1) C = m.bar (reg m e r0 v C) := by
  have hdel := stand_delivery m e r0 hrun hstand
  have hcell : m.cellOf (e (v+1)) = C := by
    rw [hdel]
    exact hback
  rw [reg_write m e r0 hcell, hdel]

/-- **The Gray lock.**  If every arrival into `C` on the tail delivers
the bar of `C`'s current register — the self-flip — then `C`'s register
stays in the two-element orbit `{v₀, bar v₀}` forever: `σ(C) ≤ 2`,
the two-value half of lemma B for pure flipper cells. -/
theorem flip_lock {C K : Nat}
    (hflip : ∀ t, K ≤ t → m.cellOf (e (t+1)) = C →
      e (t+1) = m.bar (reg m e r0 t C)) :
    ∀ d, reg m e r0 (K + d) C = reg m e r0 K C ∨
      reg m e r0 (K + d) C = m.bar (reg m e r0 K C) := by
  intro d
  induction d with
  | zero => exact Or.inl rfl
  | succ n ih =>
      by_cases hc : m.cellOf (e (K + n + 1)) = C
      · have harr := hflip (K + n) (Nat.le_add_right _ _) hc
        have hw : reg m e r0 (K + n + 1) C = e (K + n + 1) :=
          reg_write m e r0 hc
        rcases ih with h | h
        · right
          show reg m e r0 ((K + n) + 1) C = m.bar (reg m e r0 K C)
          rw [hw, harr, h]
        · left
          show reg m e r0 ((K + n) + 1) C = reg m e r0 K C
          rw [hw, harr, h, m.bar_invol]
      · rcases ih with h | h
        · left
          show reg m e r0 ((K + n) + 1) C = reg m e r0 K C
          rw [reg_skip m e r0 hc]
          exact h
        · right
          show reg m e r0 ((K + n) + 1) C = m.bar (reg m e r0 K C)
          rw [reg_skip m e r0 hc]
          exact h

/-- **The rho steering law.**  Every run whose productive steps write
into cells of `S` reaches an eventual cycle that is either completely
quiet or stands at the mouth partner of an active cell.  For
`S = [C1, C2]` this is the two-mouth case: an active two-mouth cycle
physically visits `star C1` or `star C2` — the mouth crossings of the
dogbone bounce. -/
theorem rho_steering (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat) (hnd : slots.Nodup)
    (hallcells : ∀ s, m.cellOf s ∈ cells)
    (hcells : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots)
    (S : List Nat)
    (hS : ∀ t, ProductiveStep m e r0 t → m.cellOf (e (t+1)) ∈ S) :
    ∃ K p, 0 < p ∧ K + p ≤ slots.length ^ (cells.length + 1) + 1 ∧
      (∀ t, K ≤ t → e (t + p) = e t) ∧
      ((∀ t, K ≤ t → ¬ ProductiveStep m e r0 t) ∨
       (∃ v C, K ≤ v ∧ C ∈ S ∧ m.cellOf (e v) = m.star C)) := by
  obtain ⟨K, p, hp, hbound, hper, hregper, _⟩ :=
    run_rho m e r0 hrun hr0 cells slots hnd hallcells hcells hregslots
  exact ⟨K, p, hp, hbound, hper,
    active_tail_stands_at_mouth m e r0 hrun hp hper hregper
      (fun t _ hpt => hS t hpt)⟩

end Echo
