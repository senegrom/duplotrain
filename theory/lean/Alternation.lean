import Periodicity

/-!
# The alternation seed: consecutive same-cell writes force a mouth visit

The abstract exhaustion (`../tools/baltern.py`, 265,525 active cycles, no
exception) shows the **four-beat law**: every active cycle has exactly four
productive writes per period, strictly alternating between its two active
cells.  This file proves the seed of that law.

If two *consecutive* productive steps (no productive step between them)
write the same cell `C`, and the walk avoids both `C` and `star C`
strictly between the two arrivals, then the stretch after the second
write **replays** the stretch after the first: every read along the way
is the same frozen register, the wrap step re-delivers the same slot
unproductively, and the machine closes a completely quiet loop.  On a
periodic tail that contradicts the periodic recurrence of the second
write itself (`productive_periodic`).

Headline (`consecutive_same_write_visits`): **between two consecutive
productive writes of the same cell, the walk must stand in the written
cell or at its mouth partner.**  In particular two *adjacent* productive
steps never write the same cell.  This is the entry point for the
four-beat alternation of lemma B.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Productivity is a function of the periodic data: on a tail with
periodic entries and registers, productive steps recur with the period. -/
theorem productive_periodic {K p : Nat}
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    {t : Nat} (ht : K ≤ t) :
    ProductiveStep m e r0 (t + p) ↔ ProductiveStep m e r0 t := by
  unfold ProductiveStep
  have he : e ((t + p) + 1) = e (t + 1) := by
    have h := hper (t + 1) (by omega)
    have harith : (t + 1) + p = (t + p) + 1 := by omega
    rw [harith] at h
    exact h
  rw [he, hregper t _ ht]

/-- Iterated state replay: a state coincidence at distance `q` repeats at
every multiple of `q`. -/
theorem state_replay_iter (hrun : IsRun m e r0) (cells : List Nat)
    (hcells : ∀ k, m.star (m.cellOf (e k)) ∈ cells) {i q : Nat}
    (h : stateCode m e r0 cells i = stateCode m e r0 cells (i + q)) :
    ∀ M n, stateCode m e r0 cells (i + n) =
      stateCode m e r0 cells (i + M * q + n) := by
  intro M
  induction M with
  | zero =>
      intro n
      rw [Nat.zero_mul, Nat.add_zero]
  | succ M ih =>
      intro n
      have h1 := ih n
      have h2 := state_replay m e r0 hrun cells hcells h (M * q + n)
      have e1 : i + M * q + n = i + (M * q + n) := by omega
      have e2 : i + q + (M * q + n) = i + (M + 1) * q + n := by
        rw [Nat.succ_mul]
        omega
      rw [e1] at h1
      rw [e2] at h2
      exact h1.trans h2

/-- Productivity transfers along equal states. -/
theorem productive_iff_of_state_eq (hrun : IsRun m e r0)
    (cells : List Nat)
    (hcells : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    (hallcells : ∀ s, m.cellOf s ∈ cells) {i j : Nat}
    (h : stateCode m e r0 cells i = stateCode m e r0 cells j) :
    (ProductiveStep m e r0 i ↔ ProductiveStep m e r0 j) := by
  have hnext := state_step m e r0 hrun cells hcells h
  have he : e (i + 1) = e (j + 1) :=
    stateCode_entry_eq m e r0 cells hnext
  have hreg : reg m e r0 i (m.cellOf (e (j + 1)))
      = reg m e r0 j (m.cellOf (e (j + 1))) :=
    stateCode_reg_eq m e r0 cells h _ (hallcells (e (j + 1)))
  unfold ProductiveStep
  rw [he, hreg]

/-- **The replay invariant.**  Between consecutive productive writes of
the same cell `C`, with the walk avoiding `C` and `star C` strictly
inside the window, the stretch after the second write replays the
stretch after the first: entries coincide from offset 1 on, foreign
registers agree, `C`'s register holds the second delivery, and no
productive step occurs after the second write within the window. -/
theorem consecutive_replay (hrun : IsRun m e r0)
    {C t1 t2 : Nat} (h12 : t1 < t2)
    (hq : ∀ s, t1 < s → s < t2 → ¬ ProductiveStep m e r0 s)
    (hc1 : m.cellOf (e (t1 + 1)) = C)
    (hc2 : m.cellOf (e (t2 + 1)) = C)
    (havoid : ∀ l, 1 ≤ l → l ≤ t2 - t1 - 1 →
      m.cellOf (e (t1 + 1 + l)) ≠ C ∧
      m.cellOf (e (t1 + 1 + l)) ≠ m.star C) :
    ∀ d, d ≤ t2 - t1 - 1 →
      (1 ≤ d → e (t2 + 1 + d) = e (t1 + 1 + d)) ∧
      (∀ c, c ≠ C →
        reg m e r0 (t2 + 1 + d) c = reg m e r0 (t1 + 1 + d) c) ∧
      reg m e r0 (t2 + 1 + d) C = e (t2 + 1) ∧
      (∀ s, s < d → ¬ ProductiveStep m e r0 (t2 + 1 + s)) := by
  have hqreg : ∀ d, t1 + 1 + d ≤ t2 →
      ∀ c, reg m e r0 (t1 + 1 + d) c = reg m e r0 (t1 + 1) c := by
    intro d hd c
    have h := quiet_reg m e r0 (i := t1 + 1) d
      (fun t ht1 ht2 => hq t (by omega) (by omega)) c
    exact h
  intro d
  induction d with
  | zero =>
      intro _
      refine ⟨fun h1 => absurd h1 (by omega), ?_, ?_, ?_⟩
      · intro c hc
        have hskip : reg m e r0 (t2 + 1) c = reg m e r0 t2 c := by
          apply reg_skip
          rw [hc2]
          exact fun h => hc h.symm
        have hq2 : reg m e r0 t2 c = reg m e r0 (t1 + 1) c := by
          have harith : t2 = t1 + 1 + (t2 - t1 - 1) := by omega
          rw [harith]
          exact hqreg (t2 - t1 - 1) (by omega) c
        show reg m e r0 (t2 + 1) c = reg m e r0 (t1 + 1) c
        rw [hskip]
        exact hq2
      · show reg m e r0 (t2 + 1) C = e (t2 + 1)
        exact reg_write m e r0 hc2
      · intro s hs
        exact absurd hs (by omega)
  | succ n ih =>
      intro hn1
      obtain ⟨hent, hreg, hregC, hquiet2⟩ := ih (by omega)
      -- position of the walk at offset n (both sides)
      -- the read cell at offset n is not C
      have hposC : m.cellOf (e (t1 + 1 + n)) = C ∨
          (m.cellOf (e (t1 + 1 + n)) ≠ C ∧
           m.cellOf (e (t1 + 1 + n)) ≠ m.star C) := by
        by_cases hn0 : n = 0
        · left
          rw [hn0, Nat.add_zero]
          exact hc1
        · right
          exact havoid n (by omega) (by omega)
      have hRneC : m.star (m.cellOf (e (t1 + 1 + n))) ≠ C := by
        rcases hposC with hp | hp
        · rw [hp]
          exact m.star_ne C
        · intro h
          apply hp.2
          rw [← h, m.star_invol]
      -- entries at offset n agree (n = 0: both cells are C-arrivals)
      have hentn : m.cellOf (e (t2 + 1 + n)) = m.cellOf (e (t1 + 1 + n))
          ∧ m.star (m.cellOf (e (t2 + 1 + n)))
            = m.star (m.cellOf (e (t1 + 1 + n))) := by
        by_cases hn0 : n = 0
        · subst hn0
          constructor
          · rw [Nat.add_zero, Nat.add_zero, hc1, hc2]
          · rw [Nat.add_zero, Nat.add_zero, hc1, hc2]
        · have h := hent (by omega)
          rw [h]
          exact ⟨rfl, rfl⟩
      -- the new entry replays
      have hnew : e (t2 + 1 + (n + 1)) = e (t1 + 1 + (n + 1)) := by
        show e ((t2 + 1 + n) + 1) = e ((t1 + 1 + n) + 1)
        rw [hrun (t2 + 1 + n), hrun (t1 + 1 + n), hentn.2]
        refine congrArg m.bar ?_
        exact hreg _ hRneC
      -- the u1-side step at offset n is unproductive
      have hstep1 : e ((t1 + 1 + n) + 1) =
          reg m e r0 (t1 + 1 + n) (m.cellOf (e ((t1 + 1 + n) + 1))) := by
        by_cases hp : ProductiveStep m e r0 (t1 + 1 + n)
        · exact absurd hp (hq (t1 + 1 + n) (by omega) (by omega))
        · by_cases he : e ((t1 + 1 + n) + 1) =
              reg m e r0 (t1 + 1 + n) (m.cellOf (e ((t1 + 1 + n) + 1)))
          · exact he
          · exact absurd he hp
      -- the arrival cell at offset n+1 is not C
      have hAneC : m.cellOf (e (t1 + 1 + (n + 1))) ≠ C :=
        (havoid (n + 1) (by omega) (by omega)).1
      -- the u2-side step at offset n is unproductive too
      have hstep2 : e ((t2 + 1 + n) + 1) =
          reg m e r0 (t2 + 1 + n) (m.cellOf (e ((t2 + 1 + n) + 1))) := by
        have hA2 : m.cellOf (e ((t2 + 1 + n) + 1))
            = m.cellOf (e ((t1 + 1 + n) + 1)) := by
          show m.cellOf (e (t2 + 1 + (n + 1)))
              = m.cellOf (e (t1 + 1 + (n + 1)))
          rw [hnew]
        rw [hA2]
        have hval : reg m e r0 (t2 + 1 + n)
            (m.cellOf (e ((t1 + 1 + n) + 1)))
            = reg m e r0 (t1 + 1 + n)
              (m.cellOf (e ((t1 + 1 + n) + 1))) :=
          hreg _ hAneC
        rw [hval]
        show e (t2 + 1 + (n + 1)) =
          reg m e r0 (t1 + 1 + n) (m.cellOf (e ((t1 + 1 + n) + 1)))
        rw [hnew]
        exact hstep1
      have hstall2 := unproductive_stall m e r0 (t2 + 1 + n) hstep2
      have hstall1 := unproductive_stall m e r0 (t1 + 1 + n) hstep1
      refine ⟨fun _ => hnew, ?_, ?_, ?_⟩
      · intro c hc
        show reg m e r0 ((t2 + 1 + n) + 1) c
            = reg m e r0 ((t1 + 1 + n) + 1) c
        rw [hstall2 c, hstall1 c]
        exact hreg c hc
      · show reg m e r0 ((t2 + 1 + n) + 1) C = e (t2 + 1)
        rw [hstall2 C]
        exact hregC
      · intro s hs
        by_cases hsn : s < n
        · exact hquiet2 s hsn
        · have hsn' : s = n := by omega
          subst hsn'
          intro hp
          exact hp hstep2

/-- **The quiet loop.**  With full avoidance the wrap step re-delivers
the second write's own slot unproductively: the state at the end of the
replayed window equals the state right after the second write, and the
whole window after the second write is productive-free. -/
theorem consecutive_avoid_loop (hrun : IsRun m e r0)
    (cells : List Nat)
    {C t1 t2 : Nat} (h12 : t1 < t2)
    (hq : ∀ s, t1 < s → s < t2 → ¬ ProductiveStep m e r0 s)
    (hc1 : m.cellOf (e (t1 + 1)) = C)
    (hc2 : m.cellOf (e (t2 + 1)) = C)
    (havoid : ∀ l, 1 ≤ l → l ≤ t2 - t1 - 1 →
      m.cellOf (e (t1 + 1 + l)) ≠ C ∧
      m.cellOf (e (t1 + 1 + l)) ≠ m.star C) :
    stateCode m e r0 cells (t2 + 1) =
      stateCode m e r0 cells (t2 + 1 + (t2 - t1)) ∧
    (∀ s, s < t2 - t1 → ¬ ProductiveStep m e r0 (t2 + 1 + s)) := by
  obtain ⟨D, hD⟩ : ∃ D, D = t2 - t1 - 1 := ⟨t2 - t1 - 1, rfl⟩
  obtain ⟨hent, hreg, hregC, hquiet2⟩ :=
    consecutive_replay m e r0 hrun h12 hq hc1 hc2 havoid D (by omega)
  -- the wrap step at offset D
  have hposwrap : m.cellOf (e (t1 + 1 + D)) = C ∨
      (m.cellOf (e (t1 + 1 + D)) ≠ C ∧
       m.cellOf (e (t1 + 1 + D)) ≠ m.star C) := by
    by_cases hD0 : D = 0
    · left
      rw [hD0, Nat.add_zero]
      exact hc1
    · right
      exact havoid D (by omega) (by omega)
  have hRneC : m.star (m.cellOf (e (t1 + 1 + D))) ≠ C := by
    rcases hposwrap with hp | hp
    · rw [hp]
      exact m.star_ne C
    · intro h
      apply hp.2
      rw [← h, m.star_invol]
  have hentD : m.cellOf (e (t2 + 1 + D)) = m.cellOf (e (t1 + 1 + D))
      ∧ m.star (m.cellOf (e (t2 + 1 + D)))
        = m.star (m.cellOf (e (t1 + 1 + D))) := by
    by_cases hD0 : D = 0
    · subst hD0
      constructor
      · rw [Nat.add_zero, Nat.add_zero, hc1, hc2]
      · rw [Nat.add_zero, Nat.add_zero, hc1, hc2]
    · have h := hent (by omega)
      rw [h]
      exact ⟨rfl, rfl⟩
  -- the u1-side wrap step is exactly the second write: t1+1+D = t2
  have ht1D : t1 + 1 + D = t2 := by omega
  -- the wrap entry re-delivers the second write's slot
  have hwrap : e (t2 + 1 + (D + 1)) = e (t2 + 1) := by
    show e ((t2 + 1 + D) + 1) = e (t2 + 1)
    rw [hrun (t2 + 1 + D), hentD.2]
    have hval : reg m e r0 (t2 + 1 + D)
        (m.star (m.cellOf (e (t1 + 1 + D))))
        = reg m e r0 (t1 + 1 + D)
          (m.star (m.cellOf (e (t1 + 1 + D)))) :=
      hreg _ hRneC
    rw [hval, ht1D]
    exact (hrun t2).symm
  -- the wrap step is unproductive
  have hwrapstep : e ((t2 + 1 + D) + 1) =
      reg m e r0 (t2 + 1 + D) (m.cellOf (e ((t2 + 1 + D) + 1))) := by
    have h1 : e ((t2 + 1 + D) + 1) = e (t2 + 1) := hwrap
    rw [h1, hc2]
    exact hregC.symm
  have hstall := unproductive_stall m e r0 (t2 + 1 + D) hwrapstep
  have hDD : D + 1 = t2 - t1 := by omega
  constructor
  · -- state match
    have hentry : e (t2 + 1 + (t2 - t1)) = e (t2 + 1) := by
      rw [← hDD]
      exact hwrap
    have hregs : ∀ c, reg m e r0 (t2 + 1 + (t2 - t1)) c
        = reg m e r0 (t2 + 1) c := by
      intro c
      have h1 : reg m e r0 (t2 + 1 + (t2 - t1)) c
          = reg m e r0 (t2 + 1 + D) c := by
        rw [← hDD]
        show reg m e r0 ((t2 + 1 + D) + 1) c = reg m e r0 (t2 + 1 + D) c
        exact hstall c
      rw [h1]
      by_cases hc : c = C
      · subst hc
        rw [hregC]
        exact (reg_write m e r0 hc2).symm
      · have h2 := hreg c hc
        rw [h2, ht1D]
        have h3 : reg m e r0 (t2 + 1) c = reg m e r0 t2 c := by
          apply reg_skip
          rw [hc2]
          exact fun h => hc h.symm
        rw [h3]
    show stateCode m e r0 cells (t2 + 1)
        = stateCode m e r0 cells (t2 + 1 + (t2 - t1))
    have hmap : cells.map (reg m e r0 (t2 + 1))
        = cells.map (reg m e r0 (t2 + 1 + (t2 - t1))) := by
      apply List.map_congr_left
      intro c _
      exact (hregs c).symm
    show e (t2 + 1) :: cells.map (reg m e r0 (t2 + 1))
        = e (t2 + 1 + (t2 - t1))
          :: cells.map (reg m e r0 (t2 + 1 + (t2 - t1)))
    rw [hentry, hmap]
  · -- quiet window
    intro s hs
    by_cases hsD : s < D
    · exact hquiet2 s hsD
    · have hsD' : s = D := by omega
      subst hsD'
      intro hp
      exact hp hwrapstep

/-- **The alternation seed.**  On a periodic tail, two consecutive
productive steps can write the same cell only if the walk stands in
that cell or at its mouth partner strictly between the two arrivals.
In particular, two adjacent productive steps never write the same
cell: the four-beat alternation begins here. -/
theorem consecutive_same_write_visits (hrun : IsRun m e r0)
    (cells : List Nat)
    (hcells : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    (hallcells : ∀ s, m.cellOf s ∈ cells)
    {K p : Nat} (hp : 0 < p)
    (hper : ∀ t, K ≤ t → e (t + p) = e t)
    (hregper : ∀ t c, K ≤ t → reg m e r0 (t + p) c = reg m e r0 t c)
    {C t1 t2 : Nat} (hK : K ≤ t1) (h12 : t1 < t2)
    (hq : ∀ s, t1 < s → s < t2 → ¬ ProductiveStep m e r0 s)
    (hp1 : ProductiveStep m e r0 t1)
    (hp2 : ProductiveStep m e r0 t2)
    (hc1 : m.cellOf (e (t1 + 1)) = C)
    (hc2 : m.cellOf (e (t2 + 1)) = C) :
    ∃ l, 1 ≤ l ∧ l ≤ t2 - t1 - 1 ∧
      (m.cellOf (e (t1 + 1 + l)) = C ∨
       m.cellOf (e (t1 + 1 + l)) = m.star C) := by
  by_cases hex : ∃ l, 1 ≤ l ∧ l ≤ t2 - t1 - 1 ∧
      (m.cellOf (e (t1 + 1 + l)) = C ∨
       m.cellOf (e (t1 + 1 + l)) = m.star C)
  · exact hex
  · exfalso
    have havoid : ∀ l, 1 ≤ l → l ≤ t2 - t1 - 1 →
        m.cellOf (e (t1 + 1 + l)) ≠ C ∧
        m.cellOf (e (t1 + 1 + l)) ≠ m.star C := by
      intro l h1 h2
      constructor
      · intro h
        exact hex ⟨l, h1, h2, Or.inl h⟩
      · intro h
        exact hex ⟨l, h1, h2, Or.inr h⟩
    obtain ⟨hmatch, hquiet⟩ := consecutive_avoid_loop m e r0 hrun cells
      h12 hq hc1 hc2 havoid
    -- the tail from t2+1 is (t2-t1)-periodic and quiet on one period,
    -- hence quiet forever
    have hnoprod : ∀ n, ¬ ProductiveStep m e r0 (t2 + 1 + n) := by
      intro n
      have hmod := Nat.div_add_mod n (t2 - t1)
      have hrlt : n % (t2 - t1) < t2 - t1 :=
        Nat.mod_lt _ (by omega)
      have hiter := state_replay_iter m e r0 hrun cells hcells hmatch
        (n / (t2 - t1)) (n % (t2 - t1))
      have harith : t2 + 1 + n / (t2 - t1) * (t2 - t1) + n % (t2 - t1)
          = t2 + 1 + n := by
        have hc : (t2 - t1) * (n / (t2 - t1))
            = n / (t2 - t1) * (t2 - t1) := Nat.mul_comm _ _
        omega
      rw [harith] at hiter
      have hiff := productive_iff_of_state_eq m e r0 hrun cells hcells
        hallcells hiter
      intro hprod
      exact hquiet (n % (t2 - t1)) hrlt (hiff.mpr hprod)
    -- but the second write recurs one period later
    have hrec : ProductiveStep m e r0 (t2 + p) :=
      (productive_periodic m e r0 hper hregper (by omega)).mpr hp2
    have harith : t2 + p = t2 + 1 + (p - 1) := by omega
    rw [harith] at hrec
    exact hnoprod (p - 1) hrec

end Echo
