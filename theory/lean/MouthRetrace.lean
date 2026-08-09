import EchoMachine

/-!
# The mouth retrace: a write under a mouth stand mirrors its approach

`quiet_mouth_unreachable` shows a quiet walk can never reach the mouth
partner of its own starting cell: such a path would have to be its own
`bar`-reflection, which pinches at an impossible middle.  This file runs
the same engine *forward* at a real mouth-stand write and obtains a
construction instead of a contradiction.

Let a productive step at `t3` be delivered from the written cell's mouth
(`cellOf (e t3) = star (cellOf (e (t3+1)))`), after a stretch that is
quiet since the previous write at `t2`.  Then the walk retraces its whole
approach as the `bar`-mirror, step for step:

    e (t3 + 1 + j) = bar (e (t3 + 1 - j))       (1 ≤ j ≤ t3 - t2)

with every retrace step before the last quiet.  At `j = t3 - t2` the
mirror reaches `bar (e (t2+1))` — the bar of the *previous* write.  If
that write was also delivered from its mouth, its bar lies in the same
cell, so the retrace ends in a new productive write of the previous
writer's cell, at the exactly mirrored distance.

Consequences, all local (no periodicity hypotheses anywhere):

* `mouth_stand_productive`: a mouth-stand delivery is automatically
  productive — mouths are hair-triggers;
* `mouth_stand_writers_ne`: consecutive mouth-stand writes write
  distinct cells;
* `mouth_stand_return`: after consecutive mouth-stand writes of `B`
  then `C`, the next productive step occurs at time `t3 + (t3 - t2)`
  and writes `B` again.

The last point is the four-beat engine: on any stretch whose deliveries
all stand at mouths, the productive-writer word cannot introduce a third
letter — it alternates `B C B C …` with equal spacing.  Combined with
the lobe dichotomy (`lobe_gray_lock`: each of the two cells is confined
to two register values) this is the abstract two-cell, four-state
picture of lemma B for mouth-delivery cycles.  The remaining frontier is
deliveries that do *not* stand at the written cell's mouth — cross
deliveries into foreign-valued cells.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Mouths are hair-triggers.**  Standing at the mouth partner of the
next entry's cell forces the step to be productive: the fetched register
is the entered cell's own register, and its bar differs from it. -/
theorem mouth_stand_productive (hrun : IsRun m e r0)
    (hbar : ∀ s, m.bar s ≠ s) {t : Nat}
    (hstand : m.cellOf (e t) = m.star (m.cellOf (e (t + 1)))) :
    ProductiveStep m e r0 t := by
  intro hquiet
  apply hbar (reg m e r0 t (m.cellOf (e (t + 1))))
  have h := hrun t
  rw [hstand, m.star_invol] at h
  exact h.symm.trans hquiet

/-- During the quiet approach to a mouth-stand write, the walk never
stands at that same mouth earlier: an earlier identical stand would
fetch the same register and deliver the same productive write early. -/
private theorem no_earlier_same_stand (hrun : IsRun m e r0)
    (hbar : ∀ s, m.bar s ≠ s) {t2 t3 : Nat}
    (hq : ∀ s, t2 < s → s < t3 → ¬ ProductiveStep m e r0 s)
    {τ : Nat} (hτ1 : t2 < τ) (hτ2 : τ < t3)
    (hstand3 : m.cellOf (e t3) = m.star (m.cellOf (e (t3 + 1))))
    (hstand : m.cellOf (e τ) = m.cellOf (e t3)) :
    False := by
  have hregs := quiet_reg m e r0 (i := τ) (t3 - τ)
    (fun t ht1 ht2 => hq t (by omega) (by omega))
  have harith : τ + (t3 - τ) = t3 := by omega
  rw [harith] at hregs
  apply hq τ hτ1 hτ2
  intro hqa
  apply hbar (reg m e r0 t3 (m.cellOf (e (t3 + 1))))
  have ht3read : e (t3 + 1)
      = m.bar (reg m e r0 t3 (m.cellOf (e (t3 + 1)))) := by
    have h := hrun t3
    rw [hstand3, m.star_invol] at h
    exact h
  have hτread : e (τ + 1)
      = m.bar (reg m e r0 t3 (m.cellOf (e (t3 + 1)))) := by
    have h := hrun τ
    rw [hstand, hstand3, m.star_invol] at h
    rw [← hregs] at h
    exact h
  have hsame : e (τ + 1) = e (t3 + 1) := hτread.trans ht3read.symm
  rw [hsame] at hqa
  rw [← hregs] at hqa
  exact ht3read.symm.trans hqa

/-- **Consecutive mouth-stand writes write distinct cells.**  If the
write at `t3` stands at the mouth of the same cell written at `t2`, the
quiet stretch from the stand at that cell to the stand at its mouth
violates the quiet-mouth palindrome. -/
theorem mouth_stand_writers_ne (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hbar : ∀ s, m.bar s ≠ s) {t2 t3 : Nat} (h23 : t2 < t3)
    (hq : ∀ s, t2 < s → s < t3 → ¬ ProductiveStep m e r0 s)
    (hstand3 : m.cellOf (e t3) = m.star (m.cellOf (e (t3 + 1)))) :
    m.cellOf (e (t3 + 1)) ≠ m.cellOf (e (t2 + 1)) := by
  intro hCB
  have hmouth : m.cellOf (e (t2 + 1 + (t3 - t2 - 1)))
      = m.star (m.cellOf (e (t2 + 1))) := by
    have harith : t2 + 1 + (t3 - t2 - 1) = t3 := by omega
    rw [harith, hstand3, hCB]
  exact quiet_mouth_unreachable m e r0 hrun hr0 hbar
    (i := t2 + 1) (p := t3 - t2 - 1)
    (fun t ht1 ht2 => hq t (by omega) (by omega)) hmouth

/-- **The mouth retrace.**  After a productive write delivered from the
written cell's mouth partner, the walk retraces its quiet approach as
the `bar`-mirror of itself: `e (t3+1+j) = bar (e (t3+1-j))` for every
`j` up to the full approach length `t3 - t2`, and every retrace step
strictly before phase `j` is quiet. -/
theorem mouth_retrace (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hbar : ∀ s, m.bar s ≠ s) {t2 t3 : Nat} (h23 : t2 < t3)
    (hq : ∀ s, t2 < s → s < t3 → ¬ ProductiveStep m e r0 s)
    (hstand3 : m.cellOf (e t3) = m.star (m.cellOf (e (t3 + 1)))) :
    ∀ j, 1 ≤ j → j ≤ t3 - t2 →
      e (t3 + 1 + j) = m.bar (e (t3 + 1 - j)) ∧
      ∀ u, t3 < u → u < t3 + j → ¬ ProductiveStep m e r0 u := by
  intro j
  induction j with
  | zero =>
      intro h1 _
      exact absurd h1 (by omega)
  | succ n ih =>
      intro _ hn1
      by_cases hn : n = 0
      · subst hn
        constructor
        · show e (t3 + 1 + 1) = m.bar (e (t3 + 1 - 1))
          have hidx : t3 + 1 - 1 = t3 := by omega
          rw [hidx]
          have h := hrun (t3 + 1)
          have hne : m.cellOf (e (t3 + 1))
              ≠ m.star (m.cellOf (e (t3 + 1))) :=
            fun hh => m.star_ne _ hh.symm
          rw [reg_skip m e r0 hne] at h
          rw [← hstand3] at h
          have hrw : reg m e r0 t3 (m.cellOf (e t3)) = e t3 :=
            reg_write m e r0 rfl
          rw [hrw] at h
          exact h
        · intro u hu1 hu2
          exact absurd hu1 (by omega)
      · obtain ⟨hmirror, hquietR⟩ := ih (by omega) (by omega)
        have hidx1 : t3 + 1 - n = t3 - n + 1 := by omega
        rw [hidx1] at hmirror
        have hw := witness m e r0 hrun hr0 (t3 - n)
        -- the outbound stand `t3 - n` is not the written cell: a quiet
        -- stand at the written cell strictly before its mouth stand
        -- would close a quiet mouth path
        have hE1 : m.cellOf (e (t3 - n)) ≠ m.cellOf (e (t3 + 1)) := by
          intro hXC
          apply quiet_mouth_unreachable m e r0 hrun hr0 hbar
            (i := t3 - n) (p := n)
            (fun t ht1 ht2 => hq t (by omega) (by omega))
          have harith : t3 - n + n = t3 := by omega
          rw [harith, hstand3, hXC]
        -- nor is the mouth of the outbound stand the written cell: that
        -- would repeat the delivering stand strictly earlier
        have hE2 : m.cellOf (e (t3 + 1))
            ≠ m.star (m.cellOf (e (t3 - n))) := by
          intro hCW
          apply no_earlier_same_stand m e r0 hrun hbar hq
            (τ := t3 - n) (by omega) (by omega) hstand3
          have h1 := congrArg m.star hCW
          rw [m.star_invol] at h1
          rw [← hstand3] at h1
          exact h1.symm
        -- the arrival of retrace phase `n` is quiet: it lands on the
        -- frozen register of the outbound read cell
        have hquietNew : ¬ ProductiveStep m e r0 (t3 + n) := by
          intro hp
          apply hp
          have hidx2 : t3 + n + 1 = t3 + 1 + n := by omega
          rw [hidx2, hmirror, hw.1]
          have hchain1 : reg m e r0 (t3 + n)
                (m.star (m.cellOf (e (t3 - n))))
              = reg m e r0 (t3 + 1)
                (m.star (m.cellOf (e (t3 - n)))) := by
            have h := quiet_reg m e r0 (i := t3 + 1) (n - 1)
              (fun t ht1 ht2 => hquietR t (by omega) (by omega))
            have hidx3 : t3 + 1 + (n - 1) = t3 + n := by omega
            rw [hidx3] at h
            exact h _
          have hchain2 : reg m e r0 (t3 + 1)
                (m.star (m.cellOf (e (t3 - n))))
              = reg m e r0 t3
                (m.star (m.cellOf (e (t3 - n)))) :=
            reg_skip m e r0 hE2
          have hchain3 : reg m e r0 t3
                (m.star (m.cellOf (e (t3 - n))))
              = reg m e r0 (t3 - n)
                (m.star (m.cellOf (e (t3 - n)))) := by
            have h := quiet_reg m e r0 (i := t3 - n) n
              (fun t ht1 ht2 => hq t (by omega) (by omega))
            have hidx4 : t3 - n + n = t3 := by omega
            rw [hidx4] at h
            exact h _
          rw [hchain1, hchain2, hchain3, hw.2]
        have hquietAll : ∀ u, t3 < u → u < t3 + (n + 1) →
            ¬ ProductiveStep m e r0 u := by
          intro u hu1 hu2
          by_cases hu : u = t3 + n
          · subst hu
            exact hquietNew
          · exact hquietR u hu1 (by omega)
        refine ⟨?_, hquietAll⟩
        show e (t3 + 1 + (n + 1)) = m.bar (e (t3 + 1 - (n + 1)))
        have h := hrun (t3 + 1 + n)
        rw [hmirror, hw.1, m.star_invol] at h
        have hc1 : reg m e r0 (t3 + 1 + n) (m.cellOf (e (t3 - n)))
            = reg m e r0 (t3 + 1) (m.cellOf (e (t3 - n))) := by
          have hh := quiet_reg m e r0 (i := t3 + 1) n
            (fun t ht1 ht2 => hquietAll t (by omega) (by omega))
          exact hh _
        have hc2 : reg m e r0 (t3 + 1) (m.cellOf (e (t3 - n)))
            = reg m e r0 t3 (m.cellOf (e (t3 - n))) :=
          reg_skip m e r0 (fun hcc => hE1 hcc.symm)
        have hc3 : reg m e r0 t3 (m.cellOf (e (t3 - n)))
            = reg m e r0 (t3 - n) (m.cellOf (e (t3 - n))) := by
          have hh := quiet_reg m e r0 (i := t3 - n) n
            (fun t ht1 ht2 => hq t (by omega) (by omega))
          have hidx4 : t3 - n + n = t3 := by omega
          rw [hidx4] at hh
          exact hh _
        have hrw : reg m e r0 (t3 - n) (m.cellOf (e (t3 - n)))
            = e (t3 - n) := reg_write m e r0 rfl
        rw [hc1, hc2, hc3, hrw] at h
        have hidx5 : t3 + 1 - (n + 1) = t3 - n := by omega
        rw [hidx5]
        have hidx6 : t3 + 1 + (n + 1) = t3 + 1 + n + 1 := by omega
        rw [hidx6]
        exact h

/-- **The two-letter return.**  After consecutive mouth-stand writes —
a write of `B` fetched from `star B` at `t2`, a quiet stretch, then a
write of `C` fetched from `star C` at `t3` — the next productive step
occurs at the exactly mirrored time `t3 + (t3 - t2)`, every step
between is quiet, and it writes `B` again.  A third letter cannot
follow two mouth-stand writes: the productive-writer word alternates
`B C B C …` with equal spacing. -/
theorem mouth_stand_return (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hbar : ∀ s, m.bar s ≠ s) {t2 t3 : Nat} (h23 : t2 < t3)
    (hq : ∀ s, t2 < s → s < t3 → ¬ ProductiveStep m e r0 s)
    (hstand2 : m.cellOf (e t2) = m.star (m.cellOf (e (t2 + 1))))
    (hstand3 : m.cellOf (e t3) = m.star (m.cellOf (e (t3 + 1)))) :
    ProductiveStep m e r0 (t3 + (t3 - t2)) ∧
    m.cellOf (e (t3 + (t3 - t2) + 1)) = m.cellOf (e (t2 + 1)) ∧
    ∀ u, t3 < u → u < t3 + (t3 - t2) → ¬ ProductiveStep m e r0 u := by
  obtain ⟨hmirror, hquiet⟩ :=
    mouth_retrace m e r0 hrun hr0 hbar h23 hq hstand3
      (t3 - t2) (by omega) (Nat.le_refl _)
  have hidxm : t3 + 1 - (t3 - t2) = t2 + 1 := by omega
  rw [hidxm] at hmirror
  have hlobe := mouth_delivery_lobe m e r0 hrun hr0 hstand2 rfl
  have hidxa : t3 + (t3 - t2) + 1 = t3 + 1 + (t3 - t2) := by omega
  have hcellB : m.cellOf (e (t3 + (t3 - t2) + 1))
      = m.cellOf (e (t2 + 1)) := by
    rw [hidxa, hmirror]
    exact hlobe
  -- the register of the previous writer is still its fresh write
  have hCB := mouth_stand_writers_ne m e r0 hrun hr0 hbar h23 hq hstand3
  have hreg1 : reg m e r0 (t3 + (t3 - t2)) (m.cellOf (e (t2 + 1)))
      = reg m e r0 (t3 + 1) (m.cellOf (e (t2 + 1))) := by
    have hh := quiet_reg m e r0 (i := t3 + 1) (t3 - t2 - 1)
      (fun t ht1 ht2 => hquiet t (by omega) (by omega))
    have hidx : t3 + 1 + (t3 - t2 - 1) = t3 + (t3 - t2) := by omega
    rw [hidx] at hh
    exact hh _
  have hreg2 : reg m e r0 (t3 + 1) (m.cellOf (e (t2 + 1)))
      = reg m e r0 t3 (m.cellOf (e (t2 + 1))) :=
    reg_skip m e r0 hCB
  have hreg3 : reg m e r0 t3 (m.cellOf (e (t2 + 1)))
      = reg m e r0 (t2 + 1) (m.cellOf (e (t2 + 1))) := by
    have hh := quiet_reg m e r0 (i := t2 + 1) (t3 - t2 - 1)
      (fun t ht1 ht2 => hq t (by omega) (by omega))
    have hidx : t2 + 1 + (t3 - t2 - 1) = t3 := by omega
    rw [hidx] at hh
    exact hh _
  have hrw : reg m e r0 (t2 + 1) (m.cellOf (e (t2 + 1)))
      = e (t2 + 1) := reg_write m e r0 rfl
  refine ⟨?_, hcellB, hquiet⟩
  intro hp
  apply hbar (e (t2 + 1))
  have harr : e (t3 + (t3 - t2) + 1) = m.bar (e (t2 + 1)) := by
    rw [hidxa]
    exact hmirror
  rw [hcellB, harr, hreg1, hreg2, hreg3, hrw] at hp
  exact hp

/-! ## Iteration: one mouth-stand pair locks the whole future

`mouth_stand_return` produces the next write; the lemmas below observe
that the new write again stands at a mouth — the mirror ends one step
past the previous writer's mouth — so the configuration reproduces
itself indefinitely: productive steps at the arithmetic times
`b + k*(b-a)`, every delivery a mouth stand, and every write returning
to the cell written two beats earlier.  The writer word of a run seeded
by one consecutive mouth-stand pair is two-letter periodic forever.
-/

/-- A consecutive mouth-stand pair: two mouth-stand deliveries with
nothing productive strictly between them.  (Both deliveries are
automatically productive by `mouth_stand_productive`.) -/
structure MouthPair (a b : Nat) : Prop where
  lt : a < b
  quiet : ∀ s, a < s → s < b → ¬ ProductiveStep m e r0 s
  stand_a : m.cellOf (e a) = m.star (m.cellOf (e (a + 1)))
  stand_b : m.cellOf (e b) = m.star (m.cellOf (e (b + 1)))

/-- **Pair propagation.**  A consecutive mouth-stand pair reproduces
itself one mirror further, with the same spacing, and the new write
returns to the earlier writer's cell. -/
theorem mouth_pair_step (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hbar : ∀ s, m.bar s ≠ s) {a b : Nat}
    (P : MouthPair m e r0 a b) :
    MouthPair m e r0 b (b + (b - a)) ∧
    m.cellOf (e (b + (b - a) + 1)) = m.cellOf (e (a + 1)) := by
  have hab := P.lt
  obtain ⟨hprod, hcell, hquiet⟩ :=
    mouth_stand_return m e r0 hrun hr0 hbar P.lt P.quiet
      P.stand_a P.stand_b
  have hstand_new : m.cellOf (e (b + (b - a)))
      = m.star (m.cellOf (e (b + (b - a) + 1))) := by
    rw [hcell]
    by_cases hr : b = a + 1
    · have hidx : b + (b - a) = b + 1 := by omega
      rw [hidx]
      have h1 := P.stand_b
      rw [hr] at h1
      have h2 := congrArg m.star h1
      rw [m.star_invol] at h2
      rw [hr]
      exact h2.symm
    · obtain ⟨hmirror, _⟩ := mouth_retrace m e r0 hrun hr0 hbar
        P.lt P.quiet P.stand_b (b - a - 1) (by omega) (by omega)
      have hidx1 : b + 1 + (b - a - 1) = b + (b - a) := by omega
      have hidx2 : b + 1 - (b - a - 1) = a + 1 + 1 := by omega
      rw [hidx1, hidx2] at hmirror
      rw [hmirror]
      exact (witness m e r0 hrun hr0 (a + 1)).1
  exact ⟨{ lt := by omega
           quiet := hquiet
           stand_a := P.stand_b
           stand_b := hstand_new }, hcell⟩

/-- **The pair tail.**  One consecutive mouth-stand pair yields
consecutive mouth-stand pairs at every arithmetic time
`b + k*(b-a)`: the productive pattern of the entire future is locked
to the seed spacing. -/
theorem mouth_pair_forever (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hbar : ∀ s, m.bar s ≠ s) {a b : Nat}
    (P : MouthPair m e r0 a b) :
    ∀ k, MouthPair m e r0 (b + k * (b - a))
      (b + (k + 1) * (b - a)) := by
  intro k
  induction k with
  | zero =>
      show MouthPair m e r0 (b + 0 * (b - a)) (b + (0 + 1) * (b - a))
      have h := (mouth_pair_step m e r0 hrun hr0 hbar P).1
      have hidx0 : b + 0 * (b - a) = b := by omega
      have hidx1 : b + (0 + 1) * (b - a) = b + (b - a) := by omega
      rw [hidx0, hidx1]
      exact h
  | succ n ih =>
      show MouthPair m e r0 (b + (n + 1) * (b - a))
        (b + (n + 1 + 1) * (b - a))
      have h := (mouth_pair_step m e r0 hrun hr0 hbar ih).1
      obtain ⟨X, hX⟩ : ∃ X, X = n * (b - a) := ⟨_, rfl⟩
      have e1 : (n + 1) * (b - a) = X + (b - a) := by
        rw [Nat.add_mul, Nat.one_mul, ← hX]
      have e2 : (n + 1 + 1) * (b - a) = X + (b - a) + (b - a) := by
        rw [Nat.add_mul, Nat.one_mul, e1]
      have hidx : b + (n + 1) * (b - a)
            + (b + (n + 1) * (b - a) - (b + n * (b - a)))
          = b + (n + 1 + 1) * (b - a) := by
        rw [e1, e2, ← hX]
        omega
      rw [hidx] at h
      exact h

/-- **Two-letter periodicity of the writer word.**  On the tail locked
by a mouth-stand pair, every write returns to the cell written two
beats earlier: the productive-writer word is `B C B C …` forever. -/
theorem mouth_pair_writer_period (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hbar : ∀ s, m.bar s ≠ s) {a b : Nat}
    (P : MouthPair m e r0 a b) :
    ∀ k, m.cellOf (e (b + (k + 1 + 1) * (b - a) + 1))
      = m.cellOf (e (b + k * (b - a) + 1)) := by
  intro k
  have hpair := mouth_pair_forever m e r0 hrun hr0 hbar P k
  have h := (mouth_pair_step m e r0 hrun hr0 hbar hpair).2
  obtain ⟨X, hX⟩ : ∃ X, X = k * (b - a) := ⟨_, rfl⟩
  have e1 : (k + 1) * (b - a) = X + (b - a) := by
    rw [Nat.add_mul, Nat.one_mul, ← hX]
  have e2 : (k + 1 + 1) * (b - a) = X + (b - a) + (b - a) := by
    rw [Nat.add_mul, Nat.one_mul, e1]
  have hidx : b + (k + 1) * (b - a)
        + (b + (k + 1) * (b - a) - (b + k * (b - a)))
      = b + (k + 1 + 1) * (b - a) := by
    rw [e1, e2, ← hX]
    omega
  rw [hidx] at h
  exact h

/-- The first return of the pair tail names its writer: beat `1` writes
the seed pair's first cell again. -/
theorem mouth_pair_first_return (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (hbar : ∀ s, m.bar s ≠ s) {a b : Nat}
    (P : MouthPair m e r0 a b) :
    m.cellOf (e (b + 1 * (b - a) + 1)) = m.cellOf (e (a + 1)) := by
  have h := (mouth_pair_step m e r0 hrun hr0 hbar P).2
  have hidx : b + 1 * (b - a) = b + (b - a) := by omega
  rw [hidx]
  exact h

/-! ## Lobe deliveries are exactly mouth stands

`mouth_delivery_lobe` (EchoMachine) shows a delivery fetched from the
entered cell's mouth hands out a lobe slot.  The converse holds too: a
delivered slot whose bar-partner lies in the entered cell can only have
been fetched from that cell's mouth.  So on any tail where the written
cells are lobe-valued — the left branch of `lobe_or_cross` — every
productive delivery is a mouth stand, and the two-letter lock above
applies verbatim.  The open frontier of the alternation program is
thereby confined to cross-valued writers. -/

/-- A delivery of a lobe slot stands at the written cell's mouth. -/
theorem lobe_delivery_stands (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {t : Nat}
    (hlobe : m.cellOf (m.bar (e (t + 1))) = m.cellOf (e (t + 1))) :
    m.cellOf (e t) = m.star (m.cellOf (e (t + 1))) := by
  have hw := (witness m e r0 hrun hr0 t).1
  rw [hlobe] at hw
  have h := congrArg m.star hw
  rw [m.star_invol] at h
  exact h.symm

/-- **The lobe seed.**  Two consecutive productive deliveries of lobe
slots form a consecutive mouth-stand pair: the entire two-letter tail
machinery applies to them. -/
theorem lobe_pair_seed (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {a b : Nat} (hab : a < b)
    (hq : ∀ s, a < s → s < b → ¬ ProductiveStep m e r0 s)
    (hlobe_a : m.cellOf (m.bar (e (a + 1))) = m.cellOf (e (a + 1)))
    (hlobe_b : m.cellOf (m.bar (e (b + 1))) = m.cellOf (e (b + 1))) :
    MouthPair m e r0 a b where
  lt := hab
  quiet := hq
  stand_a := lobe_delivery_stands m e r0 hrun hr0 hlobe_a
  stand_b := lobe_delivery_stands m e r0 hrun hr0 hlobe_b

end Echo
