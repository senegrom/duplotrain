import RestorationFrameOrdering
import VisibleChipReduction

/-!
# Classifying the nested restoration residue

`RestorationFrameOrdering` eliminates every foreign middle-blocker frame
which exits the overlap of a cyclic-overlap-minimal crossing.  This file
classifies the remaining laminar case.

If a foreign frame `(b,r)` is nested in the common interior of the crossing,
then its close is strictly before `u0` (shared closure is impossible), and
its restored slot is distinct from both restoration roots of the original
crossing.  Thus the only alternative to an exact lobe write is a strict
three-root nest; the nested branch cannot silently reuse either crossed
frame's root.
-/

namespace Echo

variable (m : Machine) (e : Nat -> Nat) (r0 : Nat -> Nat)

/-- Strictly nested first-restoration frames cannot restore the same root.
The close of the inner frame lies strictly inside the outer frame, where the
outer firstness condition forbids delivery of its root. -/
theorem strict_nested_first_restoration_roots_ne
    {t u b r : Nat}
    (houter : FirstRestorationFrame m e r0 t u)
    (hinner : FirstRestorationFrame m e r0 b r)
    (htb : t < b)
    (hru : r < u) :
    oldSlot m e r0 b ≠ oldSlot m e r0 t := by
  intro heq
  have hbr : b < r := hinner.1.2.1
  have hforbid := houter.2 r (by omega) hru
  apply hforbid
  exact hinner.1.2.2.2.2.trans heq

/-- Restoration roots are injective along any strictly nested family of
first-restoration frames.  This is the general charging law for repeatedly
descending into the laminar residue: each deeper frame consumes a new slot. -/
theorem strictly_nested_family_roots_injective
    {opening closing : Nat -> Nat}
    (hframes : forall i,
      FirstRestorationFrame m e r0 (opening i) (closing i))
    (hnested : forall {i j}, i < j ->
      opening i < opening j /\ closing j < closing i) :
    Function.Injective
      (fun i => oldSlot m e r0 (opening i)) := by
  intro i j heq
  apply Classical.byContradiction
  intro hne
  by_cases hij : i < j
  · have horder := hnested hij
    exact (strict_nested_first_restoration_roots_ne
      m e r0 (hframes i) (hframes j) horder.1 horder.2) heq.symm
  · have hji : j < i := by omega
    have horder := hnested hji
    exact (strict_nested_first_restoration_roots_ne
      m e r0 (hframes j) (hframes i) horder.1 horder.2) heq

/-- The exact structural residue of a foreign restoration nested in the
common interior of two crossing first-restoration frames. -/
structure StrictNestedForeignRestoration
    (t0 u0 t1 u1 b j r : Nat) : Prop where
  frame : ForeignRestorationFrame m e r0 b r
  order :
    t0 < t1 /\ t1 < b /\ b < j /\ j <= r /\ r < u0 /\ u0 < u1
  root_ne_first : oldSlot m e r0 b ≠ oldSlot m e r0 t0
  root_ne_second : oldSlot m e r0 b ≠ oldSlot m e r0 t1
  crossed_roots_ne : oldSlot m e r0 t0 ≠ oldSlot m e r0 t1

/-- On an exact recurrent tail, the strict nested obstruction consists of
six visible transfers of a full edge: the two endpoints of each original
crossed frame and the two endpoints of the nested frame. -/
structure RecurrentStrictNestedForeignRestoration
    (t0 u0 t1 u1 b j r : Nat) : Prop where
  core : StrictNestedForeignRestoration
    m e r0 t0 u0 t1 u1 b j r
  first_open_chip : VisibleFullEdgeChipMove m e r0 t0
  first_close_chip : VisibleFullEdgeChipMove m e r0 u0
  second_open_chip : VisibleFullEdgeChipMove m e r0 t1
  second_close_chip : VisibleFullEdgeChipMove m e r0 u1
  nested_open_chip : VisibleFullEdgeChipMove m e r0 b
  nested_close_chip : VisibleFullEdgeChipMove m e r0 r

/-- A productive different-edge write on a register-periodic tail is visible
and transfers fullness.  Otherwise fixed support would turn the hidden write
into a same-edge lobe flip, contrary to `hdiff`. -/
theorem recurrent_foreign_write_is_visible_chip
    (hrun : IsRun m e r0)
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p k : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hk : K <= k)
    (hprod : ProductiveStep m e r0 k)
    (hdiff : ¬ SameEdge m (oldSlot m e r0 k) (e (k+1))) :
    VisibleFullEdgeChipMove m e r0 k := by
  have hfixed : SupportFixedStep m e r0 k :=
    support_fixed_of_register_period
      m e r0 hrun hr0 hper.positive hper.register k hk
  have hchange : ProjectionChanges m e r0 k := by
    apply Classical.byContradiction
    intro hnot
    have hstall : forall c,
        nextCell m e r0 (k+1) c = nextCell m e r0 k c := by
      intro c
      apply Classical.byContradiction
      intro hne
      exact hnot ⟨c, hne⟩
    have hlobe := hidden_fixed_is_lobe
      m e r0 hrun hr0 k hprod hstall hfixed
    exact hdiff (Or.inr hlobe.1)
  exact recurrent_projection_change_is_chip_move
    m e r0 hrun hr0
    ⟨hper.positive, hper.entry, hper.register⟩ hk hchange

/-- A foreign frame nested weakly below the first close in fact closes
strictly below it.  Equality would make the inner and outer frames restore
the same register value at the same step, putting the outer root back in its
register strictly before its declared first restoration. -/
theorem nested_foreign_close_strict
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p t0 u0 t1 u1 b r : Nat}
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hframe : ForeignRestorationFrame m e r0 b r)
    (ht1b : t1 < b)
    (hru0 : r <= u0) :
    r < u0 := by
  by_cases hre : r = u0
  · have houter : ForeignRestorationFrame m e r0 t0 u0 :=
      hmin.1.1.1.1
    have ht0t1 : t0 < t1 := hmin.1.1.1.2.2.1
    have hwriter : writerAt m e b = writerAt m e t0 := by
      calc
        writerAt m e b = writerAt m e r :=
          hframe.1.1.2.2.2.1.symm
        _ = writerAt m e u0 := by rw [hre]
        _ = writerAt m e t0 := houter.1.1.2.2.2.1
    have hold : oldSlot m e r0 b = oldSlot m e r0 t0 := by
      calc
        oldSlot m e r0 b = e (r+1) := hframe.1.1.2.2.2.2.symm
        _ = e (u0+1) := by rw [hre]
        _ = oldSlot m e r0 t0 := houter.1.1.2.2.2.2
    have hbr : b < r := hframe.1.1.2.1
    exact (first_restoration_forbids_early_returned_register
      m e r0 hr0 houter.1 (by omega) (by omega) hwriter hold).elim
  · omega

/-- The three restoration roots in a strict nested residue are pairwise
distinct.  Each inequality is forced by firstness of one of the two crossed
frames. -/
theorem nested_foreign_roots_distinct
    {K p t0 u0 t1 u1 b r : Nat}
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hframe : ForeignRestorationFrame m e r0 b r)
    (ht1b : t1 < b)
    (hru0 : r < u0) :
    oldSlot m e r0 b ≠ oldSlot m e r0 t0 /\
    oldSlot m e r0 b ≠ oldSlot m e r0 t1 /\
    oldSlot m e r0 t0 ≠ oldSlot m e r0 t1 := by
  have houter : ForeignRestorationFrame m e r0 t0 u0 :=
    hmin.1.1.1.1
  have hsecond : ForeignRestorationFrame m e r0 t1 u1 :=
    hmin.1.1.1.2.1
  have horder := hmin.1.1.1.2.2
  rcases horder with ⟨ht0t1, _ht1u0, hu0u1⟩
  have hbr : b < r := hframe.1.1.2.1
  have hreturnB : e (r+1) = oldSlot m e r0 b :=
    hframe.1.1.2.2.2.2
  have hreturn0 : e (u0+1) = oldSlot m e r0 t0 :=
    houter.1.1.2.2.2.2
  constructor
  · intro heq
    have hfirst := houter.1.2 r (by omega) hru0
    apply hfirst
    exact hreturnB.trans heq
  constructor
  · intro heq
    have hfirst := hsecond.1.2 r (by omega) (by omega)
    apply hfirst
    exact hreturnB.trans heq
  · intro heq
    have hfirst := hsecond.1.2 u0 (by omega) hu0u1
    apply hfirst
    exact hreturn0.trans heq

/-- Complete classification of the formerly open nested-inside-overlap
case.  It is not merely weakly nested: it is a strict laminar frame in the
common interior, and its restoration root is a third root distinct from the
two roots of the cyclic-minimal crossing. -/
theorem nested_foreign_case_classified
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p t0 u0 t1 u1 b j r : Nat}
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hframe : ForeignRestorationFrame m e r0 b r)
    (ht1b : t1 < b)
    (hbj : b < j)
    (hjr : j <= r)
    (hru0 : r <= u0) :
    StrictNestedForeignRestoration
      m e r0 t0 u0 t1 u1 b j r := by
  have hrlt := nested_foreign_close_strict
    m e r0 hr0 hmin hframe ht1b hru0
  have hroots := nested_foreign_roots_distinct
    m e r0 hmin hframe ht1b hrlt
  have horder := hmin.1.1.1.2.2
  exact {
    frame := hframe
    order := ⟨horder.1, ht1b, hbj, hjr, hrlt, horder.2.2⟩
    root_ne_first := hroots.1
    root_ne_second := hroots.2.1
    crossed_roots_ne := hroots.2.2
  }

/-- Every endpoint in a strict nested recurrent obstruction is a visible
full-edge chip move.  This packages the nested temporal order as the exact
six transfer witnesses needed by the visible recurrent branch. -/
theorem strict_nested_foreign_is_six_chip
    (hrun : IsRun m e r0)
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p t0 u0 t1 u1 b j r : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hcore : StrictNestedForeignRestoration
      m e r0 t0 u0 t1 u1 b j r) :
    RecurrentStrictNestedForeignRestoration
      m e r0 t0 u0 t1 u1 b j r := by
  have houter : ForeignRestorationFrame m e r0 t0 u0 :=
    hmin.1.1.1.1
  have hsecond : ForeignRestorationFrame m e r0 t1 u1 :=
    hmin.1.1.1.2.1
  have hKt0 : K <= t0 := hmin.1.2.1
  have horder := hcore.order
  have hKt1 : K <= t1 := by omega
  have hKu0 : K <= u0 := by omega
  have hKu1 : K <= u1 := by omega
  have hKb : K <= b := by omega
  have hKr : K <= r := by omega
  exact {
    core := hcore
    first_open_chip := recurrent_foreign_write_is_visible_chip
      m e r0 hrun hr0 hper hKt0 houter.1.1.1 houter.2.1
    first_close_chip := recurrent_foreign_write_is_visible_chip
      m e r0 hrun hr0 hper hKu0 houter.1.1.2.2.1 houter.2.2
    second_open_chip := recurrent_foreign_write_is_visible_chip
      m e r0 hrun hr0 hper hKt1 hsecond.1.1.1 hsecond.2.1
    second_close_chip := recurrent_foreign_write_is_visible_chip
      m e r0 hrun hr0 hper hKu1 hsecond.1.1.2.2.1 hsecond.2.2
    nested_open_chip := recurrent_foreign_write_is_visible_chip
      m e r0 hrun hr0 hper hKb hcore.frame.1.1.1 hcore.frame.2.1
    nested_close_chip := recurrent_foreign_write_is_visible_chip
      m e r0 hrun hr0 hper hKr
        hcore.frame.1.1.2.2.1 hcore.frame.2.2
  }

/-- **Nested-restoration elimination/classification theorem.**

For a stable blocker in the overlap of a cyclic-overlap-minimal crossing,
the first restoration before one period has only two outcomes:

* one endpoint is an exact lobe write; or
* the frame is foreign, lies strictly in the common interior, and restores
  a third root distinct from both crossed restoration roots.

In particular, the old weak residue `r <= u0` has been eliminated. -/
theorem cyclic_minimal_stable_blocker_lobe_or_strict_three_root_nest
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p t0 u0 t1 u1 b j : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hKb : K <= b)
    (ht1b : t1 < b)
    (hbu0 : b < u0)
    (hstable : StableBlockerUntil m e r0 b j) :
    exists r,
      b < r /\ r < b+p /\
      FirstRestorationFrame m e r0 b r /\
      j <= r /\
      (ExactLobeWrite m e r0 b \/
       ExactLobeWrite m e r0 r \/
       StrictNestedForeignRestoration
         m e r0 t0 u0 t1 u1 b j r) := by
  obtain ⟨r, hbr, hrperiod, hfirst⟩ :=
    productive_has_first_restoration_before_period m e r0 hr0
      hper.positive hKb hper.register hstable.productive
  have hjr := stable_blocker_restoration_after_read
    m e r0 hstable hfirst.1
  refine ⟨r, hbr, hrperiod, hfirst, hjr, ?_⟩
  by_cases hopen : SameEdgeWrite m e r0 b
  · exact Or.inl (productive_sameEdgeWrite_exact_lobe
      m e r0 hr0 hstable.productive hopen)
  · by_cases hclose : SameEdgeWrite m e r0 r
    · exact Or.inr (Or.inl (productive_sameEdgeWrite_exact_lobe
        m e r0 hr0 hfirst.1.2.2.1 hclose))
    · have hforeign : ForeignRestorationFrame m e r0 b r :=
        ⟨hfirst, hopen, hclose⟩
      have hru0 := cyclic_minimal_middle_foreign_restoration_nested
        m e r0 hmin hforeign ht1b hbu0 hrperiod
      exact Or.inr (Or.inr (nested_foreign_case_classified
        m e r0 hr0 hmin hforeign ht1b hstable.before hjr hru0))

end Echo
