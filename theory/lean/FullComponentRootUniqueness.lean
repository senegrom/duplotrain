import PairedReachReplay
import FullReachPersistencePaired

/-!
# A fixed occupied-support component has at most one full physical edge

The normalised `PairedOutward` stack gives a short proof.  Starting from a
full edge, its carried stack slot is confirmed.  A nontrivial outward step
cannot itself end on a full carried edge: the opposite endpoint's confirmation
would force the new edge to equal the previous carried edge, contradicting the
no-immediate-backtracking side condition.

Consequently two full roots whose support walks meet must represent the same
physical edge.  This is the key local uniqueness fact needed to replace the
Fibonacci full-edge code by one marker per tree support component.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

private theorem sameEdge_trans_fullComponent
    {a b c : Nat}
    (hab : SameEdge m a b) (hbc : SameEdge m b c) :
    SameEdge m a c := by
  rcases hab with hab | hab
  · subst b
    exact hbc
  · rcases hbc with hbc | hbc
    · rw [hbc]
      exact Or.inr hab
    · left
      calc
        c = m.bar b := hbc
        _ = m.bar (m.bar a) := by rw [hab]
        _ = a := m.bar_invol a

/-- Along a normalised walk rooted at a full edge, a full carried edge can only
be the root physical edge itself. -/
theorem pairedOutward_full_carried_sameEdge
    {k f c p : Nat}
    (hroot : Full m e r0 k f)
    (hwalk : PairedOutward m e r0 k k f c p)
    (hpfull : Full m e r0 k p) :
    SameEdge m f p := by
  induction hwalk with
  | left => exact Or.inl rfl
  | right => exact sameEdge_bar m f
  | @step c q s hprev hiOcc hjOcc hsrc hback ih =>
      have hqconf : Confirmed m e r0 k q :=
        (pairedOutward_confirmed m e r0 hroot hroot hprev).1
      have hsfull : Full m e r0 k s :=
        (pairedFull_bar_iff m e r0 k s).mp hpfull
      have hqcell : m.cellOf q = c :=
        pairedOutward_slot_cell m e r0 hprev
      have hqs : q = s :=
        confirmed_same_cell_eq m e r0 hqconf hsfull.1
          (hqcell.trans hsrc.symm)
      exfalso
      apply hback
      rw [hqs]

/-- Two full-rooted normalised walks ending with the same carried slot have the
same root physical edge. -/
theorem pairedOutward_common_carried_roots
    {k f g c p : Nat}
    (hffull : Full m e r0 k f)
    (hgfull : Full m e r0 k g)
    (hf : PairedOutward m e r0 k k f c p)
    (hg : PairedOutward m e r0 k k g c p) :
    SameEdge m f g := by
  induction hf generalizing g with
  | left =>
      exact sameEdge_symm m
        (pairedOutward_full_carried_sameEdge m e r0
          hgfull hg hffull)
  | right =>
      have hbarFull : Full m e r0 k (m.bar f) :=
        (pairedFull_bar_iff m e r0 k f).mpr hffull
      have hgbar : SameEdge m g (m.bar f) :=
        pairedOutward_full_carried_sameEdge m e r0
          hgfull hg hbarFull
      exact sameEdge_trans_fullComponent m
        (sameEdge_bar m f) (sameEdge_symm m hgbar)
  | @step c q s hprev hiOcc hjOcc hsrc hback ih =>
      obtain ⟨qg, hgparent⟩ := pairedOutward_parent m e r0 hg
      have hgparent' : PairedOutward m e r0 k k g c qg := by
        simpa [m.bar_invol, hsrc] using hgparent
      have hqconf : Confirmed m e r0 k q :=
        (pairedOutward_confirmed m e r0 hffull hffull hprev).1
      have hqgconf : Confirmed m e r0 k qg :=
        (pairedOutward_confirmed m e r0 hgfull hgfull hgparent').1
      have hqcell : m.cellOf q = c :=
        pairedOutward_slot_cell m e r0 hprev
      have hqgcell : m.cellOf qg = c :=
        pairedOutward_slot_cell m e r0 hgparent'
      have hqqg : q = qg :=
        confirmed_same_cell_eq m e r0 hqconf hqgconf
          (hqcell.trans hqgcell.symm)
      rw [← hqqg] at hgparent'
      exact ih hgfull hgparent'

/-- **Full-root uniqueness in a connected occupied-support component.**  If
walks from two full edges meet at one cell, the roots are the same physical
edge. -/
theorem full_roots_sameEdge_of_common_reach
    {k f g c : Nat}
    (hffull : Full m e r0 k f)
    (hgfull : Full m e r0 k g)
    (hf : GraphReach m e r0 k f c)
    (hg : GraphReach m e r0 k g c) :
    SameEdge m f g := by
  obtain ⟨p, hfp⟩ := pairedOutward_of_reach m e r0
    (fun _ => Iff.rfl) hf
  obtain ⟨q, hgq⟩ := pairedOutward_of_reach m e r0
    (fun _ => Iff.rfl) hg
  have hpconf : Confirmed m e r0 k p :=
    (pairedOutward_confirmed m e r0 hffull hffull hfp).1
  have hqconf : Confirmed m e r0 k q :=
    (pairedOutward_confirmed m e r0 hgfull hgfull hgq).1
  have hpcell : m.cellOf p = c :=
    pairedOutward_slot_cell m e r0 hfp
  have hqcell : m.cellOf q = c :=
    pairedOutward_slot_cell m e r0 hgq
  have hpq : p = q :=
    confirmed_same_cell_eq m e r0 hpconf hqconf
      (hpcell.trans hqcell.symm)
  rw [← hpq] at hgq
  exact pairedOutward_common_carried_roots m e r0
    hffull hgfull hfp hgq

/-- In particular, a full edge reachable from another full edge is the same
physical edge. -/
theorem full_reachable_full_sameEdge
    {k f g : Nat}
    (hffull : Full m e r0 k f)
    (hgfull : Full m e r0 k g)
    (hreach : GraphReach m e r0 k f (m.cellOf g)) :
    SameEdge m f g :=
  full_roots_sameEdge_of_common_reach m e r0
    hffull hgfull hreach GraphReach.left

end Echo
