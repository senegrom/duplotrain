import SupportMove

/-!
# Common-full replay by paired path normalisation

Take one occupied support walk at time `i` and transport the same edges to time
`j`.  Normalise the two walks in lockstep:

* immediate backtracking pops the common path stack;
* every other step extends both stacks by the same slot.

Starting from a full root, the carried parent slot is confirmed at both times.
Since the normalised parent slot is literally the same, the endpoint register
agrees.  This proves full-component replay without the older rooted-tree
certificate layer.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- One oriented occupied support edge. -/
def GraphStep (k c d : Nat) : Prop :=
  ∃ s,
    Occupied m e r0 k s ∧
    m.cellOf s = c ∧
    m.cellOf (m.bar s) = d

/-- Ordinary support reachability from either endpoint of an edge. -/
inductive GraphReach (k f : Nat) : Nat → Prop
  | left : GraphReach k f (m.cellOf f)
  | right : GraphReach k f (m.cellOf (m.bar f))
  | step {c d : Nat} :
      GraphReach k f c → GraphStep m e r0 k c d →
      GraphReach k f d

/-- One normalised path stack valid at both selected times. -/
inductive PairedOutward (i j f : Nat) : Nat → Nat → Prop
  | left : PairedOutward i j f (m.cellOf f) f
  | right : PairedOutward i j f (m.cellOf (m.bar f)) (m.bar f)
  | step {c p s : Nat} :
      PairedOutward i j f c p →
      Occupied m e r0 i s → Occupied m e r0 j s →
      m.cellOf s = c →
      m.cellOf (m.bar s) ≠ m.cellOf (m.bar p) →
      PairedOutward i j f (m.cellOf (m.bar s)) (m.bar s)

/-- The carried parent slot belongs to the current cell. -/
theorem pairedOutward_slot_cell {i j f c p : Nat}
    (h : PairedOutward m e r0 i j f c p) :
    m.cellOf p = c := by
  induction h with
  | left => rfl
  | right => rfl
  | step => rfl

/-- Pop one common path frame. -/
theorem pairedOutward_parent {i j f c p : Nat}
    (h : PairedOutward m e r0 i j f c p) :
    ∃ q, PairedOutward m e r0 i j f
      (m.cellOf (m.bar p)) q := by
  cases h with
  | left =>
      exact ⟨m.bar f, PairedOutward.right⟩
  | right =>
      refine ⟨f, ?_⟩
      simpa [m.bar_invol] using
        (PairedOutward.left :
          PairedOutward m e r0 i j f (m.cellOf f) f)
  | @step c q s hprev hiOcc hjOcc hsrc hback =>
      refine ⟨q, ?_⟩
      simpa [m.bar_invol, hsrc] using hprev

/-- A support walk at time `i` normalises simultaneously at both times. -/
theorem pairedOutward_of_reach
    {i j f c : Nat}
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (h : GraphReach m e r0 i f c) :
    ∃ p, PairedOutward m e r0 i j f c p := by
  induction h with
  | left =>
      exact ⟨f, PairedOutward.left⟩
  | right =>
      exact ⟨m.bar f, PairedOutward.right⟩
  | @step c d hprev hstep ih =>
      rcases ih with ⟨p, hp⟩
      rcases hstep with ⟨s, hiOcc, hsrc, hdst⟩
      have hjOcc : Occupied m e r0 j s :=
        (hsupport s).mp hiOcc
      by_cases hback :
          m.cellOf (m.bar s) = m.cellOf (m.bar p)
      · rcases pairedOutward_parent m e r0 hp with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        have hd : d = m.cellOf (m.bar p) :=
          hdst.symm.trans hback
        simpa [hd] using hq
      · refine ⟨m.bar s, ?_⟩
        have hout := PairedOutward.step hp hiOcc hjOcc hsrc hback
        simpa [hdst] using hout

/-- The common carried slot is confirmed at both times. -/
theorem pairedOutward_confirmed
    {i j f c p : Nat}
    (hfi : Full m e r0 i f)
    (hfj : Full m e r0 j f)
    (h : PairedOutward m e r0 i j f c p) :
    Confirmed m e r0 i p ∧ Confirmed m e r0 j p := by
  induction h with
  | left => exact ⟨hfi.1, hfj.1⟩
  | right => exact ⟨hfi.2, hfj.2⟩
  | @step c p s hprev hiOcc hjOcc hsrc hback ih =>
      have hpcell : m.cellOf p = c :=
        pairedOutward_slot_cell m e r0 hprev
      have hnotI : ¬ Confirmed m e r0 i s := by
        intro hs
        have heq : p = s :=
          confirmed_same_cell_eq m e r0 ih.1 hs
            (hpcell.trans hsrc.symm)
        exact hback
          (congrArg (fun x => m.cellOf (m.bar x)) heq).symm
      have hnotJ : ¬ Confirmed m e r0 j s := by
        intro hs
        have heq : p = s :=
          confirmed_same_cell_eq m e r0 ih.2 hs
            (hpcell.trans hsrc.symm)
        exact hback
          (congrArg (fun x => m.cellOf (m.bar x)) heq).symm
      have hbarI : Confirmed m e r0 i (m.bar s) := by
        rcases hiOcc with hs | hs
        · exact absurd hs hnotI
        · exact hs
      have hbarJ : Confirmed m e r0 j (m.bar s) := by
        rcases hjOcc with hs | hs
        · exact absurd hs hnotJ
        · exact hs
      exact ⟨hbarI, hbarJ⟩

/-- **Common full root plus common support replay one register.** -/
theorem reg_eq_of_paired_full_reach
    {i j f c : Nat}
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hfi : Full m e r0 i f)
    (hfj : Full m e r0 j f)
    (hreach : GraphReach m e r0 i f c) :
    reg m e r0 i c = reg m e r0 j c := by
  rcases pairedOutward_of_reach m e r0 hsupport hreach with
    ⟨p, hp⟩
  have hc := pairedOutward_slot_cell m e r0 hp
  have hconf := pairedOutward_confirmed m e r0 hfi hfj hp
  unfold Confirmed at hconf
  rw [hc] at hconf
  exact hconf.1.trans hconf.2.symm

/-- Reachability transports across pointwise-equal supports. -/
theorem graphReach_support_congr
    {i j f c : Nat}
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (h : GraphReach m e r0 i f c) :
    GraphReach m e r0 j f c := by
  induction h with
  | left => exact GraphReach.left
  | right => exact GraphReach.right
  | @step c d hprev hstep ih =>
      apply GraphReach.step ih
      rcases hstep with ⟨s, hocc, hsrc, hdst⟩
      exact ⟨s, (hsupport s).mp hocc, hsrc, hdst⟩

end Echo
