import MellitRamanQuietClosure

/-!
# Descent of the two explicit Mellit/Raman quiet residues

The quiet-dogbone closure leaves two concrete alternatives.  This file
refines both of them.

* A productive event in a BABA gap is either a globally first writer, an
  outer-gap last-writer frame, or an interior frame closing no earlier than
  Raman's least quiet frame.  In the middle gap, an opener at or before the
  right BABA opening would create a strictly smaller BABA (or repeat the
  right-frame writer), so overlap minimality forces the opener inside.
* An escaping selected close has a canonical first element in the ordered
  list of uncovered closes.  Removing that head leaves a strictly shorter
  recursion list.

No fixed-N enumeration or cardinality hypothesis is used.
-/

namespace GeneralN

/-- A time lies in one of the two outer BABA gaps. -/
def BABAOuterGap
    (prior second reroute third k : Nat) : Prop :=
  (prior < k ∧ k < second) ∨ (reroute < k ∧ k < third)

/-- A non-first productive event in an outer gap, together with its canonical
last-writer frame. -/
def RamanOuterGapFrameResidue
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (_B : RawBABAInterlacement
      w N start prior second reroute third) : Prop :=
  ∃ k left,
    BABAOuterGap prior second reroute third k ∧
    RawProductiveAt w N start k ∧
    RawLastWriterFrame w N start left k

/-- In Raman's least-quiet-frame branch, a surviving non-first productive
middle-gap event must close at or after the selected least close. -/
def RamanPostQuietFrameResidue
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (_B : RawBABAInterlacement
      w N start prior second reroute third) : Prop :=
  ∃ opening closing k left,
    second < opening ∧
    opening < reroute ∧
    opening < closing ∧
    closing < reroute ∧
    Echo.ForeignRestorationFrame
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) opening closing ∧
    (∀ opening' closing',
      second < opening' →
      opening' < reroute →
      RawLastWriterFrame w N start opening' closing' →
      closing' < closing → False) ∧
    (∀ j, opening < j → j < closing →
      ¬ RawProductiveAt w N start j) ∧
    closing ≤ k ∧
    second < left ∧
    left < k ∧
    k < reroute ∧
    RawProductiveAt w N start k ∧
    RawLastWriterFrame w N start left k

/-- **Productive-gap classification.**

The middle-gap proof is the key point.  If the last occurrence of a
non-first writer were at or before `second`, then equality gives a forbidden
repeat inside the right last-writer frame, while strict inequality builds a
new BABA of overlap `k-second < reroute-second`.  Hence its opener is inside
the overlap.  Raman's no-frame branch excludes it; Raman's least-close branch
forces its close to be no earlier than that least close. -/
theorem RawBABAOverlapMinimal.raman_gap_productive_classification
    {w : Wiring} {N : Nat}
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hquiet : RamanQuietForeignResidue B)
    (hactive : BABAGapHasProductive B) :
    (∃ k,
      ((prior < k ∧ k < second) ∨
        (second < k ∧ k < reroute) ∨
        (reroute < k ∧ k < third)) ∧
      RawProductiveAt w N start k ∧
      RawFirstWriterAt w N start k) ∨
    RamanOuterGapFrameResidue B ∨
    RamanPostQuietFrameResidue B := by
  obtain ⟨k, hgap, hprod⟩ := hactive
  by_cases hfirst : RawFirstWriterAt w N start k
  · exact Or.inl ⟨k, hgap, hprod, hfirst⟩
  obtain ⟨left, F⟩ :=
    last_writer_frame_of_productive_not_first hprod hfirst
  rcases hgap with hpriorSecond | hsecondReroute | hrerouteThird
  · exact Or.inr (Or.inl
      ⟨k, left, Or.inl hpriorSecond, hprod, F⟩)
  · have hsecondLeft : second < left := by
      by_cases hleftLe : left ≤ second
      · have hkThird : k < third :=
          Nat.lt_trans hsecondReroute.2 B.reroute_lt_third
        by_cases hleftEq : left = second
        · subst left
          have hne := B.rightFrame.no_same_writer_between k
            hsecondReroute.1 hkThird hprod
          exact (hne
            (F.same_writer.symm.trans
              B.rightFrame.same_writer)).elim
        · have hleftLt : left < second := by omega
          have hdiff : rawWriterAt w start k ≠
              rawWriterAt w start third :=
            B.rightFrame.no_same_writer_between k
              hsecondReroute.1 hkThird hprod
          let C : RawBABAInterlacement
              w N start left second k third := {
            prior_lt_second := hleftLt
            second_lt_reroute := hsecondReroute.1
            reroute_lt_third := hkThird
            leftFrame := F
            rightFrame := B.rightFrame
            different_writers := hdiff
          }
          have hsmaller : C.overlap < B.overlap := by
            change k - second < reroute - second
            omega
          exact (hmin left second k third C hsmaller).elim
      · omega
    have hleftReroute : left < reroute :=
      Nat.lt_trans F.order hsecondReroute.2
    rcases hquiet with hnoFrame | hleast
    · exact (hnoFrame left k hsecondLeft hleftReroute F).elim
    · obtain ⟨opening, closing, hsecondOpening, hopenReroute,
        hopenClose, hcloseReroute, hforeign,
        hminimal, hquietInterior⟩ := hleast
      have hcloseLe : closing ≤ k := by
        by_cases hkClose : k < closing
        · exact (hminimal left k hsecondLeft hleftReroute F hkClose).elim
        · omega
      exact Or.inr (Or.inr
        ⟨opening, closing, k, left,
          hsecondOpening, hopenReroute, hopenClose, hcloseReroute,
          hforeign, hminimal, hquietInterior, hcloseLe,
          hsecondLeft, F.order, hsecondReroute.2, hprod, F⟩)
  · exact Or.inr (Or.inl
      ⟨k, left, Or.inr hrerouteThird, hprod, F⟩)

/-- The ordered list of selected closes not covered by one finite BABA
segment. -/
def selectedTailOutsideBABA
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (prior third : Nat) : List Nat :=
  [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1].filter
    (fun t => decide (t < prior ∨ third + 1 < t))

/-- Data for the well-founded escape recursion.  `first` is literally the
head of the ordered uncovered-close list, and `remainder` is strictly
shorter. -/
structure SelectedEscapeRecursionStep
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (prior third : Nat) : Type where
  first : Nat
  remainder : List Nat
  split : selectedTailOutsideBABA C prior third = first :: remainder
  outside : first < prior ∨ third + 1 < first
  decreases : remainder.length <
    (selectedTailOutsideBABA C prior third).length

/-- An escaping selected close supplies the canonical strict recursion step:
take the first uncovered selected close and recurse on the remaining tail. -/
theorem SelectedTailEscapesBABA.first_strict_recursion_step
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {prior third : Nat}
    (H : SelectedTailEscapesBABA C prior third) :
    Nonempty (SelectedEscapeRecursionStep C prior third) := by
  obtain ⟨t, ht, houtside⟩ := H
  have htOutside : t ∈ selectedTailOutsideBABA C prior third := by
    apply List.mem_filter.mpr
    exact ⟨ht, by simpa using houtside⟩
  cases hlist : selectedTailOutsideBABA C prior third with
  | nil =>
      rw [hlist] at htOutside
      exact (List.not_mem_nil htOutside).elim
  | cons first remainder =>
      have hfirstMem : first ∈ selectedTailOutsideBABA C prior third := by
        rw [hlist]
        exact List.mem_cons_self
      have hfirstOutside : first < prior ∨ third + 1 < first := by
        have hfiltered := (List.mem_filter.mp hfirstMem).2
        exact of_decide_eq_true hfiltered
      exact ⟨{
        first := first
        remainder := remainder
        split := hlist
        outside := hfirstOutside
        decreases := by rw [hlist]; simp
      }⟩

/-- The fully refined outcome after attacking both explicit quiet residues. -/
inductive MellitRamanResidueDescentOutcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    (B : RawBABAInterlacement
      w N start prior second reroute third) : Prop
  | cycle (h : MellitReachedSimpleCycle w start)
  | latePair (h : Nonempty (MellitLatePairResidue C))
  | earlyPureCrossing (h : Nonempty (MellitEarlyPureCrossingResidue C))
  | interiorLobe (k : Nat) (h : RawReachedDirectLobeAt w start k)
  | firstWriterCharge (k : Nat)
      (hfirst : RawFirstWriterAt w N start k)
  | escapeDescent
      (hquiet : RamanQuietForeignResidue B)
      (step : Nonempty (SelectedEscapeRecursionStep C prior third))
  | outerGapFrame (h : RamanOuterGapFrameResidue B)
  | postQuietFrame (h : RamanPostQuietFrameResidue B)

/-- Consume `mellit_raman_after_quiet_outcome` and refine both of its last
constructors to a charge, a strict selected-close recursion step, or a named
last-writer-frame residue. -/
theorem RawBABAOverlapMinimal.mellit_raman_residue_descent_outcome
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B) :
    MellitRamanResidueDescentOutcome C B := by
  rcases hmin.mellit_raman_after_quiet_outcome hN C with
    hcycle | hlate | hearly | ⟨k, hlobe⟩ |
      ⟨k, _hsecond, _hreroute, hfirst⟩ |
      ⟨hquiet, hescape⟩ | ⟨hquiet, hactive⟩
  · exact .cycle hcycle
  · exact .latePair hlate
  · exact .earlyPureCrossing hearly
  · exact .interiorLobe k hlobe
  · exact .firstWriterCharge k hfirst
  · exact .escapeDescent hquiet hescape.first_strict_recursion_step
  · rcases hmin.raman_gap_productive_classification
      hquiet hactive with hfirst | houter | hpost
    · obtain ⟨k, _hgap, _hprod, hfirst⟩ := hfirst
      exact .firstWriterCharge k hfirst
    · exact .outerGapFrame houter
    · exact .postQuietFrame hpost

end GeneralN
