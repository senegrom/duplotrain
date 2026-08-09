import SerialSerialCallerAssembly
import SharpSixEventAssembly

/-!
# Sharp placement reduction for the serial/serial leaf

This file removes two spurious placement alternatives from the canonical
tail-caller extraction.  A last-writer opening is unique once its closing
time is fixed.  Consequently, if the first post-return escape is the first
selected tail close, its previous write is exactly the canonical opening
`a1`: it cannot lie strictly to the left of the caller, and a placement at
or after the caller's right endpoint forces the caller to be empty.

The final theorem exposes the strict selected-close decrease already carried
by `RawSerialSerialNestedDescent` without introducing another residue type.
-/

namespace GeneralN

/-- Two last-writer frames with the same closing event have the same opening.
This is the finite-order uniqueness hidden in `no_same_writer_between`. -/
theorem RawLastWriterFrame.left_eq_of_same_close
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {left₁ left₂ right : Nat}
    (F₁ : RawLastWriterFrame w N start left₁ right)
    (F₂ : RawLastWriterFrame w N start left₂ right) :
    left₁ = left₂ := by
  apply Nat.le_antisymm
  · apply Classical.byContradiction
    intro hnot
    have hlt : left₂ < left₁ := by omega
    exact (F₂.no_same_writer_between left₁ hlt F₁.order
      F₁.open_productive F₁.same_writer).elim
  · apply Classical.byContradiction
    intro hnot
    have hlt : left₁ < left₂ := by omega
    exact (F₁.no_same_writer_between left₂ hlt F₂.order
      F₂.open_productive F₂.same_writer).elim

/-- Strictly before the second selected post-state, the canonical finite
writer cover needs no `z1` exception: first-writer history and the `z0`
post-state already suffice. -/
theorem RawOverlappingFiveWindowReduction.prefix_before_z1_paid
    {w : Wiring} {N t : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    (ht : t ≤ R.z1) :
    restrictedTonguesAt w N start t ∈
      rawFirstWriterHistory w N start (R.z5 + 1) ++
        [restrictedTonguesAt w N start (R.z0 + 1)] := by
  have hm := R.prefix_through_z1_paid (t := t) (by omega)
  rcases List.mem_append.mp hm with hpaid | hz1
  · exact hpaid
  · simp only [List.mem_singleton] at hz1
    exact (R.event1.2.2.post_ne_earlier
      (earlier := t) (by omega) hz1.symm).elim

/-- The canonical tail escape is paid before `z1`; at `z1` its previous
write is the canonical opening `a1`.  Thus the old three-way placement has
only an interior caller contact or the concrete degenerate case `caller=[]`.

All physical caller and return data are retained so the interior branch can
be passed directly to `early_crossing_caller_exact_false`. -/
theorem RawOverlappingFiveWindowReduction.tail_serial_escape_sharp_placement
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawOverlappingFiveWindowReduction w N start)
    (hserial : FiveFrameSerialBreak
      R.z1 R.a2 R.a3 R.a4 R.a5) :
    ∃ (g oldEntry q edge repeatTime returnTime escape : Nat)
        (base mouthState u settled : Tongues)
        (caller : List Passage),
      stepN w R.a1 start = some (g, base) ∧
      PhysicalTrace w (g, base) caller (oldEntry, mouthState) ∧
      PassagesGrooved settled caller ∧
      w.link edge = some g ∧
      stepN w repeatTime start = some (q, u) ∧
      returnTime = repeatTime + caller.length + 1 ∧
      stepN w returnTime start = some (edge, settled) ∧
      returnTime ≤ escape ∧
      escape ≤ R.z1 ∧
      RawProductiveAt w N start escape ∧
      (∀ t, returnTime ≤ t → t < escape →
        ¬ RawProductiveAt w N start t) ∧
      (restrictedTonguesAt w N start (escape + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)] ∨
        ∃ left,
          RawLastWriterFrame w N start left escape ∧
          escape = R.z1 ∧ left = R.a1 ∧
          ((0 < caller.length ∧ R.a1 ≤ left ∧
              left < R.a1 + caller.length) ∨
            caller = [])) := by
  obtain ⟨g, oldEntry, q, edge, repeatTime, returnTime, escape,
      base, mouthState, u, settled, caller,
      hstart, hcaller, hgrooved, hedge, hrepeat, hreturnTime,
      hreturn, hreturnEscape, hescape, hproductive, hminimal,
      hfirst | ⟨left, F, hleftRepeat, hplacement⟩⟩ :=
    R.tail_serial_canonical_caller_escape hN hentry hserial
  · refine ⟨g, oldEntry, q, edge, repeatTime, returnTime, escape,
      base, mouthState, u, settled, caller,
      hstart, hcaller, hgrooved, hedge, hrepeat, hreturnTime,
      hreturn, hreturnEscape, hescape, hproductive, hminimal,
      Or.inl ?_⟩
    apply List.mem_append_left
    unfold rawFirstWriterHistory
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨escape, mem_rawFirstWriterTimes_iff.mpr ?_, rfl⟩
    exact ⟨by
      have hz15 : R.z1 < R.z5 :=
        Nat.lt_trans R.order12
          (Nat.lt_trans R.order23
            (Nat.lt_trans R.order34 R.order45))
      omega, hfirst⟩
  · by_cases hbefore : escape < R.z1
    · refine ⟨g, oldEntry, q, edge, repeatTime, returnTime, escape,
        base, mouthState, u, settled, caller,
        hstart, hcaller, hgrooved, hedge, hrepeat, hreturnTime,
        hreturn, hreturnEscape, hescape, hproductive, hminimal,
        Or.inl ?_⟩
      exact R.prefix_before_z1_paid (t := escape + 1) (by omega)
    · have hescapeEq : escape = R.z1 := by omega
      have hleftEq : left = R.a1 := by
        subst escape
        exact F.left_eq_of_same_close R.frame1.outer
      refine ⟨g, oldEntry, q, edge, repeatTime, returnTime, escape,
        base, mouthState, u, settled, caller,
        hstart, hcaller, hgrooved, hedge, hrepeat, hreturnTime,
        hreturn, hreturnEscape, hescape, hproductive, hminimal,
        Or.inr ⟨left, F, hescapeEq, hleftEq, ?_⟩⟩
      rcases hplacement with hleft | hmiddle | hright
      · exact (Nat.not_lt_of_ge (hleftEq ▸ Nat.le_refl R.a1) hleft).elim
      · left
        exact ⟨by omega, hmiddle.1, hmiddle.2⟩
      · right
        cases caller with
        | nil => rfl
        | cons passage rest =>
            simp at hright
            have hpositive : 0 < rest.length + 1 := Nat.zero_lt_succ _
            omega

/-- Direct, information-preserving strict-measure interface for the
serial/serial top-level leaf.  One of its selected global closes rebases at
a positive reached time to a framed novelty with a strictly smaller close.
No recursive certificate or residual proposition appears in the result. -/
theorem RawSerialSerialNestedDescent.strict_selected_close
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {R : RawOverlappingFiveWindowReduction w N start}
    (D : RawSerialSerialNestedDescent R) :
    ∃ (returned : Nat × Tongues) (shift globalClose : Nat)
        (localFrame : RawFramedNovelty w N returned),
      stepN w shift start = some returned ∧
      0 < shift ∧
      (globalClose = R.z1 ∨ globalClose = R.z2 ∨
        globalClose = R.z3 ∨ globalClose = R.z4 ∨
        globalClose = R.z5) ∧
      localFrame.closeTime = globalClose - shift ∧
      localFrame.closeTime < globalClose := by
  rcases D with ⟨H, T, SH, ST, hSH, hST, hcompare⟩
  rcases hcompare with hHT | hTH
  · obtain ⟨_hreturnOrder, _htransition, FH, FT,
      _hFHClose, hFTClose, _hFHLt, hFTLt,
      _hlocalOrder, _hstrictOrder⟩ := hHT
    exact ⟨T.returned, T.returnTime, ST.closeTime, FT,
      T.reaches_return, T.return_positive,
      Or.inr hST, hFTClose, hFTLt⟩
  · obtain ⟨_hreturnOrder, _htransition, FT, FH,
      _hFTClose, hFHClose, _hFTLt, hFHLt,
      _hlocalOrder, _hstrictOrder⟩ := hTH
    exact ⟨H.returned, H.returnTime, SH.closeTime, FH,
      H.reaches_return, H.return_positive,
      (by
        rcases hSH with h1 | h2 | h3 | h4
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl h3))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))),
      hFHClose, hFHLt⟩

end GeneralN
