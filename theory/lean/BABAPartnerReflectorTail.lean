import BABAInterlacementTail
import SixEventSharpClosure

/-!
# Raw BABA endpoints as reached lobe reflectors

This file never treats the sparse overwrite sequence as an Echo.IsRun.
It transports a sparse exact-lobe endpoint to literal Wiring dynamics,
preserves the raw close time, and leaves the foreign restoration crossing
as the exact residue.
-/

namespace GeneralN

/-- A direct lobe actually entered immediately before productive time k
and left immediately after it. -/
def RawReachedDirectLobeAt
    (w : Wiring) (start : Prod Nat Tongues) (k : Nat) : Prop :=
  Exists fun outside =>
  Exists fun state =>
    And
      (stepN w (k - 1) start =
        some (3 * rawWriterAt w start k, state))
      (And
        (stepN w (k + 1) start =
          some (outside, flipAt state (rawWriterAt w start k)))
        (And
          (w.link (3 * rawWriterAt w start k) = some outside)
          (IsReflector w (3 * rawWriterAt w start k) outside 2
            (fun _ => True)
            (fun u => flipAt u (rawWriterAt w start k)))))

/-- Normalize the orientation-free exact-lobe edge to 3*C+1 -> 3*C+2. -/
theorem exactLobeWrite_to_canonical_direct_lobe
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k) :
    w.link (3 * rawWriterAt w start k + 1) =
      some (3 * rawWriterAt w start k + 2) := by
  obtain ⟨outside, hforward, _hback, _hstem, _hreflector⟩ :=
    exactLobeWrite_to_raw_direct_lobe_reflector hN hprod hlobe
  let C := rawWriterAt w start k
  have hC : C < N := rawProductiveAt_writer_lt hN hprod
  have hflip := rawProductiveAt_restricted_flip hN hprod
  have hbit := restrict_eq_apply hflip hC
  have hbit' :
      (tonguesAt w start (k + 1)) C =
        !((tonguesAt w start k) C) := by
    simpa [C, flipAt] using hbit
  cases hstate : (tonguesAt w start k) C with
  | false =>
      have hafter : (tonguesAt w start (k + 1)) C = true := by
        rw [hbit', hstate]
        rfl
      simpa [C, selectedBranch, branchPort, hstate, hafter]
        using hforward
  | true =>
      have hafter : (tonguesAt w start (k + 1)) C = false := by
        rw [hbit', hstate]
        rfl
      have hreverse := w.symm _ _ hforward
      simpa [C, selectedBranch, branchPort, hstate, hafter]
        using hreverse

/-- A positive productive traversal of a canonical direct lobe is an
actually reached two-step reflection ending at raw post-time k+1. -/
theorem rawProductiveAt_on_canonical_lobe_reaches_close
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hlobe :
      w.link (3 * rawWriterAt w start k + 1) =
        some (3 * rawWriterAt w start k + 2))
    (hk : 0 < k) :
    RawReachedDirectLobeAt w start k := by
  let C := rawWriterAt w start k
  obtain ⟨cur, next, D, hD, hcur, hnext, hstep, hentry,
      hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hDC : D = C := by
    simpa [C] using hD
  subst D
  have hlobeC :
      w.link (3 * C + 1) = some (3 * C + 2) := by
    simpa [C] using hlobe
  have hlobeEdge :
      w.link (selectedBranch cur.2 C) =
        some (unmatchedBranch cur.2 C) := by
    cases hstate : cur.2 C with
    | false =>
        simpa [selectedBranch, unmatchedBranch, branchPort, hstate]
          using hlobeC
    | true =>
        have hreverse := w.symm _ _ hlobeC
        simpa [selectedBranch, unmatchedBranch, branchPort, hstate]
          using hreverse
  have hkSplit : k = (k - 1) + 1 := by omega
  cases hprev : stepN w (k - 1) start with
  | none =>
      have hnone : stepN w k start = none := by
        rw [hkSplit, stepN_add, hprev]
        rfl
      rw [hcur] at hnone
      contradiction
  | some prev =>
      have hprevStep : step w prev = some cur := by
        have h := hcur
        rw [hkSplit, stepN_add, hprev] at h
        simpa [stepN] using h
      have hprevParts := step_some_parts hprevStep
      have hlobeToEntry :
          w.link (selectedBranch cur.2 C) = some cur.1 := by
        rw [hentry]
        exact hlobeEdge
      have hprevExit :
          exitPort prev = selectedBranch cur.2 C :=
        Wiring.link_injective hprevParts.1 hlobeToEntry
      have hprevSwitch : prev.1 / 3 = C := by
        have hs := arrive_exit_switch prev.2 prev.1
        change exitPort prev / 3 = prev.1 / 3 at hs
        rw [hprevExit, selectedBranch_switch] at hs
        exact hs.symm
      have hprevStem : prev.1 % 3 = 0 := by
        by_cases hstem : prev.1 % 3 = 0
        · exact hstem
        · have hexitStem : exitPort prev % 3 = 0 := by
            unfold exitPort arrive
            rw [if_neg hstem]
            omega
          have hselectedBranch :=
            selectedBranch_is_branch cur.2 C
          rw [← hprevExit] at hselectedBranch
          exact (hselectedBranch hexitStem).elim
      have hprevPort : prev.1 = 3 * C := by
        have hnormalize := stem_eq_three_mul_div hprevStem
        omega
      have hprevState : prev.2 = cur.2 := by
        have harrived : cur.2 = arrivedTongues prev := hprevParts.2
        have hsame : arrivedTongues prev = prev.2 := by
          unfold arrivedTongues
          rw [hprevPort, arrive_stem_selected]
        exact (harrived.trans hsame).symm
      have hstem : w.link (3 * C) = some next.1 := by
        have hparts := (step_some_parts hstep).1
        rw [hexit] at hparts
        exact hparts
      have hprevCfg : prev = (3 * C, cur.2) := by
        apply Prod.ext
        · exact hprevPort
        · exact hprevState
      have hnextCfg :
          next = (next.1, flipAt cur.2 C) := by
        apply Prod.ext
        · rfl
        · exact hflip
      have hpre :
          stepN w (k - 1) start =
            some (3 * rawWriterAt w start k, cur.2) := by
        simpa [C, hprevCfg] using hprev
      have hpost :
          stepN w (k + 1) start =
            some (next.1,
              flipAt cur.2 (rawWriterAt w start k)) := by
        simpa [C] using hnext.trans (congrArg some hnextCfg)
      have hstemRaw :
          w.link (3 * rawWriterAt w start k) = some next.1 := by
        simpa [C] using hstem
      have hreflector :
          IsReflector w (3 * rawWriterAt w start k) next.1 2
            (fun _ => True)
            (fun u => flipAt u (rawWriterAt w start k)) := by
        simpa [C] using
          (lobe_isReflector w C next.1 hlobeC hstem)
      exact Exists.intro next.1 (Exists.intro cur.2
        (And.intro hpre
          (And.intro hpost (And.intro hstemRaw hreflector))))

/-- Sparse exact-lobe data at a positive productive event produces a
reached raw reflector at that exact close time. -/
theorem exactLobeWrite_to_reached_direct_lobe
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k)
    (hk : 0 < k) :
    RawReachedDirectLobeAt w start k := by
  exact rawProductiveAt_on_canonical_lobe_reaches_close hN hprod
    (exactLobeWrite_to_canonical_direct_lobe hN hprod hlobe) hk

/-- If either endpoint supplies the direct lobe edge, the later endpoint
traverses that same static edge and is an actually reached reflector. -/
theorem RawLastWriterFrame.endpoint_lobe_reaches_close
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues} {left right : Nat}
    (F : RawLastWriterFrame w N start left right)
    (hlobe :
      Or
        (Echo.ExactLobeWrite
          (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) left)
        (Echo.ExactLobeWrite
          (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) right)) :
    RawReachedDirectLobeAt w start right := by
  have hcanonical :
      w.link (3 * rawWriterAt w start right + 1) =
        some (3 * rawWriterAt w start right + 2) := by
    rcases hlobe with hopen | hclose
    · have hopenLink :=
        exactLobeWrite_to_canonical_direct_lobe
          hN F.open_productive hopen
      rw [F.same_writer] at hopenLink
      exact hopenLink
    · exact exactLobeWrite_to_canonical_direct_lobe
        hN F.close_productive hclose
  have hright : 0 < right :=
    Nat.lt_of_le_of_lt (Nat.zero_le left) F.order
  exact rawProductiveAt_on_canonical_lobe_reaches_close
    hN F.close_productive hcanonical hright

/-- Timing-preserving BABA endpoint reduction.  A lobe on the left frame
is transported to reroute; one on the right frame is transported to third.
The remaining branch is the literal foreign restoration crossing. -/
theorem RawBABAInterlacement.close_lobe_or_foreign_crossing
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third) :
    Or (RawReachedDirectLobeAt w start reroute)
      (Or (RawReachedDirectLobeAt w start third)
        (Echo.ForeignRestorationCrossing
          (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start)
          prior reroute second third)) := by
  rcases B.endpoint_lobe_or_foreign_crossing hN with
    hprior | hreroute | hsecond | hthird | hcross
  · exact Or.inl
      (B.leftFrame.endpoint_lobe_reaches_close hN (Or.inl hprior))
  · exact Or.inl
      (B.leftFrame.endpoint_lobe_reaches_close hN (Or.inr hreroute))
  · exact Or.inr (Or.inl
      (B.rightFrame.endpoint_lobe_reaches_close hN (Or.inl hsecond)))
  · exact Or.inr (Or.inl
      (B.rightFrame.endpoint_lobe_reaches_close hN (Or.inr hthird)))
  · exact Or.inr (Or.inr hcross)

/-- A novel third writer has an unconditional classification with exact
close timing: first-writer charge, reached lobe close, or the foreign
crossing on a strictly smaller overlap. -/
theorem RawThirdWriterNovelAt.first_charge_or_reached_close_or_crossing
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues} {first second third : Nat}
    (T : RawThirdWriterNovelAt w N start first second third) :
    Or
      (exists reroute,
        And (second < reroute)
          (And (reroute < third)
            (RawFirstWriterAt w N start reroute)))
      (exists prior reroute,
        exists B : RawBABAInterlacement
            w N start prior second reroute third,
          And (B.overlap < third - second)
            (Or (RawReachedDirectLobeAt w start reroute)
              (Or (RawReachedDirectLobeAt w start third)
                (Echo.ForeignRestorationCrossing
                  (rawOverwriteMachine w)
                  (rawOverwriteEntry w N start)
                  (rawOverwriteInitial start)
                  prior reroute second third)))) := by
  rcases T.first_charge_or_BABA_strict_descent hN with
    hcharge | ⟨prior, reroute, B, hstrict⟩
  · exact Or.inl hcharge
  · refine Or.inr ⟨prior, reroute, B, hstrict, ?_⟩
    exact B.close_lobe_or_foreign_crossing hN

end GeneralN
