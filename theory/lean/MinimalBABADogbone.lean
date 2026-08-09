import BABAInterlacementTail
import TrackLobe

/-!
# The overlap-minimal BABA endpoint and its physical lobe

`BABAInterlacementTail` deliberately uses a sparse overwrite sequence only
for last-writer bookkeeping.  It is not an `Echo.IsRun`.  This file therefore
does not apply echo dynamics to that sequence.  Instead it translates an
`Echo.ExactLobeWrite` at a *raw productive time* back through
`rawOverwriteEntry` and `rawOverwrite_oldSlot_eq_selected` to an actual edge
of `Wiring.link`.  The edge is the two branch ports of one switch, so the raw
track contains the genuine lobe consumed by `lobe_hop` and
`lobe_isReflector`.

The subsequent section isolates the still-global part of the BABA argument:
an overlap-minimal crossing must supply the reflector at the other end of the
train's corridor before `reflector_period` can yield the four-vector tail.
-/

namespace GeneralN

/-- An exact sparse lobe write at a raw productive event is an actual track
edge from the branch selected immediately before the event to the other
branch of the same switch.  The proof explicitly excludes the `none` branch
of the totalised `wireBar`. -/
theorem rawExactLobeWrite_selected_to_unmatched
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k) :
    w.link
        (selectedBranch (tonguesAt w start k)
          (rawWriterAt w start k)) =
      some
        (unmatchedBranch (tonguesAt w start k)
          (rawWriterAt w start k)) := by
  let C := rawWriterAt w start k
  have hC : C < N := rawProductiveAt_writer_lt hN hprod
  have hflip := rawProductiveAt_restricted_flip hN hprod
  have hbit := restrict_eq_apply hflip hC
  have hbit' :
      (tonguesAt w start (k + 1)) C =
        !((tonguesAt w start k) C) := by
    simpa [C, flipAt] using hbit
  have hafter :
      selectedBranch (tonguesAt w start (k + 1)) C =
        unmatchedBranch (tonguesAt w start k) C := by
    unfold selectedBranch unmatchedBranch
    rw [hbit']
  have hentry :
      rawOverwriteEntry w N start (k + 1) =
        selectedBranch (tonguesAt w start (k + 1)) C := by
    simp [rawOverwriteEntry, hprod, C]
  have hold :
      Echo.oldSlot (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) k =
        selectedBranch (tonguesAt w start k) C := by
    simpa [C] using rawOverwrite_oldSlot_eq_selected hN hprod
  have hwire :
      unmatchedBranch (tonguesAt w start k) C =
        wireBar w (selectedBranch (tonguesAt w start k) C) := by
    calc
      unmatchedBranch (tonguesAt w start k) C =
          selectedBranch (tonguesAt w start (k + 1)) C := hafter.symm
      _ = rawOverwriteEntry w N start (k + 1) := hentry.symm
      _ = (rawOverwriteMachine w).bar
          (Echo.oldSlot (rawOverwriteMachine w)
            (rawOverwriteEntry w N start) (rawOverwriteInitial start) k) :=
          hlobe.1
      _ = wireBar w (selectedBranch (tonguesAt w start k) C) := by
          rw [hold]
          rfl
  cases hlink : w.link (selectedBranch (tonguesAt w start k) C) with
  | none =>
      exfalso
      have hfixed := wireBar_of_unlinked hlink
      have heq :
          unmatchedBranch (tonguesAt w start k) C =
            selectedBranch (tonguesAt w start k) C :=
        hwire.trans hfixed
      exact (selected_unmatched_ne (tonguesAt w start k) C) heq.symm
  | some q =>
      have hq : q = unmatchedBranch (tonguesAt w start k) C := by
        have hw := wireBar_of_link hlink
        exact (hwire.trans hw).symm
      simpa [C, hq] using hlink

/-- Orientation-free branch linkage normalized to the canonical
`3*C+1 ↔ 3*C+2` lobe used by `GeneralN.lobe_hop`. -/
theorem rawExactLobeWrite_normalized_link
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k) :
    w.link (3 * rawWriterAt w start k + 1) =
      some (3 * rawWriterAt w start k + 2) := by
  let C := rawWriterAt w start k
  have hlink := rawExactLobeWrite_selected_to_unmatched hN hprod hlobe
  cases hstate : (tonguesAt w start k) C with
  | false =>
      simpa [C, selectedBranch, unmatchedBranch, branchPort, hstate]
        using hlink
  | true =>
      have hback := w.symm _ _ hlink
      simpa [C, selectedBranch, unmatchedBranch, branchPort, hstate]
        using hback

/-- The normalized raw branch edge is the genuine two-step lobe hop. -/
theorem rawExactLobeWrite_lobe_hop
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k outside : Nat}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k)
    (hstem : w.link (3 * rawWriterAt w start k) = some outside)
    (u : Tongues) :
    stepN w 2 (3 * rawWriterAt w start k, u) =
      some (outside, flipAt u (rawWriterAt w start k)) := by
  exact lobe_hop w (rawWriterAt w start k) outside u
    (rawExactLobeWrite_normalized_link hN hprod hlobe) hstem

/-- Reflector-interface form of the direct raw lobe bridge. -/
theorem rawExactLobeWrite_isReflector
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k outside : Nat}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k)
    (hstem : w.link (3 * rawWriterAt w start k) = some outside) :
    IsReflector w (3 * rawWriterAt w start k) outside 2
      (fun _ => True) (fun u => flipAt u (rawWriterAt w start k)) := by
  exact lobe_isReflector w (rawWriterAt w start k) outside
    (rawExactLobeWrite_normalized_link hN hprod hlobe) hstem

/-- A literal lobe edge, oriented by the current tongue, is already the
nondegenerate manufactured reflector expected by the first-revisit theory.
There is no hidden echo-machine step here: the runway and candy tail are
empty, and the sole recorded passage is the physical selected-to-unmatched
branch edge. -/
def manufacturedFlipReflectorOfSelectedLobe
    {w : Wiring} (C outside : Nat) (u : Tongues)
    (hbranch :
      w.link (selectedBranch u C) = some (unmatchedBranch u C))
    (hstem : w.link (3 * C) = some outside) :
    ManufacturedFlipReflector w (3 * C) outside where
  base := u
  mouthState := u
  returnState := u
  afterReturn := flipAt u C
  runway := []
  candy := []
  mouth := 3 * C
  firstArm := selectedBranch u C
  secondArm := unmatchedBranch u C
  runwayTrace := PhysicalTrace.nil (3 * C, u)
  candyTrace :=
    PhysicalTrace.cons (arrive_stem_selected u C) hbranch
      (PhysicalTrace.nil (unmatchedBranch u C, u))
  simple := by
    simp [SwitchSimple, passageSwitch, selectedBranch_switch]
  crossed := arrive_unmatched_pivots u C
  arms_ne := selected_unmatched_ne u C
  entryEdge := w.symm _ _ hstem

/-- The exact raw endpoint lobe, together with the actual external stem edge
used by its productive step, packages as a `ManufacturedFlipReflector`.
The returned endpoint is also the configuration reached at raw time `k+1`.
-/
theorem rawExactLobeWrite_manufacturedFlipReflector
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k) :
    ∃ next : Nat × Tongues,
      stepN w (k + 1) start = some next ∧
      w.link (3 * rawWriterAt w start k) = some next.1 ∧
      Nonempty (ManufacturedFlipReflector w
        (3 * rawWriterAt w start k) next.1) := by
  obtain ⟨next, hnext, hstem⟩ :=
    rawProductiveAt_fixed_stem_successor hN hprod
  have hbranch := rawExactLobeWrite_selected_to_unmatched hN hprod hlobe
  refine ⟨next, hnext, hstem, ⟨?_⟩⟩
  exact manufacturedFlipReflectorOfSelectedLobe
    (rawWriterAt w start k) next.1 (tonguesAt w start k)
    hbranch hstem

/-- A positive raw exact-lobe event is not merely a static edge certificate:
the two actual raw steps ending at `k` are the lobe reflection.  Immediately
before them the train faces the lobe stem; immediately afterwards it is back
across that stem's external edge with exactly that tongue flipped. -/
theorem rawExactLobeWrite_observed_reflection
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k)
    (hk : 0 < k) :
    ∃ outside state,
      stepN w (k - 1) start =
        some (3 * rawWriterAt w start k, state) ∧
      stepN w (k + 1) start =
        some (outside, flipAt state (rawWriterAt w start k)) ∧
      w.link (3 * rawWriterAt w start k) = some outside := by
  let C := rawWriterAt w start k
  obtain ⟨cur, next, D, hD, hcur, hnext, hstep, hentry,
      hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hDC : D = C := by simpa [C] using hD
  subst D
  have hcurState : tonguesAt w start k = cur.2 := by
    simp [tonguesAt, hcur]
  have hlobeEdge := rawExactLobeWrite_selected_to_unmatched hN hprod hlobe
  rw [hcurState] at hlobeEdge
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
      have hprevExit : exitPort prev = selectedBranch cur.2 C :=
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
          have hselectedBranch := selectedBranch_is_branch cur.2 C
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
      refine ⟨next.1, cur.2, ?_, ?_, hstem⟩
      · have hprevCfg : prev = (3 * C, cur.2) := by
          apply Prod.ext
          · exact hprevPort
          · exact hprevState
        simpa [C, hprevCfg] using hprev
      · have hnextCfg : next = (next.1, flipAt cur.2 C) := by
          apply Prod.ext
          · rfl
          · exact hflip
        dsimp [C] at hnextCfg
        exact hnext.trans (congrArg some hnextCfg)

end GeneralN
