import SharpStateLawAssembly

/-!
# Time shifts and first-writer history coverage

Live time shifts preserve restricted vectors. A switch-simple trace has
no repeated productive writer, so induction covers every vector by the
initial state and the post-state of each first productive write.
-/

namespace GeneralN

/-- Transport one live post-time from an ambient raw run to a reached local
run. -/
theorem restrictedTonguesAt_sub_of_reach
    {w : Wiring} {N shift t : Nat}
    {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hshift : shift ≤ t)
    (hlive : (stepN w t start).isSome) :
    restrictedTonguesAt w N start t =
      restrictedTonguesAt w N middle (t - shift) := by
  have ht : t = shift + (t - shift) := by omega
  have h := restrictedTonguesAt_add_of_reaches (N := N) hreach
    (stepN_suffix_some_of_reaches hreach (by rwa [← ht]))
  rwa [← ht] at h

/-- A historical prefix adds no cost to a novelty cover of its shifted tail. -/
theorem NoveltyCoverOn.prepend
    {w : Wiring} {N K budget : Nat} {start middle : Nat × Tongues}
    {times localTimes : List Nat} {history : List (List Bool)}
    (hlocal : NoveltyCoverOn w N middle localTimes history budget)
    (hreach : stepN w K start = some middle)
    (hprefix : ∀ k, k ≤ K → restrictedTonguesAt w N start k ∈ history)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hmem : ∀ k ∈ times, K < k → k - K ∈ localTimes) :
    NoveltyCoverOn w N start times history budget := by
  obtain ⟨fresh, hfresh, hcover⟩ := hlocal
  refine ⟨fresh, hfresh, ?_⟩
  intro k hk
  by_cases hle : k ≤ K
  · exact List.mem_append_left _ (hprefix k hle)
  · rw [restrictedTonguesAt_sub_of_reach hreach (by omega) (hlive k hk)]
    exact hcover _ (hmem k hk (by omega))

theorem PhysicalTrace.rawWriterAt_eq_passageSwitch_getElem
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) :
    ∀ {k : Nat} (hk : k < passages.length),
      rawWriterAt w start k = passageSwitch passages[k] := by
  intro k hk
  induction htrace generalizing k with
  | nil => simp at hk
  | @cons p x q u v passages finish harrive hlink tail ih =>
      cases k with
      | zero =>
          simp [rawWriterAt, rawEntryAt, stepN, passageSwitch]
      | succ k =>
          have hkTail : k < passages.length := by simpa using hk
          obtain ⟨cfg, hcfg⟩ := stepN_prefix_some (Nat.le_of_lt hkTail) tail.sound
          simpa [rawWriterAt, rawEntryAt, stepN, step, harrive, hlink, hcfg] using ih hkTail

/-- Every productive event inside a switch-simple physical construction is
globally the first productive event of its writer.  This is the raw-history
extraction missing from the older five-frame formulation: passage simplicity
controls the complete absolute run prefix, not merely a local certificate. -/
theorem PhysicalTrace.rawProductiveAt_first_of_switchSimple
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    ∀ {k : Nat}, k < passages.length →
      RawProductiveAt w N start k →
      RawFirstWriterAt w N start k := by
  intro k hk hprod
  refine ⟨hprod, ?_⟩
  intro j hj hprodj hwriter
  have hjBound : j < passages.length := Nat.lt_trans hj hk
  have hwriterJ := htrace.rawWriterAt_eq_passageSwitch_getElem hjBound
  have hwriterK := htrace.rawWriterAt_eq_passageSwitch_getElem hk
  have hpair := List.pairwise_iff_getElem.mp hsimple
  have hne := hpair j k (by simpa using hjBound) (by simpa using hk) hj
  apply hne
  simpa [hwriterJ, hwriterK] using hwriter

/-- Every state of a switch-simple physical construction prefix belongs to
the canonical initial-plus-first-writer history.  This is an unconditional
global raw-history extraction, including the endpoint of the trace. -/
theorem PhysicalTrace.restrictedTonguesAt_mem_rawFirstWriterHistory
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    ∀ k, k ≤ passages.length →
      restrictedTonguesAt w N start k ∈
        rawFirstWriterHistory w N start passages.length := by
  intro k
  induction k with
  | zero => intro _; simp [rawFirstWriterHistory]
  | succ k ih =>
      intro hk
      by_cases heq : restrictedTonguesAt w N start (k + 1) = restrictedTonguesAt w N start k
      · rw [heq]; exact ih (by omega)
      · have hprod : RawProductiveAt w N start k :=
          ⟨Option.isSome_iff_exists.mpr (stepN_prefix_some hk htrace.sound), heq⟩
        have hfirst := htrace.rawProductiveAt_first_of_switchSimple hsimple (by omega) hprod
        exact List.mem_cons_of_mem _ (List.mem_map.mpr
          ⟨k, mem_rawFirstWriterTimes_iff.mpr ⟨by omega, hfirst⟩, rfl⟩)

end GeneralN
