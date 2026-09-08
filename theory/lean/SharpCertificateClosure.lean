import RepeatedNoveltyDecomposition

/-!
# Time shifts and productive-history coverage

Live time shifts preserve restricted vectors. Productive-step histories
cover every live prefix by induction. In a switch-simple trace the writer
labels are injective, supplying the finite coordinate count separately.
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

/-- A switch-simple trace visits each writer at most once. -/
theorem PhysicalTrace.rawWriterAt_injective
    {w : Wiring} {start finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) (hsimple : SwitchSimple passages)
    {i j : Nat} (hi : i < passages.length) (hj : j < passages.length)
    (heq : rawWriterAt w start i = rawWriterAt w start j) : i = j := by
  apply (List.getElem_inj (h₀ := by simpa using hi) (h₁ := by simpa using hj) hsimple).mp
  simpa [htrace.rawWriterAt_eq_passageSwitch_getElem hi,
    htrace.rawWriterAt_eq_passageSwitch_getElem hj] using heq

/-- The initial vector and post-vectors of productive steps cover every
live prefix, including repeated visits to a writer. -/
theorem restrictedTonguesAt_mem_rawProductiveHistory
    {w : Wiring} {N K : Nat} {start finish : Nat × Tongues}
    (hfinish : stepN w K start = some finish) :
    ∀ k, k ≤ K → restrictedTonguesAt w N start k ∈ rawProductiveHistory w N start K := by
  intro k
  induction k with
  | zero => intro _; simp [rawProductiveHistory]
  | succ k ih =>
      intro hk
      by_cases heq : restrictedTonguesAt w N start (k + 1) = restrictedTonguesAt w N start k
      · rw [heq]; exact ih (by omega)
      · exact List.mem_cons_of_mem _ (List.mem_map.mpr
          ⟨k, mem_rawProductiveTimes_iff.mpr ⟨by omega,
            Option.isSome_iff_exists.mpr (stepN_prefix_some hk hfinish), heq⟩, rfl⟩)

end GeneralN
