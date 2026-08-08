import TwoToOneConfigurationCount

/-!
# Canonical existence of configuration representatives

For any finite sample and any finite configuration map, induction constructs a
list containing one sampled time for every visited configuration.  No
`eraseDups` API is required: when a new head configuration is already covered,
reuse the induction hypothesis; otherwise prepend the head time and its
configuration.

Combining these representatives with the two-state overwrite fibre theorem
removes the last finite-choice assumption from the concrete echo-trace count.
-/

namespace Echo

/-- Every finite sample has a duplicate-free configuration universe together
with one sampled representative time for each configuration. -/
theorem exists_configuration_representatives
    {α : Type} (cfg : Nat → α) [DecidableEq α] :
    ∀ sample : List Nat,
      ∃ configs : List α, ∃ reps : List Nat,
        configs.Nodup ∧
        reps.map cfg = configs ∧
        (∀ k ∈ reps, k ∈ sample) ∧
        (∀ k ∈ sample, cfg k ∈ configs) := by
  intro sample
  induction sample with
  | nil =>
      exact ⟨[], [], by simp⟩
  | cons k rest ih =>
      obtain ⟨configs, reps, hnd, hmap, hsub, hcover⟩ := ih
      by_cases hk : cfg k ∈ configs
      · refine ⟨configs, reps, hnd, hmap, ?_, ?_⟩
        · intro r hr
          exact List.mem_cons_of_mem _ (hsub r hr)
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hk
          · exact hcover r hr
      · refine ⟨cfg k :: configs, k :: reps, ?_, ?_, ?_, ?_⟩
        · exact List.nodup_cons.mpr ⟨hk, hnd⟩
        · simp only [List.map_cons]
          rw [hmap]
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hsub r hr)
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hcover r hr)

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Unconditional strict-base bound for a finite echo overwrite trace.**
No representative list is supplied by the caller.  The only semantic input
beyond the echo run is that the concrete boundary tongue trajectory executes a
fixed overwrite word determined by the finite echo configuration. -/
theorem finite_echo_overwrite_trace_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots entries sample : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hcells : cells.length ≤ N)
    (hslots : slots.length ≤ 2 * N)
    (hentriesNodup : entries.Nodup)
    (hentriesLength : entries.length ≤ 2 * N)
    (hentryCover : ∀ k ∈ sample, e k ∈ entries)
    (hks : ∀ k ∈ sample, globalLo ≤ k ∧ k ≤ globalHi)
    (hpartnerCover : ∀ k,
      m.star (m.cellOf (e k)) ∈ cells)
    (actionOf : Nat × List Nat → List Nat)
    (t0 : GeneralN.Tongues)
    (hndTongues : (sample.map
      (GeneralN.pinTrajectory
        (fun n => actionOf (configSnap m e r0 cells n)) t0)).Nodup) :
    blockCoreEighth sample.length ≤
      blockCoreEighth 2 *
        (blockCoreEighth (2*N) *
          (blockCoreEighth (4*N + 2) * 2^(7*N+18))) := by
  let cfg := configSnap m e r0 cells
  obtain ⟨configs, reps, hconfigsNodup,
      hrepsConfig, hrepsSubset, hconfigsCover⟩ :=
    exists_configuration_representatives cfg sample
  exact tongue_bound_of_config_representatives
    m e r0 hrun hr0 N globalLo globalHi
    cells slots entries sample reps frame
    hcells hslots hentriesNodup hentriesLength
    hentryCover hks hpartnerCover actionOf t0
    configs hconfigsNodup
    (by simpa [cfg] using hconfigsCover)
    (by simpa [cfg] using hrepsConfig)
    hrepsSubset hndTongues

end Echo
