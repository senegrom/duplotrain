import RelevantFibonacciPhysicalBound
import RelevantEdgeFibonacciConfigBound

/-!
# Best current full physical tongue-vector bound

Using one support coordinate per physical jump edge improves the finite
configuration count inside the existing overwrite-prefixAt bridge.  The direct
physical bound is

    T ≤ 2*(N+1)*(2*N)*((N+1)*fibBalancedCapacity N + 4).

With `fibBalancedCapacity N = 2^(N/2) * F_((N+1)/2+2)`, this is
`O(N^3 * (sqrt (2*phi))^N)` with base about `1.79891`.
-/

namespace Echo

private theorem edgeFibPhysical_sum_le
    (xs : List Nat) (B : Nat)
    (h : ∀ x ∈ xs, x ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hx := h x List.mem_cons_self
      have hr : ∀ y ∈ rest, y ≤ B := by
        intro y hy
        exact h y (List.mem_cons_of_mem _ hy)
      have hi := ih hr
      simp only [List.sum_cons, List.length_cons]
      calc
        x + rest.sum ≤ B + rest.length * B := Nat.add_le_add hx hi
        _ = (rest.length + 1) * B := by
          simp [Nat.add_mul, Nat.add_comm]

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Best current all-prefixAt bound over a relevant finite echo trace.** -/
theorem relevant_echo_physical_prefix_edge_fibonacci_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots entries sample : List Nat)
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0 globalLo globalHi cells)
    (hcells : cells.length ≤ N)
    (hslots : slots.length ≤ 2 * N)
    (hentriesNodup : entries.Nodup)
    (hentriesLength : entries.length ≤ 2 * N)
    (owner prefixAt : Nat → Nat)
    (hownerEntry : ∀ x ∈ sample, e (owner x) ∈ entries)
    (hownerRange : ∀ x ∈ sample,
      globalLo ≤ owner x ∧ owner x ≤ globalHi)
    (hpartnerCover : ∀ k,
      m.star (m.cellOf (e k)) ∈ cells)
    (actionOf : Nat × List Nat → List Nat)
    (t0 : GeneralN.Tongues)
    (observed : Nat → GeneralN.Tongues)
    (hprefix : ∀ x ∈ sample, prefixAt x ≤ N)
    (hobserve : ∀ x ∈ sample,
      observed x =
        GeneralN.pinList
          ((actionOf (configSnap m e r0 cells (owner x))).take
            (prefixAt x))
          (GeneralN.pinTrajectory
            (fun n => actionOf (configSnap m e r0 cells n))
            t0 (owner x)))
    (hndObserved : (sample.map observed).Nodup) :
    sample.length ≤
      2 * (N + 1) * ((2*N) * ((N + 1) * fibBalancedCapacity N + 4)) := by
  let cfg := configSnap m e r0 cells
  let ownerTimes := sample.map owner
  obtain ⟨configs, reps, hconfigsNodup,
      hrepsConfig, hrepsSubset, hconfigsCover⟩ :=
    exists_configuration_representatives cfg ownerTimes
  have hphysicalConfigCover : ∀ x ∈ sample, cfg (owner x) ∈ configs := by
    intro x hx
    apply hconfigsCover (owner x)
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  let configSizes := finiteFibreSizes configs
    (fun x => cfg (owner x)) sample
  have hconfigSum : configSizes.sum = sample.length := by
    dsimp [configSizes]
    exact finiteFibreSizes_sum configs
      (fun x => cfg (owner x)) sample
      hconfigsNodup hphysicalConfigCover
  have hconfigEach : ∀ s ∈ configSizes, s ≤ 2 * (N + 1) := by
    intro s hs
    dsimp [configSizes, finiteFibreSizes] at hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    let configFibre := sample.filter (fun x => cfg (owner x) = q)
    have hconfigFibrePrefix : ∀ x ∈ configFibre,
        prefixAt x ∈ List.range (N + 1) := by
      intro x hx
      have hxFilter : x ∈ sample.filter
          (fun y => cfg (owner y) = q) := by
        simpa only [configFibre] using hx
      have hxSample := (List.mem_filter.mp hxFilter).1
      exact List.mem_range.mpr (by
        have hp := hprefix x hxSample
        omega)
    let prefixSizes := finiteFibreSizes (List.range (N + 1))
      prefixAt configFibre
    have hprefixSum : prefixSizes.sum = configFibre.length := by
      dsimp [prefixSizes]
      exact finiteFibreSizes_sum (List.range (N + 1))
        prefixAt configFibre List.nodup_range hconfigFibrePrefix
    have hprefixEach : ∀ z ∈ prefixSizes, z ≤ 2 := by
      intro z hz
      dsimp [prefixSizes, finiteFibreSizes] at hz
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
      let prefixFibre := configFibre.filter (fun x => prefixAt x = r)
      have hsame : ∀ x ∈ prefixFibre,
          configSnap m e r0 cells (owner x) = q := by
        intro x hx
        have hxOuter := (List.mem_filter.mp hx).1
        have hxConfig : x ∈ sample.filter
            (fun y => cfg (owner y) = q) := by
          simpa only [configFibre] using hxOuter
        exact of_decide_eq_true (List.mem_filter.mp hxConfig).2
      have hpref : ∀ x ∈ prefixFibre, prefixAt x = r := by
        intro x hx
        exact of_decide_eq_true (List.mem_filter.mp hx).2
      have hsampleOf : ∀ x ∈ prefixFibre, x ∈ sample := by
        intro x hx
        have hxOuter := (List.mem_filter.mp hx).1
        have hxConfig : x ∈ sample.filter
            (fun y => cfg (owner y) = q) := by
          simpa only [configFibre] using hxOuter
        exact (List.mem_filter.mp hxConfig).1
      have hndConfigFibre : (configFibre.map observed).Nodup := by
        dsimp [configFibre]
        exact map_filter_nodup observed
          (fun x => cfg (owner x) = q) hndObserved
      have hndPrefixFibre : (prefixFibre.map observed).Nodup := by
        dsimp [prefixFibre]
        exact map_filter_nodup observed
          (fun x => prefixAt x = r) hndConfigFibre
      have htwo := physical_prefix_fibre_length_le_two
        m e r0 hrun cells hpartnerCover actionOf t0
        owner prefixAt observed q r prefixFibre hsame hpref
        (fun x hx => hobserve x (hsampleOf x hx))
        hndPrefixFibre
      simpa [finiteFibreSize, prefixFibre] using htwo
    have hprefixBound := edgeFibPhysical_sum_le prefixSizes 2 hprefixEach
    rw [hprefixSum] at hprefixBound
    have hprefixLen : prefixSizes.length = N + 1 := by
      simp [prefixSizes, finiteFibreSizes]
    rw [hprefixLen] at hprefixBound
    show configFibre.length ≤ 2 * (N + 1)
    rw [Nat.mul_comm]
    exact hprefixBound
  have hsampleBound := edgeFibPhysical_sum_le
    configSizes (2 * (N + 1)) hconfigEach
  rw [hconfigSum] at hsampleBound
  have hconfigLen : configSizes.length = configs.length := by
    simp [configSizes, finiteFibreSizes]
  rw [hconfigLen] at hsampleBound
  have hrepsConfigNodup : (reps.map (configSnap m e r0 cells)).Nodup := by
    rw [hrepsConfig]
    exact hconfigsNodup
  have hrepsEntry : ∀ k ∈ reps, e k ∈ entries := by
    intro k hk
    have hkOwner : k ∈ ownerTimes := hrepsSubset k hk
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hkOwner
    exact hownerEntry x hx
  have hrepsRange : ∀ k ∈ reps, globalLo ≤ k ∧ k ≤ globalHi := by
    intro k hk
    have hkOwner : k ∈ ownerTimes := hrepsSubset k hk
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hkOwner
    exact hownerRange x hx
  have hconfigBound := relevantFrame_config_atMost_N_edge_fibonacci_bound
    m e r0 hrun hr0 N globalLo globalHi cells slots entries reps
    frame hfullRelevant hcells hslots hentriesNodup hentriesLength
    hrepsEntry hrepsRange hrepsConfigNodup
  have hlenReps : reps.length = configs.length := by
    have h := congrArg List.length hrepsConfig
    simpa using h
  have hsampleReps : sample.length ≤ (2 * (N + 1)) * reps.length := by
    rw [← hlenReps] at hsampleBound
    rw [Nat.mul_comm]
    exact hsampleBound
  exact Nat.le_trans hsampleReps
    (Nat.mul_le_mul_left (2 * (N + 1)) hconfigBound)

end Echo

namespace GeneralN

/-- **Best current physical bound from a constructible relevant overwrite
compilation.** -/
theorem physical_edge_fibonacci_bound_of_compilation
    {w : Wiring} {N : Nat} {c0 : Nat × Tongues}
    {sample : List Nat} {globalLo globalHi : Nat}
    (comp : RelevantPhysicalOverwriteCompilation w N c0 sample
      globalLo globalHi)
    (hnd : (sample.map fun k =>
      VectorCount.restrict N (tonguesAt w c0 k)).Nodup) :
    sample.length ≤
      2 * (N + 1) *
        ((2*N) * ((N + 1) * Echo.fibBalancedCapacity N + 4)) := by
  let observed := fun k => tonguesAt w c0 k
  have hndObserved : (sample.map observed).Nodup := by
    apply FiniteListBounds.nodup_map_of_fibre sample observed
      (fun k => VectorCount.restrict N (tonguesAt w c0 k))
    · intro i hi j hj heq
      exact congrArg (VectorCount.restrict N) heq
    · exact hnd
  exact Echo.relevant_echo_physical_prefix_edge_fibonacci_bound
    comp.machine comp.echoEntry comp.initialRegister
    comp.run comp.initialRegister_wellFormed
    N globalLo globalHi comp.cells comp.slots comp.entries sample
    comp.frame comp.full_edges_relevant
    comp.cells_length comp.slots_length
    comp.entries_nodup comp.entries_length
    comp.owner comp.prefixAt comp.owner_entry comp.owner_range
    comp.partner_cover comp.actionOf comp.initialTongues
    observed comp.prefix_length comp.physical_tongues hndObserved

end GeneralN
