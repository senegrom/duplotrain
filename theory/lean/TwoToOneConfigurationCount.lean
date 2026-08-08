import EchoConfigCount
import EchoOverwriteFibre

/-!
# From finite configurations to concrete tongue states

Choose one representative time for every finite echo configuration visited by
a concrete sample.  The representatives have pairwise-distinct finite
configurations, so `finiteFrame_config_atMost_N_strict_bound` bounds their
number.  The overwrite theorem charges at most two pairwise-distinct concrete
tongue vectors to each configuration.  Hence the same strict exponential base
survives, with only a factor `2`.
-/

namespace Echo

/-- Size of one fibre of an arbitrary finite-valued map. -/
def finiteFibreSize {α : Type} [DecidableEq α]
    (f : Nat → α) (q : α) (ks : List Nat) : Nat :=
  (ks.filter (fun k => f k = q)).length

/-- Fibre sizes indexed by a duplicate-free finite value universe. -/
def finiteFibreSizes {α : Type} [DecidableEq α]
    (values : List α) (f : Nat → α) (ks : List Nat) : List Nat :=
  values.map (fun q => finiteFibreSize f q ks)

private theorem finiteFibreSize_cons
    {α : Type} [DecidableEq α]
    (f : Nat → α) (q : α) (k : Nat) (ks : List Nat) :
    finiteFibreSize f q (k :: ks) =
      (if f k = q then 1 else 0) + finiteFibreSize f q ks := by
  by_cases h : f k = q <;>
    simp [finiteFibreSize, h, Nat.add_comm]

private theorem finite_indicator_zero
    {α : Type} [DecidableEq α] (v : α) :
    ∀ xs : List α,
      v ∉ xs →
      (xs.map (fun q => if v = q then 1 else 0)).sum = 0 := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons q rest ih =>
      intro hnot
      have hvq : v ≠ q := by
        intro h
        exact hnot (h ▸ List.mem_cons_self)
      have hvrest : v ∉ rest := by
        intro hv
        exact hnot (List.mem_cons_of_mem _ hv)
      simp [hvq, ih hvrest]

private theorem finite_indicator_one
    {α : Type} [DecidableEq α] (v : α) :
    ∀ xs : List α,
      xs.Nodup → v ∈ xs →
      (xs.map (fun q => if v = q then 1 else 0)).sum = 1 := by
  intro xs
  induction xs with
  | nil =>
      intro _ hv
      cases hv
  | cons q rest ih =>
      intro hnd hv
      have hnd' := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hv with hvq | hvrest
      · subst q
        have hzero := finite_indicator_zero v rest hnd'.1
        simp [hzero]
      · have hvq : v ≠ q := by
          intro h
          apply hnd'.1
          exact h.symm ▸ hvrest
        have hone := ih hnd'.2 hvrest
        simp [hvq, hone]

private theorem finite_sum_map_add {α : Type}
    (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

/-- Finite fibres partition a list exactly. -/
theorem finiteFibreSizes_sum
    {α : Type} [DecidableEq α]
    (values : List α) (f : Nat → α) :
    ∀ ks : List Nat,
      values.Nodup →
      (∀ k ∈ ks, f k ∈ values) →
      (finiteFibreSizes values f ks).sum = ks.length := by
  intro ks
  induction ks with
  | nil =>
      intro _ _
      simp [finiteFibreSizes, finiteFibreSize]
  | cons k rest ih =>
      intro hnd hcover
      have hk : f k ∈ values := hcover k List.mem_cons_self
      have hrest : ∀ j ∈ rest, f j ∈ values := by
        intro j hj
        exact hcover j (List.mem_cons_of_mem _ hj)
      have hpoint :
          finiteFibreSizes values f (k :: rest) =
            values.map (fun q =>
              (if f k = q then 1 else 0) +
                finiteFibreSize f q rest) := by
        unfold finiteFibreSizes
        apply List.map_congr_left
        intro q _
        exact finiteFibreSize_cons f q k rest
      rw [hpoint, finite_sum_map_add]
      rw [finite_indicator_one (f k) values hnd hk,
        ih hnd hrest]
      simp

private theorem sum_le_length_mul_bound
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
        x + rest.sum ≤ B + rest.length * B :=
          Nat.add_le_add hx hi
        _ = (rest.length + 1) * B := by
          simp [Nat.add_mul, Nat.add_comm]

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Concrete finite-bound theorem from configuration representatives.**
The caller supplies one sampled time for each visited configuration; the next
file constructs those representatives canonically. -/
theorem tongue_bound_of_config_representatives
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots entries sample reps : List Nat)
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
    (configs : List (Nat × List Nat))
    (hconfigsNodup : configs.Nodup)
    (hconfigsCover : ∀ k ∈ sample,
      configSnap m e r0 cells k ∈ configs)
    (hrepsConfig : reps.map (configSnap m e r0 cells) = configs)
    (hrepsSubset : ∀ k ∈ reps, k ∈ sample)
    (hndTongues : (sample.map
      (GeneralN.pinTrajectory
        (fun n => actionOf (configSnap m e r0 cells n)) t0)).Nodup) :
    blockCoreEighth sample.length ≤
      blockCoreEighth 2 *
        (blockCoreEighth (2*N) *
          (blockCoreEighth (4*N + 2) * 2^(7*N+18))) := by
  let cfg := configSnap m e r0 cells
  let tongue := GeneralN.pinTrajectory
    (fun n => actionOf (cfg n)) t0
  let sizes := finiteFibreSizes configs cfg sample
  have hsum : sizes.sum = sample.length := by
    dsimp [sizes]
    exact finiteFibreSizes_sum configs cfg sample
      hconfigsNodup hconfigsCover
  have heach : ∀ s ∈ sizes, s ≤ 2 := by
    intro s hs
    dsimp [sizes, finiteFibreSizes] at hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    let fibre := sample.filter (fun k => cfg k = q)
    have hsame : ∀ k ∈ fibre, cfg k = q := by
      intro k hk
      have hkFilter : k ∈ sample.filter (fun j => cfg j = q) := by
        simpa only [fibre] using hk
      exact of_decide_eq_true (List.mem_filter.mp hkFilter).2
    have hndFibre : (fibre.map tongue).Nodup := by
      dsimp [fibre, tongue]
      exact map_filter_nodup
        (GeneralN.pinTrajectory
          (fun n => actionOf (cfg n)) t0)
        (fun k => cfg k = q) hndTongues
    have htwo := config_tongue_fibre_length_le_two
      m e r0 hrun cells hpartnerCover actionOf t0
      q fibre (by simpa [cfg] using hsame) (by
        simpa [cfg, tongue] using hndFibre)
    simpa [finiteFibreSize, fibre] using htwo
  have hsample : sample.length ≤ 2 * configs.length := by
    have hsumBound := sum_le_length_mul_bound sizes 2 heach
    rw [hsum] at hsumBound
    have hlen : sizes.length = configs.length := by
      simp [sizes, finiteFibreSizes]
    rw [hlen] at hsumBound
    simpa [Nat.mul_comm] using hsumBound
  have hrepsConfigNodup :
      (reps.map (configSnap m e r0 cells)).Nodup := by
    rw [hrepsConfig]
    exact hconfigsNodup
  have hrepsEntry : ∀ k ∈ reps, e k ∈ entries := by
    intro k hk
    exact hentryCover k (hrepsSubset k hk)
  have hrepsRange : ∀ k ∈ reps,
      globalLo ≤ k ∧ k ≤ globalHi := by
    intro k hk
    exact hks k (hrepsSubset k hk)
  have hconfigBound := finiteFrame_config_atMost_N_strict_bound
    m e r0 hrun hr0 N globalLo globalHi
    cells slots entries reps frame hcells hslots
    hentriesNodup hentriesLength hrepsEntry hrepsRange
    hrepsConfigNodup
  have hlenReps : reps.length = configs.length := by
    have h := congrArg List.length hrepsConfig
    simpa using h
  have hsample' : sample.length ≤ 2 * reps.length := by
    rwa [hlenReps]
  have hmono := blockCoreEighth_mono hsample'
  rw [blockCoreEighth_mul] at hmono
  exact Nat.le_trans hmono
    (Nat.mul_le_mul_left (blockCoreEighth 2) hconfigBound)

end Echo
