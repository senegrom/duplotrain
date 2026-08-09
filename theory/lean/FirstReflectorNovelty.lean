import TrackNoveltyCover

/-!
# Novelty of one manufactured-reflector activation

The first repeated switch in a switch-simple exploration manufactures either
a stay reflector or a flip reflector.  Its forced activation is not a second
long source of states: it is the contact step followed by the exact reverse of
the old runway.  Consequently the complete activation contributes at most one
new tongue vector, independently of the runway length.

This is a local raw-track theorem.  It does not claim the still-open global
`StateLaw`; the remaining global work is to combine the two manufactured
explorations and the protected-repair residual without charging overlapping
support twice.
-/

namespace GeneralN

/-- The local return passage of either manufactured-reflector constructor
contacts the retained runway at its mouth and produces the advertised
activated state. -/
theorem ManufacturedReflector.return_arrive_mouth
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    arrive A.preReturn.2 A.preReturn.1 =
      (A.mouthConfig.1, A.activatedState) := by
  cases A with
  | flip R =>
      exact R.crossed
  | stay R =>
      obtain ⟨after, hhead⟩ := R.coreTrace.head_arrive.2
      have hsound := R.coreTrace.sound
      have hafter : after = R.returnState := by
        simp [stepN, step, hhead, R.selfLink] at hsound
        exact hsound
      have hback := arrive_back R.mouthState R.mouth
      rw [hhead, hafter] at hback
      exact hback

/-- The runway is among the support paths retained by a manufactured
reflector, so a grooved support state grooves the runway itself. -/
theorem ManufacturedReflector.runway_grooved
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) {state : Tongues}
    (hpaths : PathGrooves A.toSupported.paths state) :
    PassagesGrooved state A.runway :=
  hpaths A.runway A.runway_mem_support

/-- **One activation, one novelty.**

At depth zero the pre-return vector is still present.  Every positive depth
through the contact and complete reverse runway has exactly the activated
vector.  If the pre-return vector is historical, the whole activation
therefore has a one-vector novelty cover. -/
theorem ManufacturedReflector.activation_one_novelty_cover
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    (N : Nat) (history : List (List Bool))
    (hpre : VectorCount.restrict N A.preReturn.2 ∈ history)
    (times : List Nat)
    (htimes : ∀ d ∈ times, d ≤ A.runway.length + 1) :
    NoveltyCoverOn w N A.preReturn times history 1 := by
  exact completed_retrace_one_novelty_cover
    A.runway_trace
    (A.runway_grooved hpaths)
    A.entryEdge
    A.return_arrive_mouth
    N history hpre times htimes

/-- Absolute-time version for an activation embedded in the original train
run.  The one-vector budget is unchanged by the preceding journey. -/
theorem ManufacturedReflector.activation_at_one_novelty_cover
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some A.preReturn)
    (N : Nat) (history : List (List Bool))
    (hpre : VectorCount.restrict N A.preReturn.2 ∈ history)
    (times : List Nat)
    (htimes : ∀ j ∈ times,
      K ≤ j ∧ j ≤ K + A.runway.length + 1) :
    NoveltyCoverOn w N start times history 1 := by
  exact completed_retrace_at_one_novelty_cover
    A.runway_trace
    (A.runway_grooved hpaths)
    A.entryEdge
    A.return_arrive_mouth
    hreach N history hpre times htimes

/-- **A manufactured first reflector costs only one state beyond its outward
prefix.**  If the train reaches the pre-return configuration by time `K`, all
vectors through the complete activation lie among the `K+1` prefix vectors
and the single activated vector. -/
theorem ManufacturedReflector.prefix_and_activation_one_novelty_cover
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some A.preReturn)
    (N : Nat) (times : List Nat)
    (htimes : ∀ j ∈ times, j ≤ K + A.runway.length + 1) :
    NoveltyCoverOn w N start times
      ((List.range (K+1)).map (restrictedTonguesAt w N start)) 1 := by
  let history :=
    (List.range (K+1)).map (restrictedTonguesAt w N start)
  have hvectorK : restrictedTonguesAt w N start K =
      VectorCount.restrict N A.preReturn.2 := by
    simp [restrictedTonguesAt, tonguesAt, hreach]
  have hpre : VectorCount.restrict N A.preReturn.2 ∈ history := by
    rw [← hvectorK]
    exact List.mem_map.mpr ⟨K, List.mem_range.mpr (by omega), rfl⟩
  refine ⟨[VectorCount.restrict N A.activatedState], by simp, ?_⟩
  intro j hj
  by_cases hbefore : j ≤ K
  · apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨j, List.mem_range.mpr (by omega), rfl⟩
  · have hlower : K ≤ j := by omega
    rcases completed_retrace_at_vector_mem_history_or_contact
        A.runway_trace (A.runway_grooved hpaths) A.entryEdge
        A.return_arrive_mouth hreach N history hpre hlower
        (htimes j hj) with hhistorical | hactivated
    · exact List.mem_append_left _ hhistorical
    · apply List.mem_append_right history
      simp [hactivated]

/-- Quantitative first-reflector corollary.  A prefix of length at most `N`
followed by its complete manufactured activation exposes at most `N+2`
pairwise-distinct restricted tongue vectors. -/
theorem ManufacturedReflector.prefix_and_activation_distinct_le_N_add_two
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    {start : Nat × Tongues} {K N : Nat}
    (hreach : stepN w K start = some A.preReturn)
    (hK : K ≤ N)
    (times : List Nat)
    (htimes : ∀ j ∈ times, j ≤ K + A.runway.length + 1)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 2 := by
  have hcover := A.prefix_and_activation_one_novelty_cover
    hpaths hreach N times htimes
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simp only [List.length_map, List.length_range] at hcount
  omega

/-- Geometric form used by the global construction.  Switch simplicity of
the retained exploration supplies `K ≤ N` automatically from the raw wiring
bound. -/
theorem ManufacturedReflector.manufacturing_journey_distinct_le_N_add_two
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (htimes : ∀ j ∈ times,
      j ≤ A.exploration.length + A.runway.length + 1)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, A.baseState))).Nodup) :
    times.length ≤ N + 2 := by
  have hlength : A.exploration.length ≤ N :=
    A.exploration_trace.simple_length_le hN A.exploration_simple
  exact A.prefix_and_activation_distinct_le_N_add_two
    hpaths A.exploration_trace.sound hlength times htimes hnd

/-- Literal distinct-vector form of `activation_one_novelty_cover`: sampled
vectors absent from the supplied history number at most one. -/
theorem ManufacturedReflector.activation_novel_vectors_le_one
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    (N : Nat) (history : List (List Bool))
    (hpre : VectorCount.restrict N A.preReturn.2 ∈ history)
    (times : List Nat)
    (htimes : ∀ d ∈ times, d ≤ A.runway.length + 1)
    (hnovel : ∀ d ∈ times,
      restrictedTonguesAt w N A.preReturn d ∉ history)
    (hnd : (times.map
      (restrictedTonguesAt w N A.preReturn)).Nodup) :
    times.length ≤ 1 := by
  exact completed_retrace_novel_vectors_le_one
    A.runway_trace
    (A.runway_grooved hpaths)
    A.entryEdge
    A.return_arrive_mouth
    N history hpre times htimes hnovel hnd

end GeneralN
