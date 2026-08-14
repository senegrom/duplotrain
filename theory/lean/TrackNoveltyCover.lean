import StateLaw
import TrackNovelReplay

/-!
# Novelty covers for completed physical retraces

`TrackNovelReplay` proves the pointwise fact behind novelty accounting: once
a train contacts the exit of an old grooved physical trace, every positive
time on the completed reverse traversal carries the one contact tongue
vector.

This file packages that fact as an exact cover and as a counting theorem.
The semantic premise `PassagesGrooved v recorded` is essential.  Mere switch
simplicity of the old trace does not imply that an arbitrary contact vector
still grooves it, so no theorem below hides that premise.

The global coefficient-one state law remains open.  What is closed here is
the local step needed by a global four-novelty argument: a completed retrace
whose initial vector is already historical contributes at most one genuinely
new restricted tongue vector, regardless of the length of the retraced path.
-/

namespace GeneralN

/-- The first `N` tongue bits at time `k` of a run. -/
def restrictedTonguesAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : List Bool :=
  VectorCount.restrict N (tonguesAt w start k)

/-- On the selected times, every restricted tongue vector is either already
in `history` or belongs to a list of at most `budget` exceptional vectors. -/
def NoveltyCoverOn (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (times : List Nat) (history : List (List Bool)) (budget : Nat) : Prop :=
  ∃ fresh : List (List Bool),
    fresh.length ≤ budget ∧
    ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈ history ++ fresh

/-- The cover shape needed by the conjectured sharp tail argument: all
selected vectors are historical except for at most four candidates. -/
def FourNoveltyCover (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (times : List Nat) (history : List (List Bool)) : Prop :=
  NoveltyCoverOn w N start times history 4

private theorem nodup_subset_length_novelty
    {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs cover : List α},
      xs.Nodup →
      (∀ x ∈ xs, x ∈ cover) →
      xs.length ≤ cover.length := by
  intro xs
  induction xs with
  | nil =>
      intro cover _ _
      exact Nat.zero_le _
  | cons x rest ih =>
      intro cover hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ cover := hsub x List.mem_cons_self
      have hrest : ∀ y ∈ rest, y ∈ cover.erase x := by
        intro y hy
        have hyCover : y ∈ cover :=
          hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun heq => hnd.1 (heq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyCover
      have hle := ih hnd.2 hrest
      have herase : (cover.erase x).length = cover.length - 1 :=
        List.length_erase_of_mem hx
      have hpositive : 0 < cover.length := by
        cases cover with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- A novelty cover converts directly into a count of distinct sampled
vectors.  This is the generic final bookkeeping step of a novelty proof. -/
theorem noveltyCoverOn_distinct_count
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times : List Nat} {history : List (List Bool)} {budget : Nat}
    (hcover : NoveltyCoverOn w N start times history budget)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ history.length + budget := by
  obtain ⟨fresh, hfreshLength, hmem⟩ := hcover
  have hsubset :
      ∀ x ∈ times.map (restrictedTonguesAt w N start),
        x ∈ history ++ fresh := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact hmem k hk
  have hbound := nodup_subset_length_novelty hnd hsubset
  simp only [List.length_map, List.length_append] at hbound
  omega

/-- Novelty covers compose by concatenating both the sampled times and their
exception lists.  Thus four one-novelty frame covers yield a four-novelty
cover once the global track argument supplies the four-frame decomposition. -/
theorem noveltyCoverOn_append
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {leftTimes rightTimes : List Nat} {history : List (List Bool)}
    {leftBudget rightBudget : Nat}
    (hleft : NoveltyCoverOn w N start leftTimes history leftBudget)
    (hright : NoveltyCoverOn w N start rightTimes history rightBudget) :
    NoveltyCoverOn w N start (leftTimes ++ rightTimes) history
      (leftBudget + rightBudget) := by
  obtain ⟨leftFresh, hleftLength, hleftMem⟩ := hleft
  obtain ⟨rightFresh, hrightLength, hrightMem⟩ := hright
  refine ⟨leftFresh ++ rightFresh, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · intro k hk
    rcases List.mem_append.mp hk with hkLeft | hkRight
    · rcases List.mem_append.mp (hleftMem k hkLeft) with
        hhistory | hfresh
      · exact List.mem_append_left _ hhistory
      · exact List.mem_append_right history
          (List.mem_append_left _ hfresh)
    · rcases List.mem_append.mp (hrightMem k hkRight) with
        hhistory | hfresh
      · exact List.mem_append_left _ hhistory
      · exact List.mem_append_right history
          (List.mem_append_right leftFresh hfresh)

/-- In particular, a four-novelty cover gives the desired constant-four
count above the supplied history. -/
theorem fourNoveltyCover_distinct_count
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times : List Nat} {history : List (List Bool)}
    (hcover : FourNoveltyCover w N start times history)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ history.length + 4 :=
  noveltyCoverOn_distinct_count hcover hnd

/-- Four independently established one-novelty covers combine into the
four-candidate interface.  The time lists need not be ordered; the theorem is
purely a cover assembly result. -/
theorem four_one_novelty_covers
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times₁ times₂ times₃ times₄ : List Nat}
    {history : List (List Bool)}
    (h₁ : NoveltyCoverOn w N start times₁ history 1)
    (h₂ : NoveltyCoverOn w N start times₂ history 1)
    (h₃ : NoveltyCoverOn w N start times₃ history 1)
    (h₄ : NoveltyCoverOn w N start times₄ history 1) :
    FourNoveltyCover w N start
      (((times₁ ++ times₂) ++ times₃) ++ times₄) history := by
  have h₁₂ := noveltyCoverOn_append h₁ h₂
  have h₁₂₃ := noveltyCoverOn_append h₁₂ h₃
  have h₁₂₃₄ := noveltyCoverOn_append h₁₂₃ h₄
  simpa [FourNoveltyCover] using h₁₂₃₄

/-- Once the structural argument supplies a history of size at most `N+2`
and a four-novelty cover, the requested `N+6` arithmetic is immediate.  The
open global problem is precisely to construct those objects for an arbitrary
raw-track trajectory. -/
theorem fourNoveltyCover_to_N_add_six
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {times : List Nat} {history : List (List Bool)}
    (hhistory : history.length ≤ N + 2)
    (hcover : FourNoveltyCover w N start times history)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  have hcount := fourNoveltyCover_distinct_count hcover hnd
  omega

/-- **Exact completed-retrace tongue law.**  Depth zero has the initial vector
`u`; every positive depth through the final reverse passage has exactly the
contact vector `v`. -/
theorem completed_retrace_tongues_exact
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    {d : Nat} (hd : d ≤ recorded.length + 1) :
    tonguesAt w (p, u) d = if d = 0 then u else v := by
  obtain ⟨port, hstep⟩ :=
    (physicalTrace_contact_retraces_prefix_pointwise
      hrecorded hgrooved hentry hcontact).2 d hd
  simp [tonguesAt, hstep]

/-- Historical-or-contact projection of `completed_retrace_tongues_exact` to
the first `N` switch bits.  This is stronger than the requested switch-simple
form: switch simplicity is not used once the semantically necessary grooving
premise is available. -/
theorem completed_retrace_vector_mem_history_or_contact
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (N : Nat) (history : List (List Bool))
    (hu : VectorCount.restrict N u ∈ history)
    {d : Nat} (hd : d ≤ recorded.length + 1) :
    restrictedTonguesAt w N (p, u) d ∈ history ∨
      restrictedTonguesAt w N (p, u) d =
        VectorCount.restrict N v := by
  obtain ⟨port, hstep⟩ :=
    (physicalTrace_contact_retraces_prefix_pointwise
      hrecorded hgrooved hentry hcontact).2 d hd
  have hvector :
      restrictedTonguesAt w N (p, u) d =
        VectorCount.restrict N (if d = 0 then u else v) := by
    simp [restrictedTonguesAt, tonguesAt, hstep]
  by_cases hzero : d = 0
  · left
    rw [hvector, if_pos hzero]
    exact hu
  · right
    rw [hvector, if_neg hzero]

/-- Absolute-time form of the exact novelty law.  If the original run reaches
the contact configuration at time `K`, every time in the corresponding
completed frame is historical or has exactly the contact vector. -/
theorem completed_retrace_at_vector_mem_history_or_contact
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some (p, u))
    (N : Nat) (history : List (List Bool))
    (hu : VectorCount.restrict N u ∈ history)
    {j : Nat} (hlower : K ≤ j)
    (hupper : j ≤ K + recorded.length + 1) :
    restrictedTonguesAt w N start j ∈ history ∨
      restrictedTonguesAt w N start j =
        VectorCount.restrict N v := by
  let d := j - K
  have hd : d ≤ recorded.length + 1 := by
    dsimp [d]
    omega
  obtain ⟨port, hlocal⟩ :=
    (physicalTrace_contact_retraces_prefix_pointwise
      hrecorded hgrooved hentry hcontact).2 d hd
  have hj : j = K + d := by
    dsimp [d]
    omega
  have hglobal :
      stepN w j start =
        some (port, if d = 0 then u else v) := by
    rw [hj, stepN_add, hreach]
    exact hlocal
  have hvector :
      restrictedTonguesAt w N start j =
        VectorCount.restrict N (if d = 0 then u else v) := by
    simp [restrictedTonguesAt, tonguesAt, hglobal]
  by_cases hzero : d = 0
  · left
    rw [hvector, if_pos hzero]
    exact hu
  · right
    rw [hvector, if_neg hzero]

/-- A completed retrace has a one-novelty cover on any selected collection of
depths contained in the frame. -/
theorem completed_retrace_one_novelty_cover
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (N : Nat) (history : List (List Bool))
    (hu : VectorCount.restrict N u ∈ history)
    (times : List Nat)
    (htimes : ∀ d ∈ times, d ≤ recorded.length + 1) :
    NoveltyCoverOn w N (p, u) times history 1 := by
  refine ⟨[VectorCount.restrict N v], by simp, ?_⟩
  intro d hd
  rcases completed_retrace_vector_mem_history_or_contact
      hrecorded hgrooved hentry hcontact N history hu
      (htimes d hd) with hhistorical | hcontactVector
  · exact List.mem_append_left _ hhistorical
  · apply List.mem_append_right history
    simp [hcontactVector]

/-- Absolute-time one-novelty cover for a completed frame embedded in the
original run. -/
theorem completed_retrace_at_one_novelty_cover
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some (p, u))
    (N : Nat) (history : List (List Bool))
    (hu : VectorCount.restrict N u ∈ history)
    (times : List Nat)
    (htimes : ∀ j ∈ times,
      K ≤ j ∧ j ≤ K + recorded.length + 1) :
    NoveltyCoverOn w N start times history 1 := by
  refine ⟨[VectorCount.restrict N v], by simp, ?_⟩
  intro j hj
  rcases completed_retrace_at_vector_mem_history_or_contact
      hrecorded hgrooved hentry hcontact hreach N history hu
      (htimes j hj).1 (htimes j hj).2 with hhistorical | hcontactVector
  · exact List.mem_append_left _ hhistorical
  · apply List.mem_append_right history
    simp [hcontactVector]

theorem completed_retrace_novel_vectors_le_one
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (N : Nat) (history : List (List Bool))
    (hu : VectorCount.restrict N u ∈ history)
    (times : List Nat)
    (htimes : ∀ d ∈ times, d ≤ recorded.length + 1)
    (hnovel : ∀ d ∈ times,
      restrictedTonguesAt w N (p, u) d ∉ history)
    (hnd : (times.map (restrictedTonguesAt w N (p, u))).Nodup) :
    times.length ≤ 1 := by
  have hsubset :
      ∀ x ∈ times.map (restrictedTonguesAt w N (p, u)),
        x ∈ [VectorCount.restrict N v] := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    rcases completed_retrace_vector_mem_history_or_contact
        hrecorded hgrooved hentry hcontact N history hu
        (htimes d hd) with hhistorical | hcontactVector
    · exact (hnovel d hd hhistorical).elim
    · simp [hcontactVector]
  have hbound := nodup_subset_length_novelty hnd hsubset
  simpa using hbound

end GeneralN
