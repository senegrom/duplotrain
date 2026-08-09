import TrackFiniteAlternation

/-!
# A retrace turned by a first writer costs no extra vector

The completed-retrace theorem normally reserves one exceptional vector: the
contact state laid down at the turning switch.  If that contact is itself a
globally first productive write, its post-vector is already one of the
canonical `rawFirstWriterHistory` vectors.  Therefore every *positive* depth
of the complete reverse is historical and the retrace has novelty budget
zero.

This is the coefficient-one accounting lemma needed by the serial escape
argument.  It is a raw general-`N` theorem and assumes no tail certificate.
-/

namespace GeneralN

/-- At every positive depth of a completed retrace, the represented vector
is exactly the contact vector. -/
theorem completed_retrace_at_positive_vector_eq_contact
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    {start : Nat × Tongues} {K j N : Nat}
    (hreach : stepN w K start = some (p, u))
    (hlower : K < j)
    (hupper : j ≤ K + recorded.length + 1) :
    restrictedTonguesAt w N start j =
      VectorCount.restrict N v := by
  let d := j - K
  have hdPositive : 0 < d := by
    dsimp [d]
    omega
  have hd : d ≤ recorded.length + 1 := by
    dsimp [d]
    omega
  have hj : K + d = j := by
    dsimp [d]
    omega
  obtain ⟨port, hlocal⟩ :=
    (physicalTrace_contact_retraces_prefix_pointwise
      hrecorded hgrooved hentry hcontact).2 d hd
  have hglobal : stepN w j start = some (port, v) := by
    rw [← hj, stepN_add, hreach]
    simpa [Nat.ne_of_gt hdPositive] using hlocal
  simp [restrictedTonguesAt, tonguesAt, hglobal]

/-- The contact vector of a completed retrace belongs to the canonical
first-writer history whenever the turning step is a first productive write. -/
theorem first_writer_retrace_contact_mem_history
    {w : Wiring} {N horizon K g e p oldEntry : Nat}
    {start : Nat × Tongues}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (hreach : stepN w K start = some (p, u))
    (hfirst : RawFirstWriterAt w N start K)
    (hK : K < horizon) :
    VectorCount.restrict N v ∈
      rawFirstWriterHistory w N start horizon := by
  have hpost :
      restrictedTonguesAt w N start (K + 1) =
        VectorCount.restrict N v :=
    completed_retrace_at_positive_vector_eq_contact
      hrecorded hgrooved hentry hcontact hreach
        (N := N) (j := K + 1) (by omega) (by omega)
  apply List.mem_cons_of_mem
  apply List.mem_map.mpr
  refine ⟨K, ?_, hpost⟩
  exact mem_rawFirstWriterTimes_iff.mpr ⟨hK, hfirst⟩

/-- **First-writer retrace = zero exceptional vectors.**

For any selected positive times inside the completed reverse, every vector
already lies in `rawFirstWriterHistory`; the novelty cover therefore has an
empty exceptional list. -/
theorem first_writer_completed_retrace_zero_novelty_cover
    {w : Wiring} {N horizon K g e p oldEntry : Nat}
    {start : Nat × Tongues}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (hreach : stepN w K start = some (p, u))
    (hfirst : RawFirstWriterAt w N start K)
    (hK : K < horizon)
    (times : List Nat)
    (htimes : ∀ j, j ∈ times →
      K < j ∧ j ≤ K + recorded.length + 1) :
    NoveltyCoverOn w N start times
      (rawFirstWriterHistory w N start horizon) 0 := by
  have hv := first_writer_retrace_contact_mem_history
    hrecorded hgrooved hentry hcontact hreach hfirst hK
  refine ⟨[], by simp, ?_⟩
  intro j hj
  simp only [List.append_nil]
  rw [completed_retrace_at_positive_vector_eq_contact
    hrecorded hgrooved hentry hcontact hreach
      (htimes j hj).1 (htimes j hj).2]
  exact hv

end GeneralN
