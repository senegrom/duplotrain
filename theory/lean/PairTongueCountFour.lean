import TrackThetaAllTime

/-!
# Tongue counts from the absolute phase laws

The four-phase capstone (`manufactured_flip_pair_all_time_four_phase`) and
the compatible-orbit law make every flip/flip and every avoiding reflector
pair cost **four** tongue vectors flat.  Only the stay/flip contact
geometries still pay a travel-shaped price (`8*N+1`), so the reflector-pair
count drops from `12*N+3` to `8*N+4`, and the complete-repair branch from
`13*N+3` to `9*N+4`.
-/

namespace GeneralN
theorem manufactured_pair_avoid_distinct_le_four
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, state))).Nodup) :
    times.length ≤ 4 := by
  have hcover : NoveltyCoverOn w N (g, state) times [] 4 := by
    refine ⟨[VectorCount.restrict N state,
      VectorCount.restrict N (A.toSupported.action.apply state),
      VectorCount.restrict N
        (B.toSupported.action.apply (A.toSupported.action.apply state)),
      VectorCount.restrict N
        (A.toSupported.action.apply
          (B.toSupported.action.apply
            (A.toSupported.action.apply state)))],
      by simp, ?_⟩
    intro k hk
    have hmem := manufactured_pair_all_time_four_phase_tongues
      A B state hA hB hAB hBA k
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    unfold restrictedTonguesAt
    rcases hmem with h | h | h | h
    · rw [h]
      simp
    · rw [h]
      simp
    · rw [h]
      simp
    · rw [h]
      simp
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

end GeneralN
