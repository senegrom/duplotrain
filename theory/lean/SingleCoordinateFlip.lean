import RepairLeadTwoPhase

/-! Boolean functions differing only at one coordinate are equal or one flip apart. -/

namespace GeneralN

/-- If every coordinate where `v` differs from `u` is `k`, then `u` is
exactly `v` or `v` with coordinate `k` flipped. -/
theorem tongues_eq_or_eq_flipAt_of_changes_only
    {u v : Tongues} {k : Nat}
    (hchanges : ∀ j, v j ≠ u j → j = k) :
    u = v ∨ u = flipAt v k := by
  by_cases hkey : u k = v k
  · left
    funext j
    by_cases hj : j = k
    · subst j
      exact hkey
    · by_contra hneq
      have hvune : v j ≠ u j := by
        intro heq
        exact hneq heq.symm
      exact hj (hchanges j hvune)
  · right
    funext j
    by_cases hj : j = k
    · subst j
      cases hu : u k <;> cases hv : v k <;>
        simp_all [flipAt]
    · have huv : u j = v j := by
        by_contra hneq
        have hvune : v j ≠ u j := by
          intro heq
          exact hneq heq.symm
        exact hj (hchanges j hvune)
      simp [flipAt, hj, huv]

end GeneralN
