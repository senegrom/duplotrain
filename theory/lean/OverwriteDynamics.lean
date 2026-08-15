import GeneralN

/-!
# Idempotence of cascade overwrite words

A trailing cascade performs a fixed finite sequence of tongue assignments.
For one switch, only the last assignment in the word matters.  Consequently
applying the same finite assignment word twice has exactly the same result as
applying it once.

This is the concrete-state mechanism missing from a naïve one-register-per-
tree encoding.  A repeated echo-machine period need not reproduce all latent
off-path tongue bits on its first traversal, but after that traversal every
switch touched by the period already holds the period's final assignment.
The second traversal therefore ends in the same full tongue vector.
-/

namespace GeneralN

/-- Apply branch-pin assignments from left to right. -/
def pinList : List Nat → Tongues → Tongues
  | [], t => t
  | p :: ps, t => pinList ps (pin t p)


theorem descent_result_eq_pinList
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    t' = pinList (p :: ps) t := by
  induction h with
  | last hp hlink hs => rfl
  | cons hp hlink hp' hrest ih =>
      simp only [pinList]
      exact ih

end GeneralN
