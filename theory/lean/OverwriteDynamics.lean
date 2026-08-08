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

/-- The Boolean written by a trailing arrival at branch port `p`. -/
def pinValue (p : Nat) : Bool := decide (p % 3 = 2)

/-- The final assignment made to switch `k` by a pin word, if any. -/
def finalPinValue : List Nat → Nat → Option Bool
  | [], _ => none
  | p :: ps, k =>
      match finalPinValue ps k with
      | some b => some b
      | none => if p / 3 = k then some (pinValue p) else none

/-- Evaluation of a pin word is completely described by its last assignment
to each switch. -/
theorem pinList_apply : ∀ ps t k,
    pinList ps t k = (finalPinValue ps k).getD (t k) := by
  intro ps
  induction ps with
  | nil =>
      intro t k
      rfl
  | cons p ps ih =>
      intro t k
      unfold pinList finalPinValue
      rw [ih]
      cases hlast : finalPinValue ps k with
      | some b => simp [hlast]
      | none =>
          by_cases hpk : p / 3 = k
          · simp [hlast, hpk, pin, pinValue]
          · simp [hlast, hpk, pin, pinValue]

/-- Repeating a fixed cascade-assignment word is idempotent. -/
theorem pinList_idempotent (ps : List Nat) (t : Tongues) :
    pinList ps (pinList ps t) = pinList ps t := by
  funext k
  rw [pinList_apply, pinList_apply, pinList_apply]
  cases hlast : finalPinValue ps k <;> simp [hlast]

/-- Concatenating pin words is sequential composition. -/
theorem pinList_append (xs ys : List Nat) (t : Tongues) :
    pinList (xs ++ ys) t = pinList ys (pinList xs t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.cons_append, pinList]
      exact ih (pin t x)

/-- Execute a finite list of cascade words. -/
def runPinWords (words : List (List Nat)) (t : Tongues) : Tongues :=
  pinList words.flatten t

/-- Repeating an entire finite block of cascades is idempotent. -/
theorem runPinWords_idempotent
    (words : List (List Nat)) (t : Tongues) :
    runPinWords words (runPinWords words t) = runPinWords words t := by
  exact pinList_idempotent words.flatten t

/-- Splitting a list of cascade words is sequential composition. -/
theorem runPinWords_append
    (xs ys : List (List Nat)) (t : Tongues) :
    runPinWords (xs ++ ys) t = runPinWords ys (runPinWords xs t) := by
  unfold runPinWords
  rw [List.flatten_append, pinList_append]

/-- A concrete descent writes exactly its recorded branch word. -/
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

/-- Re-running the same recorded descent after it has just run changes no
full tongue vector, now as a direct corollary of overwrite idempotence. -/
theorem descent_pinList_noop
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    pinList (p :: ps) t' = t' := by
  rw [descent_result_eq_pinList h]
  exact pinList_idempotent (p :: ps) t

end GeneralN
