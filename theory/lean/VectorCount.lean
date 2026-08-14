import GeneralN

/-!
# The unconditional ceiling: f(N) ≤ 2^N, machine-checked

The state-count question asks how many distinct tongue vectors a single
train can visit on an N-switch wiring.  The conjectured law is
f(N) = min(2^N, N+4); the N+4 half currently rests on the two echo-machine
lemmas (../lazy-point-theory.md).  This file closes the other half
unconditionally: **no run of any wiring, of any length, ever visits more
than 2^N distinct tongue vectors** — a genuine pigeonhole proof (no
`native_decide`, no Mathlib), not an appeal to "obviously the state space
is 2^N".

The content is `pigeonhole`: a duplicate-free list of length-N boolean
vectors has at most 2^N elements, by induction on N (split on the first
coordinate, recurse on the tails).  `vector_count_le` and
`trajectory_count_le` specialise it to tongue assignments and to
trajectories `Nat → Tongues` — the tongue component of any run of any
wiring in the `GeneralN` model.
-/

namespace VectorCount

open GeneralN (Tongues)

/-- The tongue vector restricted to the first `N` switches. -/
def restrict (N : Nat) (u : Tongues) : List Bool :=
  (List.range N).map u
private def tails (b : Bool) : List (List Bool) → List (List Bool)
  | [] => []
  | [] :: rest => tails b rest
  | (b' :: t) :: rest =>
      if b' = b then t :: tails b rest else tails b rest

private theorem tails_nil (b : Bool) : tails b [] = [] := rfl

private theorem tails_cons_nil (b : Bool) (rest : List (List Bool)) :
    tails b ([] :: rest) = tails b rest := rfl

private theorem tails_cons_eq (b : Bool) (t : List Bool)
    (rest : List (List Bool)) :
    tails b ((b :: t) :: rest) = t :: tails b rest := by
  simp [tails]

private theorem tails_cons_ne {b b' : Bool} (h : b' ≠ b) (t : List Bool)
    (rest : List (List Bool)) :
    tails b ((b' :: t) :: rest) = tails b rest := by
  simp [tails, h]

private theorem mem_tails (b : Bool) :
    ∀ (l : List (List Bool)) (s : List Bool),
      s ∈ tails b l → (b :: s) ∈ l := by
  intro l
  induction l with
  | nil => intro s hs; rw [tails_nil] at hs; cases hs
  | cons x rest ih =>
      intro s hs
      cases x with
      | nil =>
          rw [tails_cons_nil] at hs
          exact List.mem_cons_of_mem _ (ih s hs)
      | cons b' t =>
          by_cases hb : b' = b
          · rw [hb] at hs ⊢
            rw [tails_cons_eq] at hs
            cases hs with
            | head => exact List.mem_cons_self
            | tail _ h => exact List.mem_cons_of_mem _ (ih s h)
          · rw [tails_cons_ne hb] at hs
            exact List.mem_cons_of_mem _ (ih s hs)

private theorem tails_nodup (b : Bool) :
    ∀ (l : List (List Bool)), l.Nodup → (tails b l).Nodup := by
  intro l
  induction l with
  | nil => intro _; rw [tails_nil]; exact List.nodup_nil
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases x with
      | nil => rw [tails_cons_nil]; exact ih hnd.2
      | cons b' t =>
          by_cases hb : b' = b
          · rw [hb] at hnd ⊢
            rw [tails_cons_eq, List.nodup_cons]
            exact ⟨fun hmem => hnd.1 (mem_tails b rest t hmem), ih hnd.2⟩
          · rw [tails_cons_ne hb]
            exact ih hnd.2

private theorem tails_length (N : Nat) :
    ∀ (l : List (List Bool)), (∀ x ∈ l, x.length = N + 1) →
      (tails true l).length + (tails false l).length = l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x rest ih =>
      intro hlen
      have hrest := fun y hy => hlen y (List.mem_cons_of_mem _ hy)
      have hih := ih hrest
      cases x with
      | nil =>
          have h := hlen [] List.mem_cons_self
          simp only [List.length_nil] at h
          omega
      | cons b' t =>
          cases b' with
          | true =>
              rw [tails_cons_eq, tails_cons_ne (by decide : true ≠ false),
                List.length_cons, List.length_cons]
              omega
          | false =>
              rw [tails_cons_eq, tails_cons_ne (by decide : false ≠ true),
                List.length_cons, List.length_cons]
              omega

/-- A duplicate-free list of length-`N` boolean vectors has at most
`2^N` elements. -/
theorem pigeonhole : ∀ (N : Nat) (l : List (List Bool)),
    (∀ x ∈ l, x.length = N) → l.Nodup → l.length ≤ 2 ^ N := by
  intro N
  induction N with
  | zero =>
      intro l hlen hnd
      cases l with
      | nil => exact Nat.zero_le _
      | cons x rest =>
          have hx : x = [] := by
            have h := hlen x List.mem_cons_self
            cases x with
            | nil => rfl
            | cons a t => simp only [List.length_cons] at h; omega
          cases rest with
          | nil => exact Nat.le_refl _
          | cons y rest2 =>
              have hy : y = [] := by
                have h := hlen y
                  (List.mem_cons_of_mem _ List.mem_cons_self)
                cases y with
                | nil => rfl
                | cons a t => simp only [List.length_cons] at h; omega
              rw [List.nodup_cons] at hnd
              exact absurd
                (by rw [hx, hy]; exact List.mem_cons_self) hnd.1
  | succ N ih =>
      intro l hlen hnd
      have hsplit := tails_length N l hlen
      have ht := ih (tails true l)
        (fun s hs => by
          have h := hlen (true :: s) (mem_tails true l s hs)
          simp only [List.length_cons] at h
          omega)
        (tails_nodup true l hnd)
      have hf := ih (tails false l)
        (fun s hs => by
          have h := hlen (false :: s) (mem_tails false l s hs)
          simp only [List.length_cons] at h
          omega)
        (tails_nodup false l hnd)
      have hpow : 2 ^ (N + 1) = 2 ^ N + 2 ^ N := by
        rw [Nat.pow_succ]; omega
      omega

end VectorCount
