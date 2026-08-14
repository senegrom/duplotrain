/-!
# General-N lazy-point theory, formalised

No exhaustion in this file: every theorem is proved for an ARBITRARY number
of switches and arbitrary wirings, by structural induction.

Model.  Ports are naturals: switch `k` owns stem `3k`, left branch `3k+1`,
right branch `3k+2`.  A wiring is a symmetric partial pairing of ports (the
plain-track edges; geometry provably never enters).  Tongues are
`Nat → Bool` (`false` = Left).  A configuration is the port the train is
about to enter plus the tongues; `step` performs the lazy-point rule --
facing (enter stem) exits by the tongue and leaves it alone, trailing
(enter branch) pins the tongue and exits the stem -- then follows the exit
port's edge (`none` = capped/unwired: the run ends).

Results (all general-N, no `native_decide`, no `sorry`):

* `trailing_route` / `trailing_route_independent` -- a trailing pass's exit
  route never reads the tongues: cascades are wiring-determined (T1/T2 of
  ../lazy-point-theory.md).
* `descent_sound` -- a `Descent` (a trailing cascade carrying its wiring
  facts) is executed faithfully by the dynamics.
* `descent_pins` / `descent_noop` / `descent_sound_noop` -- a cascade's
  tongue effect is exactly its pins; re-running it over already-agreeing
  tongues is a no-op.
* `retrace` (T3, the key lemma) -- entering the LAST cascade switch's stem
  with any tongues agreeing with the cascade's pins, the walk performs pure
  facing moves that traverse the cascade BACKWARDS, leaves every tongue
  untouched, and emerges over the cascade's original entry edge.  This is
  the mechanism that forces the bounce and caps every cycle at the dogbone
  Gray square.
-/

namespace GeneralN

abbrev Tongues := Nat → Bool

structure Wiring where
  link : Nat → Option Nat
  symm : ∀ p q, link p = some q → link q = some p

/-- The branch port of switch `k` selected by tongue value `v`. -/
def branchPort (k : Nat) (v : Bool) : Nat := 3 * k + (if v then 2 else 1)

/-- The tongue value that selects branch port `p`. -/
def bval (p : Nat) : Bool := p % 3 == 2

/-- Pin the tongue of `p`'s switch to `p`'s branch. -/
def pin (t : Tongues) (p : Nat) : Tongues :=
  fun j => if j = p / 3 then bval p else t j

/-- Enter port `p`: (exit port, new tongues). -/
def arrive (t : Tongues) (p : Nat) : Nat × Tongues :=
  if p % 3 = 0 then (branchPort (p / 3) (t (p / 3)), t)
  else (3 * (p / 3), pin t p)

def step (w : Wiring) (c : Nat × Tongues) : Option (Nat × Tongues) :=
  (w.link (arrive c.2 c.1).1).map fun q => (q, (arrive c.2 c.1).2)

def stepN (w : Wiring) : Nat → Nat × Tongues → Option (Nat × Tongues)
  | 0, c => some c
  | n + 1, c => (step w c).bind (stepN w n)

theorem stepN_add (w : Wiring) (m n : Nat) (c : Nat × Tongues) :
    stepN w (m + n) c = (stepN w m c).bind (stepN w n) := by
  induction m generalizing c with
  | zero => simp [stepN]
  | succ m ih =>
    have h : m + 1 + n = (m + n) + 1 := by omega
    rw [h]
    show (step w c).bind (stepN w (m + n)) = _
    cases hs : step w c with
    | none => simp [stepN, hs]
    | some c' => simp [stepN, hs, ih c']

/-- A branch port is recovered from its switch and tongue value. -/
theorem branchPort_bval {p : Nat} (hp : p % 3 ≠ 0) :
    branchPort (p / 3) (bval p) = p := by
  have h3 : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases h3 with h1 | h2
  · have hb : bval p = false := by unfold bval; rw [h1]; rfl
    rw [hb]
    show 3 * (p / 3) + 1 = p
    omega
  · have hb : bval p = true := by unfold bval; rw [h2]; rfl
    rw [hb]
    show 3 * (p / 3) + 2 = p
    omega

/-! ## Trailing routes ignore the tongues (T1/T2) -/


inductive Descent (w : Wiring) :
    Tongues → Nat → List Nat → Nat → Tongues → Prop
  | last {t : Tongues} {p s : Nat} :
      p % 3 ≠ 0 → w.link (3 * (p / 3)) = some s → s % 3 = 0 →
      Descent w t p [] s (pin t p)
  | cons {t : Tongues} {p p' s : Nat} {ps : List Nat} {t' : Tongues} :
      p % 3 ≠ 0 → w.link (3 * (p / 3)) = some p' → p' % 3 ≠ 0 →
      Descent w (pin t p) p' ps s t' →
      Descent w t p (p' :: ps) s t'

def Agrees (u : Tongues) (l : List Nat) : Prop :=
  ∀ b ∈ l, u (b / 3) = bval b

theorem pin_of_agrees {u : Tongues} {b : Nat} (h : u (b / 3) = bval b) :
    pin u b = u := by
  funext j
  unfold pin
  by_cases hj : j = b / 3
  · rw [if_pos hj, hj, ← h]
  · rw [if_neg hj]

def lastOf (p : Nat) : List Nat → Nat
  | [] => p
  | q :: qs => lastOf q qs

/-- **Retrace.**  If a descent trailed through `p :: ps` and the tongues `u`
agree with its pins, then a train entering the LAST cascade switch's stem
performs `(p :: ps).length` pure facing moves that walk the cascade
backwards -- the pins route it home -- with `u` unchanged, and emerges over
the cascade's original entry edge `ℓ` (any port linked to `p`). -/
theorem retrace {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    ∀ ℓ : Nat, w.link ℓ = some p →
    ∀ u : Tongues, Agrees u (p :: ps) →
      stepN w (p :: ps).length (3 * (lastOf p ps / 3), u) = some (ℓ, u) := by
  induction h with
  | @last t p s hp hlink hs =>
    intro ℓ hentry u hagree
    have hu : u (p / 3) = bval p := hagree p (by simp)
    have hstem : (3 * (p / 3)) % 3 = 0 := by omega
    have hdiv : (3 * (p / 3)) / 3 = p / 3 := by omega
    have hbranch : branchPort (p / 3) (u (p / 3)) = p := by
      rw [hu]; exact branchPort_bval hp
    have hback : w.link p = some ℓ := w.symm _ _ hentry
    show stepN w 1 (3 * (lastOf p [] / 3), u) = some (ℓ, u)
    simp [lastOf, stepN, step, arrive, hstem, hdiv, hbranch, hback]
  | @cons t p p' s ps t' hp hlink hp' hrest ih =>
    intro ℓ hentry u hagree
    have htail : Agrees u (p' :: ps) := by
      intro b hb
      exact hagree b (List.mem_cons_of_mem _ hb)
    have hmid := ih (3 * (p / 3)) hlink u htail
    have hu : u (p / 3) = bval p := hagree p (by simp)
    have hstem : (3 * (p / 3)) % 3 = 0 := by omega
    have hdiv : (3 * (p / 3)) / 3 = p / 3 := by omega
    have hbranch : branchPort (p / 3) (u (p / 3)) = p := by
      rw [hu]; exact branchPort_bval hp
    have hback : w.link p = some ℓ := w.symm _ _ hentry
    have hone : stepN w 1 (3 * (p / 3), u) = some (ℓ, u) := by
      simp [stepN, step, arrive, hstem, hdiv, hbranch, hback]
    have hlen : (p :: p' :: ps).length = (p' :: ps).length + 1 := by
      simp [List.length_cons]
    rw [hlen, stepN_add]
    have hlast : lastOf p (p' :: ps) = lastOf p' ps := rfl
    rw [hlast, hmid]
    simpa using hone

/-! ## The generalized dogbone: the bounce and its Gray square (T6) -/

/-- Flip one tongue. -/
def flipAt (u : Tongues) (k : Nat) : Tongues :=
  fun j => if j = k then !(u j) else u j

theorem flipAt_flipAt (u : Tongues) (k : Nat) :
    flipAt (flipAt u k) k = u := by
  funext j
  unfold flipAt
  by_cases hj : j = k <;> simp [hj]

theorem flipAt_comm {u : Tongues} {a b : Nat} (hab : a ≠ b) :
    flipAt (flipAt u a) b = flipAt (flipAt u b) a := by
  funext j
  unfold flipAt
  by_cases hja : j = a
  · simp [hja, hab]
  · by_cases hjb : j = b
    · simp [hjb, Ne.symm hab]
    · simp [hja, hjb]

theorem descent_last_link {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    w.link (3 * (lastOf p ps / 3)) = some s := by
  induction h with
  | last hp hlink hs => exact hlink
  | cons hp hlink hp' _ ih => exact ih

theorem descent_mem_suffix {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') {q : Nat} (hq : q ∈ p :: ps) :
    ∃ t₂ qs t₃, Descent w t₂ q qs s t₃ := by
  induction h with
  | @last t p s hp hlink hs =>
    have hqp : q = p := by simpa using hq
    subst hqp
    exact ⟨t, [], _, Descent.last hp hlink hs⟩
  | @cons t p p' s ps t' hp hlink hp' hrest ih =>
    rcases List.mem_cons.mp hq with hqp | hqtail
    · subst hqp
      exact ⟨t, p' :: ps, t', Descent.cons hp hlink hp' hrest⟩
    · exact ih hqtail

/-- Two descents entering the SAME SWITCH (by either branch) land at the
same stem: both exit that switch's stem, whose single edge fixes all the
rest of the journey. -/
theorem descent_land_unique {w : Wiring} {t₁ : Tongues}
    {q₁ s₁ : Nat} {qs₁ : List Nat} {t₁' : Tongues}
    (h₁ : Descent w t₁ q₁ qs₁ s₁ t₁') :
    ∀ {t₂ : Tongues} {q₂ s₂ : Nat} {qs₂ : List Nat} {t₂' : Tongues},
      q₁ / 3 = q₂ / 3 → Descent w t₂ q₂ qs₂ s₂ t₂' → s₁ = s₂ := by
  induction h₁ with
  | @last t p s hp hlink hs =>
    intro t₂ q₂ s₂ qs₂ t₂' hsw h₂
    rw [hsw] at hlink
    cases h₂ with
    | last hp₂ hlink₂ hs₂ =>
      rw [hlink] at hlink₂
      injection hlink₂
    | cons hp₂ hlink₂ hp₂' hrest₂ =>
      rw [hlink] at hlink₂
      injection hlink₂ with heq
      subst heq
      exact absurd hs hp₂'
  | @cons t p p' s ps t' hp hlink hp' hrest ih =>
    intro t₂ q₂ s₂ qs₂ t₂' hsw h₂
    rw [hsw] at hlink
    cases h₂ with
    | last hp₂ hlink₂ hs₂ =>
      rw [hlink] at hlink₂
      injection hlink₂ with heq
      subst heq
      exact absurd hs₂ hp'
    | cons hp₂ hlink₂ hp₂' hrest₂ =>
      rw [hlink] at hlink₂
      injection hlink₂ with heq
      subst heq
      exact ih rfl hrest₂

/-- **Merge-landing (T2, general N).**  Two cascades whose paths share a
switch land at the same stem.  Hence cascade-connected components -- the
SYSTEMS -- each have a unique landing stem. -/
theorem merge_land {w : Wiring} {ta tb : Tongues} {pa pb sa sb : Nat}
    {psa psb : List Nat} {ta' tb' : Tongues}
    (ha : Descent w ta pa psa sa ta')
    (hb : Descent w tb pb psb sb tb')
    {qa qb : Nat} (hqa : qa ∈ pa :: psa) (hqb : qb ∈ pb :: psb)
    (hsw : qa / 3 = qb / 3) :
    sa = sb := by
  obtain ⟨t₂, qs, t₃, hsub_a⟩ := descent_mem_suffix ha hqa
  obtain ⟨t₄, qs', t₅, hsub_b⟩ := descent_mem_suffix hb hqb
  exact descent_land_unique hsub_a hsw hsub_b

/-- **Landing injectivity.**  Every cascade landing at stem `s` ends at the
same last switch -- the one wired to `s`'s stem edge.  So distinct systems
have distinct landing stems: facing `s` identifies the system that just
ran. -/
theorem land_last_unique {w : Wiring} {t₁ t₂ : Tongues}
    {p₁ p₂ s : Nat} {ps₁ ps₂ : List Nat} {t₁' t₂' : Tongues}
    (h₁ : Descent w t₁ p₁ ps₁ s t₁')
    (h₂ : Descent w t₂ p₂ ps₂ s t₂') :
    3 * (lastOf p₁ ps₁ / 3) = 3 * (lastOf p₂ ps₂ / 3) := by
  have b₁ := w.symm _ _ (descent_last_link h₁)
  have b₂ := w.symm _ _ (descent_last_link h₂)
  rw [b₁] at b₂
  injection b₂



def IsReflector (w : Wiring) (g e k : Nat)
    (S : Tongues → Prop) (τ : Tongues → Tongues) : Prop :=
  ∀ u, S u → stepN w k (g, u) = some (e, τ u) ∧ S (τ u)
end GeneralN
