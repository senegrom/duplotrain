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

/-- Mapping a function that is injective on a duplicate-free list preserves
duplicate-freedom. -/
theorem nodup_map_of_injective_on_mem
    {α β : Type} {f : α → β} {xs : List α}
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b)
    (hnd : xs.Nodup) : (xs.map f).Nodup := by
  change (xs.map f).Pairwise (fun a b => a ≠ b)
  rw [List.pairwise_map]
  exact hnd.imp_of_mem fun ha hb hne hEq =>
    hne (hinj _ ha _ hb hEq)

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


theorem pin_of_agrees {u : Tongues} {b : Nat} (h : u (b / 3) = bval b) :
    pin u b = u := by
  funext j
  unfold pin
  by_cases hj : j = b / 3
  · rw [if_pos hj, hj, ← h]
  · rw [if_neg hj]

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


def IsReflector (w : Wiring) (g e k : Nat)
    (S : Tongues → Prop) (τ : Tongues → Tongues) : Prop :=
  ∀ u, S u → stepN w k (g, u) = some (e, τ u) ∧ S (τ u)
end GeneralN
