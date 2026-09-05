/-!
# The lazy-point model

Ports are naturals: switch `k` owns stem `3k`, left branch `3k+1`, right
branch `3k+2`.  A `Wiring` is a symmetric partial pairing of ports (the
plain-track edges; geometry never enters).  `Tongues` are `Nat → Bool`
(`false` = left).  A configuration is the port the train is about to enter
plus the tongues.  `arrive` performs the lazy-point rule — facing (enter a
stem) exits by the tongue's branch and moves no tongue, trailing (enter a
branch) pins that tongue and exits the stem — and `step` follows the exit
port's edge (`none` = capped or unwired: the run ends).  `stepN` iterates,
`flipAt` flips one tongue, and `IsReflector` names a track section that
returns the train to a fixed exit with a predictable tongue effect.
Everything downstream is proved for an arbitrary number of switches and an
arbitrary wiring.
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
    branchPort (p / 3) (bval p) = p := by grind [branchPort, bval]

/-! ## Tongue algebra -/

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

/-- A track section that returns every admissible tongue state `S` to exit
`e` after `k` steps from entry `g`, acting on the tongues as `τ`. -/
def IsReflector (w : Wiring) (g e k : Nat)
    (S : Tongues → Prop) (τ : Tongues → Tongues) : Prop :=
  ∀ u, S u → stepN w k (g, u) = some (e, τ u) ∧ S (τ u)
end GeneralN
