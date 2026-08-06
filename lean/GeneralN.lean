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
  docs/lazy-point-theory.md).
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

/-- The exit route of a trailing pass is a pure wiring fact. -/
theorem trailing_route (w : Wiring) (p : Nat) (t : Tongues)
    (hp : p % 3 ≠ 0) :
    (step w (p, t)).map Prod.fst = w.link (3 * (p / 3)) := by
  cases h : w.link (3 * (p / 3)) <;> simp [step, arrive, hp, h]

/-- Hence it is independent of the tongues. -/
theorem trailing_route_independent (w : Wiring) (p : Nat) (t u : Tongues)
    (hp : p % 3 ≠ 0) :
    (step w (p, t)).map Prod.fst = (step w (p, u)).map Prod.fst := by
  rw [trailing_route w p t hp, trailing_route w p u hp]

/-! ## Descents: trailing cascades carrying their wiring facts -/

inductive Descent (w : Wiring) :
    Tongues → Nat → List Nat → Nat → Tongues → Prop
  | last {t : Tongues} {p s : Nat} :
      p % 3 ≠ 0 → w.link (3 * (p / 3)) = some s → s % 3 = 0 →
      Descent w t p [] s (pin t p)
  | cons {t : Tongues} {p p' s : Nat} {ps : List Nat} {t' : Tongues} :
      p % 3 ≠ 0 → w.link (3 * (p / 3)) = some p' → p' % 3 ≠ 0 →
      Descent w (pin t p) p' ps s t' →
      Descent w t p (p' :: ps) s t'

theorem descent_sound {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    stepN w (ps.length + 1) (p, t) = some (s, t') := by
  induction h with
  | @last t p s hp hlink hs =>
    simp [stepN, step, arrive, hp, hlink]
  | @cons t p p' s ps t' hp hlink hp' _ ih =>
    have hlen : (p' :: ps).length + 1 = 1 + (ps.length + 1) := by
      rw [List.length_cons]; omega
    rw [hlen, stepN_add]
    have h1 : stepN w 1 (p, t) = some (p', pin t p) := by
      simp [stepN, step, arrive, hp, hlink]
    rw [h1]
    simpa using ih

theorem descent_pins {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    t' = (p :: ps).foldl pin t := by
  induction h with
  | last hp hlink hs => rfl
  | cons hp hlink hp' _ ih => simpa using ih

/-- `u` agrees with the pins of every branch in `l`. -/
def Agrees (u : Tongues) (l : List Nat) : Prop :=
  ∀ b ∈ l, u (b / 3) = bval b

theorem pin_of_agrees {u : Tongues} {b : Nat} (h : u (b / 3) = bval b) :
    pin u b = u := by
  funext j
  unfold pin
  by_cases hj : j = b / 3
  · rw [if_pos hj, hj, ← h]
  · rw [if_neg hj]

theorem descent_noop {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') (hagree : Agrees t (p :: ps)) :
    t' = t := by
  induction h with
  | @last t p s hp hlink hs =>
    exact pin_of_agrees (hagree p (by simp))
  | @cons t p p' s ps t' hp hlink hp' hrest ih =>
    have hpin : pin t p = t := pin_of_agrees (hagree p (by simp))
    have htail : Agrees (pin t p) (p' :: ps) := by
      intro b hb
      rw [hpin]
      exact hagree b (List.mem_cons_of_mem _ hb)
    rw [ih htail, hpin]

/-- Re-running a cascade over agreeing tongues moves the train but not the
tongues. -/
theorem descent_sound_noop {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') (hagree : Agrees t (p :: ps)) :
    stepN w (ps.length + 1) (p, t) = some (s, t) := by
  have hs := descent_sound h
  rwa [descent_noop h hagree] at hs

/-! ## The retrace theorem (T3) -/

/-- The last branch of the cascade `p :: ps`. -/
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

/-- Flipping a switch outside a cascade preserves agreement with its pins. -/
theorem agrees_flip {u : Tongues} {l : List Nat} {k : Nat}
    (h : Agrees u l) (hk : ∀ q ∈ l, q / 3 ≠ k) :
    Agrees (flipAt u k) l := by
  intro b hb
  unfold flipAt
  rw [if_neg (hk b hb)]
  exact h b hb

/-- The last link of a descent: the landing stem is wired to the last
cascade switch's stem. -/
theorem descent_last_link {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    w.link (3 * (lastOf p ps / 3)) = some s := by
  induction h with
  | last hp hlink hs => exact hlink
  | cons hp hlink hp' _ ih => exact ih

/-- A descent's route and wiring facts do not depend on the initial tongues:
the same cascade runs from any tongue state. -/
theorem descent_rebase {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') (t₂ : Tongues) :
    ∃ t₃, Descent w t₂ p ps s t₃ := by
  induction h generalizing t₂ with
  | last hp hlink hs => exact ⟨_, Descent.last hp hlink hs⟩
  | cons hp hlink hp' _ ih =>
    obtain ⟨t₃, hd⟩ := ih (pin t₂ _)
    exact ⟨t₃, Descent.cons hp hlink hp' hd⟩

/-- **Lobe hop.**  Facing a lobed switch crosses the lobe, flips the tongue,
and leaves by the stem edge -- two steps, both tongue values alike. -/
theorem lobe_hop (w : Wiring) (a p : Nat) (u : Tongues)
    (hlobe : w.link (3 * a + 1) = some (3 * a + 2))
    (hstem : w.link (3 * a) = some p) :
    stepN w 2 (3 * a, u) = some (p, flipAt u a) := by
  have h0 : (3 * a) % 3 = 0 := by omega
  have hd : (3 * a) / 3 = a := by omega
  have hn1 : (3 * a + 1) % 3 ≠ 0 := by omega
  have hn2 : (3 * a + 2) % 3 ≠ 0 := by omega
  have h1d : (3 * a + 1) / 3 = a := by omega
  have h2d : (3 * a + 2) / 3 = a := by omega
  have hlobe' : w.link (3 * a + 2) = some (3 * a + 1) := w.symm _ _ hlobe
  have h1m : (3 * a + 1) % 3 = 1 := by omega
  have h2m : (3 * a + 2) % 3 = 2 := by omega
  cases hu : u a with
  | false =>
    have hb : branchPort a (u a) = 3 * a + 1 := by rw [hu]; rfl
    have hpin : pin u (3 * a + 2) = flipAt u a := by
      funext j
      unfold pin flipAt bval
      rw [h2d, h2m]
      by_cases hj : j = a
      · rw [if_pos hj, if_pos hj, hj, hu]
        rfl
      · rw [if_neg hj, if_neg hj]
    simp [stepN, step, arrive, h0, hd, hb, hlobe, h2d, hstem, hpin]
  | true =>
    have hb : branchPort a (u a) = 3 * a + 2 := by rw [hu]; rfl
    have hpin : pin u (3 * a + 1) = flipAt u a := by
      funext j
      unfold pin flipAt bval
      rw [h1d, h1m]
      by_cases hj : j = a
      · rw [if_pos hj, if_pos hj, hj, hu]
        rfl
      · rw [if_neg hj, if_neg hj]
    simp [stepN, step, arrive, h0, hd, hb, hlobe', h1d, hstem, hpin]

/-- **The generalized dogbone bounce** (T6, arbitrary N, arbitrary interior
cascade).  Two lobed switches `a` and `b`, `a`'s stem wired into a trailing
cascade `p :: ps` landing on `b`'s stem.  From `a`'s stem with any tongues
agreeing with the cascade's pins and avoiding `a`, `b` inside the cascade:
one half-period of `2·|ps| + 6` steps flips exactly `a` and `b` and returns
the train to `a`'s stem.  The walk is trapped in the bounce forever. -/
theorem dogbone_halfPeriod
    (w : Wiring) (a b p : Nat) (ps : List Nat) (t₀ t₁ : Tongues) (u : Tongues)
    (ha_lobe : w.link (3 * a + 1) = some (3 * a + 2))
    (hb_lobe : w.link (3 * b + 1) = some (3 * b + 2))
    (ha_stem : w.link (3 * a) = some p)
    (hD : Descent w t₀ p ps (3 * b) t₁)
    (hagree : Agrees u (p :: ps))
    (hnota : ∀ q ∈ p :: ps, q / 3 ≠ a)
    (hnotb : ∀ q ∈ p :: ps, q / 3 ≠ b) :
    stepN w (2 * ps.length + 6) (3 * a, u)
      = some (3 * a, flipAt (flipAt u a) b) := by
  -- Phase 1: hop a's lobe (2 steps).
  have hop1 := lobe_hop w a p u ha_lobe ha_stem
  -- Phase 2: ride the cascade, a no-op on tongues (|ps| + 1 steps).
  have hagree1 : Agrees (flipAt u a) (p :: ps) := agrees_flip hagree hnota
  obtain ⟨t₂, hD1⟩ := descent_rebase hD (flipAt u a)
  have ride := descent_sound_noop hD1 hagree1
  -- Phase 3: hop b's lobe (2 steps); b's stem edge comes from the descent.
  have hb_stem : w.link (3 * b) = some (3 * (lastOf p ps / 3)) :=
    w.symm _ _ (descent_last_link hD)
  have hop2 := lobe_hop w b (3 * (lastOf p ps / 3)) (flipAt u a)
    hb_lobe hb_stem
  -- Phase 4: retrace the cascade backwards (|ps| + 1 steps).
  have hagree2 : Agrees (flipAt (flipAt u a) b) (p :: ps) :=
    agrees_flip hagree1 hnotb
  have back := retrace hD (3 * a) ha_stem (flipAt (flipAt u a) b) hagree2
  -- Assemble: 2 + (|ps|+1) + 2 + (|ps|+1) = 2|ps| + 6.
  have hlen : 2 * ps.length + 6
      = 2 + ((ps.length + 1) + (2 + (p :: ps).length)) := by
    rw [List.length_cons]; omega
  rw [hlen, stepN_add, hop1]
  show (stepN w ((ps.length + 1) + (2 + (p :: ps).length))
    (p, flipAt u a)) = _
  rw [stepN_add, ride]
  show (stepN w (2 + (p :: ps).length) (3 * b, flipAt u a)) = _
  rw [stepN_add, hop2]
  simpa using back

/-- Full period: two half-periods restore the tongues exactly.  The bounce
is a genuine cycle, and its tongue states are precisely the Gray square
`{u, flip a u, flip a (flip b u), flip b u}` at the phase boundaries. -/
theorem dogbone_period
    (w : Wiring) (a b p : Nat) (ps : List Nat) (t₀ t₁ : Tongues) (u : Tongues)
    (ha_lobe : w.link (3 * a + 1) = some (3 * a + 2))
    (hb_lobe : w.link (3 * b + 1) = some (3 * b + 2))
    (ha_stem : w.link (3 * a) = some p)
    (hD : Descent w t₀ p ps (3 * b) t₁)
    (hagree : Agrees u (p :: ps))
    (hnota : ∀ q ∈ p :: ps, q / 3 ≠ a)
    (hnotb : ∀ q ∈ p :: ps, q / 3 ≠ b)
    (hab : a ≠ b) :
    stepN w (2 * (2 * ps.length + 6)) (3 * a, u) = some (3 * a, u) := by
  have h1 := dogbone_halfPeriod w a b p ps t₀ t₁ u
    ha_lobe hb_lobe ha_stem hD hagree hnota hnotb
  have hagree' : Agrees (flipAt (flipAt u a) b) (p :: ps) :=
    agrees_flip (agrees_flip hagree hnota) hnotb
  have h2 := dogbone_halfPeriod w a b p ps t₀ t₁
    (flipAt (flipAt u a) b)
    ha_lobe hb_lobe ha_stem hD hagree' hnota hnotb
  have hflip : flipAt (flipAt (flipAt (flipAt u a) b) a) b = u := by
    rw [flipAt_comm (Ne.symm hab), flipAt_flipAt, flipAt_flipAt]
  have hlen : 2 * (2 * ps.length + 6)
      = (2 * ps.length + 6) + (2 * ps.length + 6) := by omega
  rw [hlen, stepN_add, h1]
  show stepN w (2 * ps.length + 6) (3 * a, flipAt (flipAt u a) b) = _
  rw [h2, hflip]

/-! ## Reflector gadgets: the bounce beyond lobes

A *reflector* is a one-port gadget: a train facing its mouth stem wanders
inside and, a fixed number of steps later, emerges over the mouth's own
edge, with the tongues transformed by a fixed map `τ` on an invariant state
class.  A lobed switch is the smallest reflector (`lobe_isReflector`, with
`τ = flipAt a`); the compound rotators observed in the exhaustive winners
are two-switch reflectors.  The bounce theorem below shows that ANY two
reflectors joined by ANY trailing cascade trap the train forever in a
four-phase cycle whose tongue states are the orbit of the group generated
by `τA, τB` -- for involutions with disjoint support, the Gray square.
This reduces the general cycle theorem to the single remaining claim that
every maximal active cluster implements a reflector interface (C* of
docs/lazy-point-theory.md). -/

/-- A reflector with mouth `g`, exit port `e` (the far end of `g`'s own
edge), period `k`, invariant state class `S` and state map `τ`. -/
def IsReflector (w : Wiring) (g e k : Nat)
    (S : Tongues → Prop) (τ : Tongues → Tongues) : Prop :=
  ∀ u, S u → stepN w k (g, u) = some (e, τ u) ∧ S (τ u)

/-- A lobed switch is a reflector on all states. -/
theorem lobe_isReflector (w : Wiring) (a p : Nat)
    (hlobe : w.link (3 * a + 1) = some (3 * a + 2))
    (hstem : w.link (3 * a) = some p) :
    IsReflector w (3 * a) p 2 (fun _ => True) (flipAt · a) := by
  intro u _
  exact ⟨lobe_hop w a p u hlobe hstem, trivial⟩

/-- **The reflector bounce, half period.**  Reflector A's exit feeds a
trailing cascade landing on reflector B's mouth; B's exit is the cascade's
last stem, so the retrace carries the train straight back to A's mouth.
One half-period applies `τA` then `τB`. -/
theorem reflector_halfPeriod
    (w : Wiring) {gA kA gB kB p : Nat} {ps : List Nat}
    {SA SB : Tongues → Prop} {τA τB : Tongues → Tongues}
    {t₀ t₁ : Tongues}
    (hA : IsReflector w gA p kA SA τA)
    (hB : IsReflector w gB (3 * (lastOf p ps / 3)) kB SB τB)
    (hD : Descent w t₀ p ps gB t₁)
    (hga : w.link gA = some p)
    (hAa : ∀ u, Agrees u (p :: ps) → Agrees (τA u) (p :: ps))
    (hBa : ∀ u, Agrees u (p :: ps) → Agrees (τB u) (p :: ps))
    (u : Tongues) (hSA : SA u) (hSB : SB (τA u))
    (hagree : Agrees u (p :: ps)) :
    stepN w (kA + (ps.length + 1) + kB + (p :: ps).length) (gA, u)
      = some (gA, τB (τA u)) := by
  obtain ⟨hopA, _⟩ := hA u hSA
  have hagree1 : Agrees (τA u) (p :: ps) := hAa u hagree
  obtain ⟨t₂, hD1⟩ := descent_rebase hD (τA u)
  have ride := descent_sound_noop hD1 hagree1
  obtain ⟨hopB, _⟩ := hB (τA u) hSB
  have back := retrace hD gA hga (τB (τA u)) (hBa _ hagree1)
  rw [stepN_add, stepN_add, stepN_add, hopA]
  show ((stepN w (ps.length + 1) (p, τA u)).bind (stepN w kB)).bind
    (stepN w (p :: ps).length) = _
  rw [ride]
  show (stepN w kB (gB, τA u)).bind (stepN w (p :: ps).length) = _
  rw [hopB]
  exact back

/-- **The reflector bounce, full period.**  For involutive, commuting state
maps (disjoint gadget supports), two half-periods restore the tongues
exactly: any reflector pair joined by any cascade is trapped in a genuine
cycle whose tongue states are the Gray orbit `{u, τA u, τB (τA u), τB u}`. -/
theorem reflector_period
    (w : Wiring) {gA kA gB kB p : Nat} {ps : List Nat}
    {SA SB : Tongues → Prop} {τA τB : Tongues → Tongues}
    {t₀ t₁ : Tongues}
    (hA : IsReflector w gA p kA SA τA)
    (hB : IsReflector w gB (3 * (lastOf p ps / 3)) kB SB τB)
    (hD : Descent w t₀ p ps gB t₁)
    (hga : w.link gA = some p)
    (hAa : ∀ u, Agrees u (p :: ps) → Agrees (τA u) (p :: ps))
    (hBa : ∀ u, Agrees u (p :: ps) → Agrees (τB u) (p :: ps))
    (hSAB : ∀ u, SA u → SA (τB (τA u)))
    (hSBB : ∀ u, SB u → SB (τA (τB u)))
    (hcomm : ∀ u, τA (τB u) = τB (τA u))
    (hinvA : ∀ u, τA (τA u) = u)
    (hinvB : ∀ u, τB (τB u) = u)
    (u : Tongues) (hSA : SA u) (hSB : SB (τA u))
    (hagree : Agrees u (p :: ps)) :
    stepN w (2 * (kA + (ps.length + 1) + kB + (p :: ps).length)) (gA, u)
      = some (gA, u) := by
  have h1 := reflector_halfPeriod w hA hB hD hga hAa hBa u hSA hSB hagree
  have hagree2 : Agrees (τB (τA u)) (p :: ps) := hBa _ (hAa _ hagree)
  have hSA2 : SA (τB (τA u)) := hSAB u hSA
  have hSB2 : SB (τA (τB (τA u))) := hSBB (τA u) hSB
  have h2 := reflector_halfPeriod w hA hB hD hga hAa hBa
    (τB (τA u)) hSA2 hSB2 hagree2
  have hflip : τB (τA (τB (τA u))) = u := by
    rw [hcomm (τA u), hinvA, hinvB]
  have hlen : 2 * (kA + (ps.length + 1) + kB + (p :: ps).length)
      = (kA + (ps.length + 1) + kB + (p :: ps).length)
        + (kA + (ps.length + 1) + kB + (p :: ps).length) := by omega
  rw [hlen, stepN_add, h1]
  show stepN w _ (gA, τB (τA u)) = _
  rw [h2, hflip]

end GeneralN
