/-!
# The echo machine: the cycle dynamics of lazy-point wirings, abstracted

Every wiring's trailing structure compiles to a **forest**: each switch's
stem edge fixes its parent (a branch port of another switch = tree edge;
a stem port = this switch is a root, mouth-paired with the root at the
other end; a cap = dead root).  A used cascade *ascends* a tree from its
entry switch to the root and exits through the mouth into the partner
root, whose tree the train then *descends* by facing moves.  Tongues of a
tree are written **only** during its own ascents, and an ascent from
entry slot `e` points the whole ascent path back at `e` — so a descent
from the root always exits at the slot of the tree's **most recent
ascent** (the retrace theorem, `GeneralN.retrace`).  Free branch ports —
**slots** — are paired involutively by the branch-branch track edges
(**jump edges**), and mouth edges pair roots, hence trees, involutively.

The eventual-cycle dynamics therefore reduces to this register machine
("the echo machine"): one register per tree (**cell**) holding the slot
of its last ascent, and the step, from ascent entry `e`:

    write   reg[cell e] := e            -- ascend the tree of e
    read    f := reg[star (cell e)]     -- descend the partner tree
    jump    next entry := bar f         -- cross the jump edge

This file proves, for **all** N (nothing below constrains the number of
cells or slots):

* `reg_write`, `reg_skip`, `reg_stable`, `reg_last_write` — a register
  holds exactly the slot of its cell's most recent ascent;
* `return_jump` — the fundamental step identity: the entry after time
  `k` is `bar` of the last ascent entry of the partner cell;
* `echo` — the repetition identity: every entry produced by two nested
  returns **literally repeats an earlier entry** (the LIFO seed);
* `succ_repeat` / `entry_change_read_change` — alternation propagation:
  two ascents of the same cell produce the same successor unless the
  partner register changed in between;
* `bounce_step` / `bounce_orbit` — on a partner-alternating orbit (the
  dogbone pattern) `e (k+2) = bar (e k)`, hence **every entry of the
  orbit lies in {e 0, bar (e 0), e 1, bar (e 1)}**: at most four
  distinct entries — the Gray square, for all N.
-/

namespace Echo

/-- The echo machine: cells (trees) with an involutive, fixed-point-free
mouth pairing `star`, and slots (free branch ports) with an involutive
jump pairing `bar`.  `cellOf` places each slot in its cell. -/
structure Machine where
  cellOf : Nat → Nat
  star : Nat → Nat
  bar : Nat → Nat
  star_invol : ∀ c, star (star c) = c
  star_ne : ∀ c, star c ≠ c
  bar_invol : ∀ e, bar (bar e) = e

variable (m : Machine)

/-- Register of cell `c` after ascents `e 0, …, e k` (initial registers
`r0 c`: where the untouched tree's tongues point). -/
def reg (e : Nat → Nat) (r0 : Nat → Nat) : Nat → Nat → Nat
  | 0, c => if m.cellOf (e 0) = c then e 0 else r0 c
  | k+1, c => if m.cellOf (e (k+1)) = c then e (k+1) else reg e r0 k c

/-- `e` is a run of the machine from initial registers `r0`: each next
entry is the jump partner of the register of the partner cell. -/
def IsRun (e : Nat → Nat) (r0 : Nat → Nat) : Prop :=
  ∀ k, e (k+1) = m.bar (reg m e r0 k (m.star (m.cellOf (e k))))

variable (e : Nat → Nat) (r0 : Nat → Nat)

/-- Ascending a cell writes its register. -/
theorem reg_write {k c : Nat} (h : m.cellOf (e k) = c) :
    reg m e r0 k c = e k := by
  cases k with
  | zero => simp [reg, h]
  | succ n => simp [reg, h]

/-- Ascending another cell leaves the register alone. -/
theorem reg_skip {k c : Nat} (h : m.cellOf (e (k+1)) ≠ c) :
    reg m e r0 (k+1) c = reg m e r0 k c := by
  simp [reg, h]

/-- A register is stable across any stretch of foreign ascents. -/
theorem reg_stable {i c : Nat} :
    ∀ d, (∀ ℓ, i < ℓ → ℓ ≤ i + d → m.cellOf (e ℓ) ≠ c) →
      reg m e r0 (i + d) c = reg m e r0 i c := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ n ih =>
      intro hno
      have hskip : m.cellOf (e (i + n + 1)) ≠ c := by
        have := hno (i + n + 1) (by omega) (by omega)
        exact this
      calc reg m e r0 (i + (n + 1)) c
          = reg m e r0 (i + n) c := reg_skip m e r0 hskip
        _ = reg m e r0 i c := ih (fun ℓ h1 h2 => hno ℓ h1 (by omega))

/-- A register holds the entry of its cell's most recent ascent. -/
theorem reg_last_write {j k c : Nat} (hc : m.cellOf (e j) = c)
    (hjk : j ≤ k) (hno : ∀ i, j < i → i ≤ k → m.cellOf (e i) ≠ c) :
    reg m e r0 k c = e j := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  calc reg m e r0 (j + d) c
      = reg m e r0 j c := reg_stable m e r0 d (fun ℓ h1 h2 => hno ℓ h1 h2)
    _ = e j := reg_write m e r0 hc

/-- **The fundamental step identity.**  If the partner of the cell
ascended at time `k` was last ascended at time `j`, the next entry is
the jump partner of that ascent's entry: the walk re-enters through the
slot by which the partner tree was last entered. -/
theorem return_jump (hrun : IsRun m e r0) {j k : Nat}
    (hc : m.cellOf (e j) = m.star (m.cellOf (e k))) (hjk : j ≤ k)
    (hno : ∀ i, j < i → i ≤ k → m.cellOf (e i) ≠ m.star (m.cellOf (e k))) :
    e (k+1) = m.bar (e j) := by
  rw [hrun k, reg_last_write m e r0 hc hjk hno]

/-- **The echo (repetition) identity.**  Two nested applications of
`return_jump`: if the partner of cell `k` was last ascended at `j+1`,
and the partner of cell `j` was last ascended at `i`, then the entry
after `k` **repeats the entry at `i`** exactly.  Every step of the
machine replays history: the LIFO seed. -/
theorem echo (hrun : IsRun m e r0) {i j k : Nat}
    (h1c : m.cellOf (e (j+1)) = m.star (m.cellOf (e k))) (h1j : j + 1 ≤ k)
    (h1no : ∀ i', j + 1 < i' → i' ≤ k →
      m.cellOf (e i') ≠ m.star (m.cellOf (e k)))
    (h2c : m.cellOf (e i) = m.star (m.cellOf (e j))) (h2j : i ≤ j)
    (h2no : ∀ ℓ, i < ℓ → ℓ ≤ j → m.cellOf (e ℓ) ≠ m.star (m.cellOf (e j))) :
    e (k+1) = e i := by
  have hk : e (k+1) = m.bar (e (j+1)) := return_jump m e r0 hrun h1c h1j h1no
  have hj : e (j+1) = m.bar (e i) := return_jump m e r0 hrun h2c h2j h2no
  rw [hk, hj, m.bar_invol]

/-- **Alternation propagation, positive form.**  Two ascents of the same
cell whose gap contains no partner-cell ascent produce the *same*
successor entry.  (So an entry change at a cell requires its feeder's
partner to have been ascended in between.) -/
theorem succ_repeat (hrun : IsRun m e r0) {i j : Nat}
    (hcell : m.cellOf (e i) = m.cellOf (e j)) (hij : i ≤ j)
    (hno : ∀ ℓ, i < ℓ → ℓ ≤ j → m.cellOf (e ℓ) ≠ m.star (m.cellOf (e i))) :
    e (j+1) = e (i+1) := by
  have hi := hrun i
  have hj := hrun j
  rw [hcell] at hi hno
  have hreg : reg m e r0 j (m.star (m.cellOf (e j)))
      = reg m e r0 i (m.star (m.cellOf (e j))) := by
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    exact reg_stable m e r0 d (fun ℓ h1 h2 => hno ℓ h1 h2)
  rw [hj, hreg, ← hi]

/-- **Alternation propagation, contrapositive form.**  If two ascents of
the same cell produce different successors, the partner register itself
changed value in between. -/
theorem entry_change_read_change (hrun : IsRun m e r0) {i j : Nat}
    (_hcell : m.cellOf (e i) = m.cellOf (e j))
    (hne : e (j+1) ≠ e (i+1)) :
    reg m e r0 j (m.star (m.cellOf (e j)))
      ≠ reg m e r0 i (m.star (m.cellOf (e i))) := by
  intro heq
  apply hne
  have hi := hrun i
  have hj := hrun j
  rw [hj, heq, ← hi]

/-- Registers are well-formed: if the initial registers hold slots of
their own cells, they do so forever (writes only store own-cell
entries). -/
theorem reg_cell (hr0 : ∀ c, m.cellOf (r0 c) = c) :
    ∀ k c, m.cellOf (reg m e r0 k c) = c := by
  intro k
  induction k with
  | zero =>
      intro c
      by_cases h : m.cellOf (e 0) = c
      · rw [reg_write m e r0 h]; exact h
      · show m.cellOf (if m.cellOf (e 0) = c then e 0 else r0 c) = c
        rw [if_neg h]; exact hr0 c
  | succ n ih =>
      intro c
      by_cases h : m.cellOf (e (n+1)) = c
      · rw [reg_write m e r0 h]; exact h
      · rw [reg_skip m e r0 h]; exact ih c

/-- **The witness identity.**  Every entry names its own delivery: the
cell of `bar (e (k+1))` is exactly the mouth partner of the previous
cell, and that partner's register at read time is exactly
`bar (e (k+1))`.  This pins the walk's predecessor structure — the
formal seed of the delivery-chain (nesting) analysis of lemma B. -/
theorem witness (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) :
    m.cellOf (m.bar (e (k+1))) = m.star (m.cellOf (e k)) ∧
    reg m e r0 k (m.star (m.cellOf (e k))) = m.bar (e (k+1)) := by
  have h := hrun k
  have hv : m.bar (e (k+1)) = reg m e r0 k (m.star (m.cellOf (e k))) := by
    rw [h, m.bar_invol]
  constructor
  · rw [hv]; exact reg_cell m e r0 hr0 k _
  · exact hv.symm

/-- **Merge at the mouth, direct form.**  Two ascents of the same cell
whose partner registers agree at read time have identical successors:
an alternating cell cannot steer its own variation. -/
theorem succ_of_reg_eq (hrun : IsRun m e r0) {i j : Nat}
    (hcell : m.cellOf (e i) = m.cellOf (e j))
    (hreg : reg m e r0 i (m.star (m.cellOf (e i)))
          = reg m e r0 j (m.star (m.cellOf (e j)))) :
    e (i+1) = e (j+1) := by
  rw [hrun i, hrun j, hcell] at *
  exact congrArg m.bar hreg

/-- The dogbone pattern: consecutive ascents are of partner cells. -/
def Alternating : Prop :=
  ∀ k, m.cellOf (e (k+1)) = m.star (m.cellOf (e k))

/-- **The bounce.**  On a partner-alternating run each read sees the
register written two steps ago, so `e (k+2) = bar (e k)`. -/
theorem bounce_step (hrun : IsRun m e r0) (halt : Alternating m e)
    (k : Nat) : e (k+2) = m.bar (e k) := by
  have h1 := hrun (k+1)
  rw [halt k, m.star_invol] at h1
  have hne : m.cellOf (e (k+1)) ≠ m.cellOf (e k) := by
    rw [halt k]
    exact m.star_ne _
  rw [reg_skip m e r0 hne, reg_write m e r0 rfl] at h1
  exact h1

private theorem twoStep (P : Nat → Prop) (h0 : P 0) (h1 : P 1)
    (hs : ∀ n, P n → P (n+2)) : ∀ n, P n
  | 0 => h0
  | 1 => h1
  | n+2 => hs n (twoStep P h0 h1 hs n)

/-- **The Gray square, for all N.**  Every entry of a partner-alternating
run lies in `{e 0, bar (e 0), e 1, bar (e 1)}`: a dogbone-pattern orbit
visits at most four distinct entries, no matter how many switches the
wiring has. -/
theorem bounce_orbit (hrun : IsRun m e r0) (halt : Alternating m e) :
    ∀ k, e k = e 0 ∨ e k = m.bar (e 0) ∨ e k = e 1 ∨ e k = m.bar (e 1) := by
  refine twoStep _ (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) ?_
  intro n ih
  have hb := bounce_step m e r0 hrun halt n
  rcases ih with h | h | h | h
  · rw [hb, h]; exact Or.inr (Or.inl rfl)
  · rw [hb, h, m.bar_invol]; exact Or.inl rfl
  · rw [hb, h]; exact Or.inr (Or.inr (Or.inr rfl))
  · rw [hb, h, m.bar_invol]; exact Or.inr (Or.inr (Or.inl rfl))

/-- An unproductive write — one that rewrites the value already stored —
changes **no** register at all: the machine state can only move through
productive writes. -/
theorem unproductive_stall (k : Nat)
    (h : e (k+1) = reg m e r0 k (m.cellOf (e (k+1)))) :
    ∀ c, reg m e r0 (k+1) c = reg m e r0 k c := by
  intro c
  by_cases hc : m.cellOf (e (k+1)) = c
  · rw [reg_write m e r0 hc, h, hc]
  · exact reg_skip m e r0 hc

private theorem exists_last {P : Nat → Prop} :
    ∀ k, (∃ j, j ≤ k ∧ P j) →
      ∃ j, j ≤ k ∧ P j ∧ ∀ i, j < i → i ≤ k → ¬ P i := by
  intro k
  induction k with
  | zero =>
      intro h
      obtain ⟨j, hj, hp⟩ := h
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0
      exact ⟨0, Nat.le_refl 0, hp, fun i h1 h2 _ => by omega⟩
  | succ n ih =>
      intro h
      obtain ⟨j, hj, hp⟩ := h
      by_cases hn : P (n+1)
      · exact ⟨n+1, Nat.le_refl _, hn, fun i h1 h2 _ => by omega⟩
      · have hj' : j ≤ n := by
          by_cases hje : j = n+1
          · exact absurd (hje ▸ hp) hn
          · omega
        obtain ⟨j', h1, h2, h3⟩ := ih ⟨j, hj', hp⟩
        refine ⟨j', Nat.le_trans h1 (Nat.le_succ n), h2, ?_⟩
        intro i hi1 hi2
        by_cases hie : i = n+1
        · exact hie ▸ hn
        · exact h3 i hi1 (by omega)

/-- **Absorption step.**  If the current entry is one of the lobe slots
`{a, bar a}` of cell A and the partner cell B's register holds one of
its lobe slots `{b, bar b}`, the same holds two steps later — with the
intermediate entry in `{b, bar b}`. -/
private theorem absorb_step (hrun : IsRun m e r0) {a b k : Nat}
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hAB : m.star (m.cellOf a) = m.cellOf b)
    (hek : e k = a ∨ e k = m.bar a)
    (hrB : reg m e r0 k (m.cellOf b) = b ∨
           reg m e r0 k (m.cellOf b) = m.bar b) :
    (e (k+2) = a ∨ e (k+2) = m.bar a) ∧
    (reg m e r0 (k+2) (m.cellOf b) = b ∨
     reg m e r0 (k+2) (m.cellOf b) = m.bar b) := by
  have hne : m.cellOf b ≠ m.cellOf a := by
    rw [← hAB]
    exact m.star_ne _
  have hBA : m.star (m.cellOf b) = m.cellOf a := by
    have h := congrArg m.star hAB
    rw [m.star_invol] at h
    exact h.symm
  have hcellk : m.cellOf (e k) = m.cellOf a := by
    rcases hek with h | h
    · rw [h]
    · rw [h]; exact ha
  have h1 : e (k+1) = m.bar (reg m e r0 k (m.cellOf b)) := by
    have h := hrun k
    rw [hcellk, hAB] at h
    exact h
  have hek1 : e (k+1) = m.bar b ∨ e (k+1) = b := by
    rcases hrB with hr | hr
    · exact Or.inl (by rw [h1, hr])
    · exact Or.inr (by rw [h1, hr, m.bar_invol])
  have hcellk1 : m.cellOf (e (k+1)) = m.cellOf b := by
    rcases hek1 with h | h
    · rw [h]; exact hb
    · rw [h]
  have hrB1 : reg m e r0 (k+1) (m.cellOf b) = e (k+1) :=
    reg_write m e r0 hcellk1
  have hrA : reg m e r0 (k+1) (m.cellOf a) = e k := by
    rw [reg_skip m e r0 (by rw [hcellk1]; exact hne)]
    exact reg_write m e r0 hcellk
  have h2 : e (k+1+1) = m.bar (e k) := by
    have h := hrun (k+1)
    rw [hcellk1, hBA, hrA] at h
    exact h
  have hek2 : e (k+1+1) = a ∨ e (k+1+1) = m.bar a := by
    rcases hek with h | h
    · exact Or.inr (by rw [h2, h])
    · exact Or.inl (by rw [h2, h, m.bar_invol])
  have hcellk2 : m.cellOf (e (k+1+1)) = m.cellOf a := by
    rcases hek2 with h | h
    · rw [h]
    · rw [h]; exact ha
  have hregB2 : reg m e r0 (k+1+1) (m.cellOf b) = e (k+1) := by
    rw [reg_skip m e r0 (by rw [hcellk2]; exact hne.symm)]
    exact hrB1
  refine ⟨hek2, ?_⟩
  rcases hek1 with h | h
  · exact Or.inr (hregB2.trans h)
  · exact Or.inl (hregB2.trans h)

/-- **Absorption: the lobed Gray square is a trap.**  Suppose slots `a`
and `bar a` share a cell A, slots `b` and `bar b` share the partner
cell B = star A.  If the walk ever enters `a` while B's register holds
`b` or `bar b`, then **forever after** the even-step entries stay in
`{a, bar a}` and B's register stays in `{b, bar b}`. -/
theorem absorb (hrun : IsRun m e r0) {a b k0 : Nat}
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hAB : m.star (m.cellOf a) = m.cellOf b)
    (hstart : e k0 = a)
    (hreg : reg m e r0 k0 (m.cellOf b) = b ∨
            reg m e r0 k0 (m.cellOf b) = m.bar b) :
    ∀ t, (e (k0 + 2*t) = a ∨ e (k0 + 2*t) = m.bar a) ∧
         (reg m e r0 (k0 + 2*t) (m.cellOf b) = b ∨
          reg m e r0 (k0 + 2*t) (m.cellOf b) = m.bar b) := by
  intro t
  induction t with
  | zero => exact ⟨Or.inl hstart, hreg⟩
  | succ n ih =>
      exact absorb_step m e r0 hrun ha hb hAB ih.1 ih.2

/-- **The absorbed alternation bound.**  After absorption every entry —
even and odd steps alike — lies in the four-element set
`{a, bar a, b, bar b}`: the run is captured by the dogbone pattern, so
every later write (productive or not) happens in the two cells A, B,
and the eventual cycle carries at most four distinct entries.  This is
the machine form of the lobed case of the cycle theorem. -/
theorem absorb_entries (hrun : IsRun m e r0) {a b k0 : Nat}
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hAB : m.star (m.cellOf a) = m.cellOf b)
    (hstart : e k0 = a)
    (hreg : reg m e r0 k0 (m.cellOf b) = b ∨
            reg m e r0 k0 (m.cellOf b) = m.bar b) :
    ∀ j, k0 ≤ j →
      e j = a ∨ e j = m.bar a ∨ e j = b ∨ e j = m.bar b := by
  intro j hj
  obtain ⟨d, rfl⟩ : ∃ d, j = k0 + d := ⟨j - k0, by omega⟩
  have habs := absorb m e r0 hrun ha hb hAB hstart hreg
  have hsplit : d = 2 * (d / 2) ∨ d = 2 * (d / 2) + 1 := by omega
  rcases hsplit with h | h
  · rcases (habs (d / 2)).1 with he | he
    · rw [h]; exact Or.inl he
    · rw [h]; exact Or.inr (Or.inl he)
  · have hek := (habs (d / 2)).1
    have hcellk : m.cellOf (e (k0 + 2 * (d / 2))) = m.cellOf a := by
      rcases hek with he | he
      · rw [he]
      · rw [he]; exact ha
    have h1 : e (k0 + 2 * (d / 2) + 1)
        = m.bar (reg m e r0 (k0 + 2 * (d / 2)) (m.cellOf b)) := by
      have hh := hrun (k0 + 2 * (d / 2))
      rw [hcellk, hAB] at hh
      exact hh
    have hodd : e (k0 + 2 * (d / 2) + 1) = m.bar b ∨
        e (k0 + 2 * (d / 2) + 1) = b := by
      rcases (habs (d / 2)).2 with hr | hr
      · exact Or.inl (by rw [h1, hr])
      · exact Or.inr (by rw [h1, hr, m.bar_invol])
    rw [h]
    rcases hodd with he | he
    · exact Or.inr (Or.inr (Or.inr he))
    · exact Or.inr (Or.inr (Or.inl he))

/-- **The accounting theorem** (unconditional, general N).  A productive
write is either the **first** write of its cell — at most one per cell,
i.e. at most N over the whole run — or an **alternation**: it differs
from that cell's most recent previous write.  Together with
`unproductive_stall` this is the skeleton of f(N) ≤ N + O(1): every
change of the machine state is a first ascent or an alternation, so the
state count is 1 + #first-ascents + #alternations, and the two open
lemmas B and C only have to bound the alternations. -/
theorem productive_first_or_alternation (k : Nat)
    (hprod : e (k+1) ≠ reg m e r0 k (m.cellOf (e (k+1)))) :
    (∀ j, j ≤ k → m.cellOf (e j) ≠ m.cellOf (e (k+1))) ∨
    (∃ j, j ≤ k ∧ m.cellOf (e j) = m.cellOf (e (k+1)) ∧
      (∀ i, j < i → i ≤ k → m.cellOf (e i) ≠ m.cellOf (e (k+1))) ∧
      e (k+1) ≠ e j) := by
  by_cases hex : ∃ j, j ≤ k ∧ m.cellOf (e j) = m.cellOf (e (k+1))
  · right
    obtain ⟨j, hjk, hjc, hlast⟩ :=
      exists_last (P := fun j => m.cellOf (e j) = m.cellOf (e (k+1))) k hex
    refine ⟨j, hjk, hjc, hlast, ?_⟩
    have hreg : reg m e r0 k (m.cellOf (e (k+1))) = e j :=
      reg_last_write m e r0 hjc hjk hlast
    intro heq
    exact hprod (heq.trans hreg.symm)
  · left
    intro j hjk hc
    exact hex ⟨j, hjk, hc⟩

/-! ## The counting scaffold around the open core

The actual target theorem — in the language of tracks and switches —
is `GeneralN.StateLaw` in `StateLaw.lean`, and **it is open**.  This
section proves only the counting that surrounds the open core: IF a
run's snapshots eventually stay in a ≤4-element set (the Gray tail —
open) and at most one alternation precedes that tail (open), THEN at
most `#cells + 6` distinct snapshots occur.  The two IFs are the hard
part of the problem, not side conditions; nothing here discharges
them. -/

/-- The register snapshot at time `k` on a finite list of cells. -/
def snap (cells : List Nat) (k : Nat) : List Nat :=
  cells.map (reg m e r0 k)

/-- Step `k → k+1` changes the written cell's register. -/
def ProductiveStep (k : Nat) : Prop :=
  e (k+1) ≠ reg m e r0 k (m.cellOf (e (k+1)))

/-- Step `k → k+1` performs the first write of its cell. -/
def FirstStep (k : Nat) : Prop :=
  ∀ j, j ≤ k → m.cellOf (e j) ≠ m.cellOf (e (k+1))

private theorem map_congr' {f g : Nat → Nat} :
    ∀ l : List Nat, (∀ x ∈ l, f x = g x) → l.map f = l.map g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x t ih =>
      intro h
      simp only [List.map_cons]
      rw [h x List.mem_cons_self,
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Unproductive steps do not move the snapshot. -/
theorem snap_stall (cells : List Nat) {k : Nat}
    (h : ¬ ProductiveStep m e r0 k) :
    snap m e r0 cells (k+1) = snap m e r0 cells k := by
  have heq : e (k+1) = reg m e r0 k (m.cellOf (e (k+1))) := by
    by_cases hq : e (k+1) = reg m e r0 k (m.cellOf (e (k+1)))
    · exact hq
    · exact absurd hq h
  exact map_congr' _ (fun c _ => unproductive_stall m e r0 k heq c)

/-- Snapshots are constant across productive-free stretches. -/
theorem snap_between (cells : List Nat) (a : Nat) :
    ∀ d, (∀ i, a ≤ i → i < a + d → ¬ ProductiveStep m e r0 i) →
      snap m e r0 cells (a + d) = snap m e r0 cells a := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      calc snap m e r0 cells (a + (n+1))
          = snap m e r0 cells (a + n) :=
            snap_stall m e r0 cells (h (a+n) (by omega) (by omega))
        _ = snap m e r0 cells a :=
            ih (fun i h1 h2 => h i h1 (by omega))

private theorem exists_last_lt {P : Nat → Prop} :
    ∀ k, (∃ j, j < k ∧ P j) →
      ∃ j, j < k ∧ P j ∧ ∀ i, j < i → i < k → ¬ P i := by
  intro k
  induction k with
  | zero =>
      intro h
      obtain ⟨j, hj, _⟩ := h
      exact absurd hj (by omega)
  | succ n ih =>
      intro h
      by_cases hn : P n
      · exact ⟨n, by omega, hn, fun i h1 h2 _ => by omega⟩
      · obtain ⟨j, hj, hp⟩ := h
        have hj' : j < n := by
          by_cases hje : j = n
          · exact absurd (hje ▸ hp) hn
          · omega
        obtain ⟨j', h1, h2, h3⟩ := ih ⟨j, hj', hp⟩
        refine ⟨j', by omega, h2, ?_⟩
        intro i hi1 hi2
        by_cases hie : i = n
        · exact hie ▸ hn
        · exact h3 i hi1 (by omega)

open Classical in
/-- The tag of time `k`: 0 if no productive step precedes `k`; else,
for the last productive step `j` before `k`, the written cell's code
(first write) or 1 (alternation). -/
private noncomputable def codeOf (k : Nat) : Nat :=
  if h : ∃ j, j < k ∧ ProductiveStep m e r0 j then
    if FirstStep m e (exists_last_lt k h).choose
    then m.cellOf (e ((exists_last_lt k h).choose + 1)) + 2
    else 1
  else 0

private theorem codeOf_spec (cells : List Nat) (k : Nat) :
    (codeOf m e r0 k = 0 ∧
      snap m e r0 cells k = snap m e r0 cells 0) ∨
    (∃ j, j < k ∧ ProductiveStep m e r0 j ∧
      snap m e r0 cells k = snap m e r0 cells (j+1) ∧
      ((FirstStep m e j ∧ codeOf m e r0 k = m.cellOf (e (j+1)) + 2) ∨
       (¬ FirstStep m e j ∧ codeOf m e r0 k = 1))) := by
  by_cases h : ∃ j, j < k ∧ ProductiveStep m e r0 j
  · right
    obtain ⟨hj, hp, hno⟩ := (exists_last_lt k h).choose_spec
    refine ⟨(exists_last_lt k h).choose, hj, hp, ?_, ?_⟩
    · have hd : (exists_last_lt k h).choose + 1 +
          (k - ((exists_last_lt k h).choose + 1)) = k := by omega
      have hsb := snap_between m e r0 cells
        ((exists_last_lt k h).choose + 1)
        (k - ((exists_last_lt k h).choose + 1))
        (fun i h1 h2 => hno i (by omega) (by omega))
      rw [hd] at hsb
      exact hsb
    · by_cases hf : FirstStep m e (exists_last_lt k h).choose
      · exact Or.inl ⟨hf, by unfold codeOf; rw [dif_pos h, if_pos hf]⟩
      · exact Or.inr ⟨hf, by unfold codeOf; rw [dif_pos h, if_neg hf]⟩
  · left
    constructor
    · unfold codeOf; rw [dif_neg h]
    · have hsb := snap_between m e r0 cells 0 k
        (fun i _ h2 => fun hp => h ⟨i, by omega, hp⟩)
      rw [Nat.zero_add] at hsb
      exact hsb

private theorem mem_len_one {l : List Nat} (h : l.length ≤ 1) :
    ∀ {a b : Nat}, a ∈ l → b ∈ l → a = b := by
  intro a b ha hb
  cases l with
  | nil => cases ha
  | cons x t =>
      cases t with
      | nil =>
          have ha' : a = x := by simpa using ha
          have hb' : b = x := by simpa using hb
          rw [ha', hb']
      | cons y t2 => simp only [List.length_cons] at h; omega

/-- Equal codes force equal snapshots (before the tail). -/
private theorem code_eq_snap_eq (cells : List Nat) (K : Nat)
    (alts : List Nat) (halts : alts.length ≤ 1)
    (hcover : ∀ i, i < K → ProductiveStep m e r0 i →
      FirstStep m e i ∨ i ∈ alts)
    {k1 k2 : Nat} (h1 : k1 < K) (h2 : k2 < K)
    (hc : codeOf m e r0 k1 = codeOf m e r0 k2) :
    snap m e r0 cells k1 = snap m e r0 cells k2 := by
  rcases codeOf_spec m e r0 cells k1 with ⟨c1, s1⟩ | ⟨j1, hj1, hp1, hs1, hcase1⟩
  · rcases codeOf_spec m e r0 cells k2 with ⟨c2, s2⟩ | ⟨j2, hj2, hp2, hs2, hcase2⟩
    · rw [s1, s2]
    · rcases hcase2 with ⟨_, hcode⟩ | ⟨_, hcode⟩ <;>
        (rw [c1, hcode] at hc; omega)
  · rcases codeOf_spec m e r0 cells k2 with ⟨c2, s2⟩ | ⟨j2, hj2, hp2, hs2, hcase2⟩
    · rcases hcase1 with ⟨_, hcode⟩ | ⟨_, hcode⟩ <;>
        (rw [c2, hcode] at hc; omega)
    · rcases hcase1 with ⟨hf1, hcode1⟩ | ⟨hnf1, hcode1⟩ <;>
        rcases hcase2 with ⟨hf2, hcode2⟩ | ⟨hnf2, hcode2⟩
      · have hcell : m.cellOf (e (j1+1)) = m.cellOf (e (j2+1)) := by
          rw [hcode1, hcode2] at hc; omega
        have hj : j1 = j2 := by
          rcases Nat.lt_trichotomy j1 j2 with h | h | h
          · exact absurd hcell (hf2 (j1+1) (by omega))
          · exact h
          · exact absurd hcell.symm (hf1 (j2+1) (by omega))
        rw [hs1, hs2, hj]
      · rw [hcode1, hcode2] at hc; omega
      · rw [hcode1, hcode2] at hc; omega
      · have m1 : j1 ∈ alts :=
          (hcover j1 (by omega) hp1).resolve_left hnf1
        have m2 : j2 ∈ alts :=
          (hcover j2 (by omega) hp2).resolve_left hnf2
        have hj : j1 = j2 := mem_len_one halts m1 m2
        rw [hs1, hs2, hj]

private theorem nodup_transfer {f : Nat → List Nat} {c : Nat → Nat} :
    ∀ l : List Nat, (∀ x ∈ l, ∀ y ∈ l, c x = c y → f x = f y) →
      (l.map f).Nodup → (l.map c).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x t ih =>
      intro hinj hnd
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      refine ⟨?_, ih (fun a ha b hb =>
        hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        hnd.2⟩
      intro hmem
      obtain ⟨y, hy, hcy⟩ := List.mem_map.mp hmem
      have hfy : f x = f y :=
        hinj x List.mem_cons_self y (List.mem_cons_of_mem _ hy) hcy.symm
      exact hnd.1 (List.mem_map.mpr ⟨y, hy, hfy.symm⟩)

private theorem nodup_subset_length {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l S : List α},
    l.Nodup → (∀ x ∈ l, x ∈ S) → l.length ≤ S.length := by
  intro l
  induction l with
  | nil => intro S _ _; exact Nat.zero_le _
  | cons x t ih =>
      intro S hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ t, y ∈ S.erase x := by
        intro y hy
        have hyS : y ∈ S := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hih := ih hnd.2 hsub'
      have hlen : (S.erase x).length = S.length - 1 :=
        List.length_erase_of_mem hx
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons a t2 => simp
      simp only [List.length_cons]
      omega

private theorem filter_split (p : Nat → Bool) :
    ∀ l : List Nat,
      (l.filter p).length + (l.filter (fun x => !(p x))).length
        = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      cases hp : p x with
      | true => simp [hp]; omega
      | false => simp [hp]; omega

private theorem nodup_map_filter {f : Nat → List Nat} {p : Nat → Bool} :
    ∀ {l : List Nat}, (l.map f).Nodup → ((l.filter p).map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x t ih =>
      intro h
      simp only [List.map_cons, List.nodup_cons] at h
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          refine ⟨?_, ih h.2⟩
          intro hmem
          obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
          exact h.1 (List.mem_map.mpr
            ⟨y, (List.mem_filter.mp hy).1, hfy⟩)
      | false =>
          simp only [List.filter_cons, hp]
          exact ih h.2

open Classical in
/-- **Conditional counting scaffold — NOT the state law.**  IF a run
has a Gray tail (`htail`: from some `K` on the snapshot lies in a
fixed ≤4-element set) and at most one alternation before it
(`hcover`/`halts`), THEN at most `#cells + 6` distinct snapshots
occur.  Those two hypotheses are **the open core of the problem — the
hard part**, unproved for general runs; what this theorem contributes
is only the counting around them: snapshot stability, last-write
extraction, first-write injectivity, the coding.  The actual target
statement lives in `StateLaw.lean` (`GeneralN.StateLaw`) and is open. -/
theorem state_law (_hrun : IsRun m e r0)
    (cells : List Nat) (hcells : ∀ k, m.cellOf (e k) ∈ cells)
    (K : Nat) (S : List (List Nat)) (hS : S.length ≤ 4)
    (htail : ∀ j, K ≤ j → snap m e r0 cells j ∈ S)
    (alts : List Nat) (halts : alts.length ≤ 1)
    (hcover : ∀ i, i < K → ProductiveStep m e r0 i →
      FirstStep m e i ∨ i ∈ alts)
    (ks : List Nat)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ cells.length + 6 := by
  have hsplit := filter_split (fun k => decide (k < K)) ks
  -- tail: distinct snapshots inside S
  have htailpart :
      (ks.filter (fun k => !(decide (k < K)))).length ≤ 4 := by
    have hnd2 := nodup_map_filter
      (p := fun k => !(decide (k < K))) hnd
    have hmem : ∀ v ∈ (ks.filter (fun k => !(decide (k < K)))).map
        (snap m e r0 cells), v ∈ S := by
      intro v hv
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      have hk2 := (List.mem_filter.mp hk).2
      have hK : K ≤ k := by
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hk2
        omega
      exact htail k hK
    have hle := nodup_subset_length hnd2 hmem
    rw [List.length_map] at hle
    omega
  -- transient: inject into 0 :: 1 :: cells.map (· + 2)
  have htrans :
      (ks.filter (fun k => decide (k < K))).length
        ≤ cells.length + 2 := by
    have hltK : ∀ k ∈ ks.filter (fun k => decide (k < K)), k < K := by
      intro k hk
      have := (List.mem_filter.mp hk).2
      simpa using this
    have hndl := nodup_map_filter (p := fun k => decide (k < K)) hnd
    have hcodes : ((ks.filter (fun k => decide (k < K))).map
        (codeOf m e r0)).Nodup :=
      nodup_transfer _
        (fun x hx y hy hc => code_eq_snap_eq m e r0 cells K alts halts
          hcover (hltK x hx) (hltK y hy) hc)
        hndl
    have hmemcodes : ∀ v ∈ (ks.filter (fun k => decide (k < K))).map
        (codeOf m e r0), v ∈ 0 :: 1 :: cells.map (· + 2) := by
      intro v hv
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hv
      rcases codeOf_spec m e r0 cells k with ⟨hc0, _⟩ |
        ⟨j, _, _, _, hcase⟩
      · rw [hc0]; exact List.mem_cons_self
      · rcases hcase with ⟨_, hcode⟩ | ⟨_, hcode⟩
        · rw [hcode]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨_, hcells (j+1), rfl⟩))
        · rw [hcode]
          exact List.mem_cons_of_mem _ List.mem_cons_self
    have hle := nodup_subset_length hcodes hmemcodes
    rw [List.length_map] at hle
    simp only [List.length_cons, List.length_map] at hle
    omega
  omega

/-! ## The heat structure (unconditional)

A slot is **confirmed** when its own cell's register points at it; each
cell confirms exactly one slot.  Every step's read value is confirmed
(`head_confirmed`), so the walk always traverses an edge out of a
confirmed slot; the step is productive exactly when the *arrival* end
is unconfirmed with confirmed partner — a **token** (`arrival_token`).
A productive step consumes its token and can create at most one new
one, at the evicted slot of the same cell (`token_step`).  Hence the
total number of tokens — the machine's capacity for future
alternations — **never increases** (`tokens_nonincreasing`) and is at
most one per cell at every moment (`tokens_le_cells`).  These are
theorems about arbitrary runs, no hypotheses beyond well-formed
initial registers.  What they do NOT give: a bound on the number of
alternation *events* (a token can be consumed and re-emitted forever —
that is exactly the Gray flip), so the open core stands. -/

/-- Slot `s` is confirmed at time `k`: its cell's register points at it. -/
def Confirmed (k s : Nat) : Prop :=
  reg m e r0 k (m.cellOf s) = s

/-- The confirmation dynamics: after step `k`, a slot is confirmed iff
it is the arrival, or it kept a confirmation outside the written cell. -/
theorem confirmed_step (k s : Nat) :
    Confirmed m e r0 (k+1) s ↔
      (s = e (k+1) ∨
       (m.cellOf s ≠ m.cellOf (e (k+1)) ∧ Confirmed m e r0 k s)) := by
  unfold Confirmed
  by_cases hc : m.cellOf s = m.cellOf (e (k+1))
  · rw [hc, reg_write m e r0 rfl]
    constructor
    · intro h; exact Or.inl h.symm
    · rintro (h | ⟨hne, _⟩)
      · exact h.symm
      · exact absurd rfl hne
  · rw [reg_skip m e r0 (fun h => hc h.symm)]
    constructor
    · intro h; exact Or.inr ⟨hc, h⟩
    · rintro (rfl | ⟨_, h⟩)
      · exact absurd rfl hc
      · exact h

/-- Every step reads a confirmed slot: the traversed edge's head is
always confirmed. -/
theorem head_confirmed (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (k : Nat) :
    Confirmed m e r0 k (m.bar (e (k+1))) := by
  have hw := witness m e r0 hrun hr0 k
  unfold Confirmed
  rw [hw.1]
  exact hw.2

/-- A **token**: an unconfirmed slot whose jump partner is confirmed —
a hot edge end, the only kind of place a productive step can land. -/
def TokenEnd (k s : Nat) : Prop :=
  ¬ Confirmed m e r0 k s ∧ Confirmed m e r0 k (m.bar s)

instance (k s : Nat) : Decidable (TokenEnd m e r0 k s) := by
  unfold TokenEnd Confirmed
  infer_instance

/-- A productive step lands exactly on a token. -/
theorem arrival_token (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (k : Nat)
    (hp : ProductiveStep m e r0 k) :
    TokenEnd m e r0 k (e (k+1)) := by
  constructor
  · intro h
    exact hp h.symm
  · exact head_confirmed m e r0 hrun hr0 k

/-- A slot that loses confirmation at step `k` is the written cell's
evicted register. -/
theorem lost_confirmation {k s : Nat} (hk : Confirmed m e r0 k s)
    (hk1 : ¬ Confirmed m e r0 (k+1) s) :
    s = reg m e r0 k (m.cellOf (e (k+1))) := by
  have h1 : ¬(s = e (k+1) ∨
      (m.cellOf s ≠ m.cellOf (e (k+1)) ∧ Confirmed m e r0 k s)) :=
    fun h => hk1 ((confirmed_step m e r0 k s).mpr h)
  have hcs : m.cellOf s = m.cellOf (e (k+1)) := by
    by_cases hc : m.cellOf s = m.cellOf (e (k+1))
    · exact hc
    · exact absurd (Or.inr ⟨hc, hk⟩) h1
  unfold Confirmed at hk
  rw [hcs] at hk
  exact hk.symm

/-- **Token bookkeeping.**  Any token present after step `k` is either
the freshly evicted register of the written cell, or was already a
token before the step (and is not the arrival). -/
theorem token_step (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (k s : Nat)
    (ht : TokenEnd m e r0 (k+1) s) :
    s = reg m e r0 k (m.cellOf (e (k+1))) ∨
    (TokenEnd m e r0 k s ∧ s ≠ e (k+1)) := by
  obtain ⟨hu, hb⟩ := ht
  have hse : s ≠ e (k+1) := by
    intro h
    exact hu ((confirmed_step m e r0 k s).mpr (Or.inl h))
  rcases (confirmed_step m e r0 k (m.bar s)).mp hb with hbe | ⟨_, hbk⟩
  · have hs : s = m.bar (e (k+1)) := by rw [← hbe, m.bar_invol]
    have hck : Confirmed m e r0 k s :=
      hs ▸ head_confirmed m e r0 hrun hr0 k
    exact Or.inl (lost_confirmation m e r0 hck hu)
  · by_cases hcs : Confirmed m e r0 k s
    · exact Or.inl (lost_confirmation m e r0 hcs hu)
    · exact Or.inr ⟨⟨hcs, hbk⟩, hse⟩

/-- The tokens present at time `k`, listed over a slot universe. -/
def tokenEnds (slots : List Nat) (k : Nat) : List Nat :=
  slots.filter (fun s => decide (TokenEnd m e r0 k s))

private theorem nodup_filter (p : Nat → Bool) :
    ∀ {l : List Nat}, l.Nodup → (l.filter p).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x t ih =>
      intro h
      rw [List.nodup_cons] at h
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hmem => h.1 ((List.mem_filter.mp hmem).1), ih h.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih h.2

private theorem nodup_map_on {f : Nat → Nat} :
    ∀ {l : List Nat}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) →
      l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x t ih =>
      intro hinj hnd
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih (fun a ha b hb =>
        hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        hnd.2⟩
      intro hmem
      obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
      exact hnd.1 (hinj y (List.mem_cons_of_mem _ hy) x
        List.mem_cons_self hfy ▸ hy)

/-- **Heat never grows.**  The number of tokens is non-increasing along
the run: a productive step consumes its token and creates at most one
(at the evicted slot); an unproductive step moves nothing. -/
theorem tokens_nonincreasing (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (slots : List Nat) (hnd : slots.Nodup)
    (hslots : ∀ j, e j ∈ slots) (k : Nat) :
    (tokenEnds m e r0 slots (k+1)).length
      ≤ (tokenEnds m e r0 slots k).length := by
  by_cases hp : ProductiveStep m e r0 k
  · have harr : e (k+1) ∈ tokenEnds m e r0 slots k := by
      rw [tokenEnds, List.mem_filter]
      exact ⟨hslots (k+1),
        decide_eq_true (arrival_token m e r0 hrun hr0 k hp)⟩
    have hsub : ∀ s ∈ tokenEnds m e r0 slots (k+1),
        s ∈ reg m e r0 k (m.cellOf (e (k+1))) ::
          (tokenEnds m e r0 slots k).erase (e (k+1)) := by
      intro s hs
      rw [tokenEnds, List.mem_filter] at hs
      have hT : TokenEnd m e r0 (k+1) s := of_decide_eq_true hs.2
      rcases token_step m e r0 hrun hr0 k s hT with hv | ⟨hTk, hne⟩
      · rw [hv]; exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ ?_
        rw [List.mem_erase_of_ne hne, tokenEnds, List.mem_filter]
        exact ⟨hs.1, decide_eq_true hTk⟩
    have hnd1 : (tokenEnds m e r0 slots (k+1)).Nodup :=
      nodup_filter _ hnd
    have hlen := nodup_subset_length hnd1 hsub
    rw [List.length_cons, List.length_erase_of_mem harr] at hlen
    have hpos : 0 < (tokenEnds m e r0 slots k).length := by
      cases htk : tokenEnds m e r0 slots k with
      | nil => rw [htk] at harr; cases harr
      | cons a t => simp
    omega
  · have heq : e (k+1) = reg m e r0 k (m.cellOf (e (k+1))) := by
      by_cases hq : e (k+1) = reg m e r0 k (m.cellOf (e (k+1)))
      · exact hq
      · exact absurd hq hp
    have hstall := unproductive_stall m e r0 k heq
    have hEq : tokenEnds m e r0 slots (k+1)
        = tokenEnds m e r0 slots k := by
      unfold tokenEnds
      apply List.filter_congr
      intro s _
      have h1 : Confirmed m e r0 (k+1) s ↔ Confirmed m e r0 k s := by
        unfold Confirmed; rw [hstall]
      have h2 : Confirmed m e r0 (k+1) (m.bar s) ↔
          Confirmed m e r0 k (m.bar s) := by
        unfold Confirmed; rw [hstall]
      exact decide_eq_decide.mpr (by unfold TokenEnd; rw [h1, h2])
    rw [hEq]
    exact Nat.le_refl _

/-- The tokens of cell `C` at time `k`. -/
def cellTokens (slots : List Nat) (C k : Nat) : List Nat :=
  slots.filter (fun s => decide (TokenEnd m e r0 k s ∧ m.cellOf s = C))

/-- Unproductive steps do not move any cell's token set. -/
theorem cellTokens_stall {k : Nat}
    (heq : e (k+1) = reg m e r0 k (m.cellOf (e (k+1))))
    (slots : List Nat) (C : Nat) :
    cellTokens m e r0 slots C (k+1) = cellTokens m e r0 slots C k := by
  unfold cellTokens
  apply List.filter_congr
  intro s _
  have hstall := unproductive_stall m e r0 k heq
  have h1 : Confirmed m e r0 (k+1) s ↔ Confirmed m e r0 k s := by
    unfold Confirmed; rw [hstall]
  have h2 : Confirmed m e r0 (k+1) (m.bar s) ↔
      Confirmed m e r0 k (m.bar s) := by
    unfold Confirmed; rw [hstall]
  exact decide_eq_decide.mpr (by unfold TokenEnd; rw [h1, h2])

/-- **Freeze-out.**  A cell with no tokens never changes its register
again: a productive arrival needs a token of the cell it writes, and
no step can hand a tokenless cell a new one (fresh tokens appear only
at the evicted slot of the written cell itself).  Unconditional. -/
theorem freezeout (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (slots : List Nat) (hslots : ∀ j, e j ∈ slots)
    {C k : Nat} (h0 : ∀ s, s ∉ cellTokens m e r0 slots C k) :
    ∀ d, (∀ s, s ∉ cellTokens m e r0 slots C (k+d)) ∧
      reg m e r0 (k+d) C = reg m e r0 k C := by
  intro d
  induction d with
  | zero => exact ⟨h0, rfl⟩
  | succ n ih =>
      obtain ⟨htok, hreg⟩ := ih
      by_cases hp : ProductiveStep m e r0 (k+n)
      · have hD : m.cellOf (e (k+n+1)) ≠ C := by
          intro hDC
          have ht := arrival_token m e r0 hrun hr0 (k+n) hp
          have hmem : e (k+n+1) ∈ cellTokens m e r0 slots C (k+n) := by
            rw [cellTokens, List.mem_filter]
            exact ⟨hslots (k+n+1), decide_eq_true ⟨ht, hDC⟩⟩
          exact htok _ hmem
        constructor
        · show ∀ s, s ∉ cellTokens m e r0 slots C (k+n+1)
          intro s hs
          rw [cellTokens, List.mem_filter] at hs
          obtain ⟨hT, hC⟩ := of_decide_eq_true hs.2
          rcases token_step m e r0 hrun hr0 (k+n) s hT with hv | ⟨hTk, _⟩
          · have hcs : m.cellOf s = m.cellOf (e (k+n+1)) := by
              rw [hv]; exact reg_cell m e r0 hr0 (k+n) _
            exact hD (hcs.symm.trans hC)
          · exact htok s (by
              rw [cellTokens, List.mem_filter]
              exact ⟨hs.1, decide_eq_true ⟨hTk, hC⟩⟩)
        · show reg m e r0 (k+n+1) C = reg m e r0 k C
          rw [reg_skip m e r0 hD]
          exact hreg
      · have heq : e (k+n+1) = reg m e r0 (k+n) (m.cellOf (e (k+n+1))) := by
          by_cases hq : e (k+n+1) = reg m e r0 (k+n) (m.cellOf (e (k+n+1)))
          · exact hq
          · exact absurd hq hp
        constructor
        · show ∀ s, s ∉ cellTokens m e r0 slots C (k+n+1)
          rw [cellTokens_stall m e r0 heq slots C]
          exact htok
        · show reg m e r0 (k+n+1) C = reg m e r0 k C
          rw [unproductive_stall m e r0 (k+n) heq C]
          exact hreg

/-- **The singleton lock.**  A cell whose tokens all equal one slot `t`
keeps its register in the two-element set `{current register, t}`
**forever**: its productive arrivals can only consume `t` or its own
re-emissions, so the register bounces between at most two values.
This is the σ ≤ 2 half of lemma B for singleton-token cells,
unconditional. -/
theorem singleton_lock (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (slots : List Nat) (hslots : ∀ j, e j ∈ slots)
    {C k t : Nat}
    (h1 : ∀ s ∈ cellTokens m e r0 slots C k, s = t) :
    ∀ d, (reg m e r0 (k+d) C = reg m e r0 k C ∨
          reg m e r0 (k+d) C = t) ∧
      (∀ s ∈ cellTokens m e r0 slots C (k+d),
        s = reg m e r0 k C ∨ s = t) := by
  intro d
  induction d with
  | zero => exact ⟨Or.inl rfl, fun s hs => Or.inr (h1 s hs)⟩
  | succ n ih =>
      obtain ⟨hregmem, htokmem⟩ := ih
      by_cases hp : ProductiveStep m e r0 (k+n)
      · by_cases hD : m.cellOf (e (k+n+1)) = C
        · have harr : e (k+n+1) ∈ cellTokens m e r0 slots C (k+n) := by
            rw [cellTokens, List.mem_filter]
            exact ⟨hslots _, decide_eq_true
              ⟨arrival_token m e r0 hrun hr0 (k+n) hp, hD⟩⟩
          have harrmem := htokmem _ harr
          have hregnew : reg m e r0 (k+n+1) C = e (k+n+1) := by
            rw [← hD]
            exact reg_write m e r0 rfl
          constructor
          · show reg m e r0 (k+n+1) C = reg m e r0 k C ∨
                reg m e r0 (k+n+1) C = t
            rw [hregnew]
            exact harrmem
          · show ∀ s ∈ cellTokens m e r0 slots C (k+n+1),
                s = reg m e r0 k C ∨ s = t
            intro s hs
            rw [cellTokens, List.mem_filter] at hs
            obtain ⟨hT, hC⟩ := of_decide_eq_true hs.2
            rcases token_step m e r0 hrun hr0 (k+n) s hT with hv | ⟨hTk, _⟩
            · rw [hv, hD]
              exact hregmem
            · exact htokmem s (by
                rw [cellTokens, List.mem_filter]
                exact ⟨hs.1, decide_eq_true ⟨hTk, hC⟩⟩)
        · constructor
          · show reg m e r0 (k+n+1) C = reg m e r0 k C ∨
                reg m e r0 (k+n+1) C = t
            rw [reg_skip m e r0 hD]
            exact hregmem
          · show ∀ s ∈ cellTokens m e r0 slots C (k+n+1),
                s = reg m e r0 k C ∨ s = t
            intro s hs
            rw [cellTokens, List.mem_filter] at hs
            obtain ⟨hT, hC⟩ := of_decide_eq_true hs.2
            rcases token_step m e r0 hrun hr0 (k+n) s hT with hv | ⟨hTk, _⟩
            · have hcs : m.cellOf s = m.cellOf (e (k+n+1)) := by
                rw [hv]; exact reg_cell m e r0 hr0 (k+n) _
              exact absurd (hcs.symm.trans hC) hD
            · exact htokmem s (by
                rw [cellTokens, List.mem_filter]
                exact ⟨hs.1, decide_eq_true ⟨hTk, hC⟩⟩)
      · have heq : e (k+n+1) = reg m e r0 (k+n) (m.cellOf (e (k+n+1))) := by
          by_cases hq : e (k+n+1) = reg m e r0 (k+n) (m.cellOf (e (k+n+1)))
          · exact hq
          · exact absurd hq hp
        constructor
        · show reg m e r0 (k+n+1) C = reg m e r0 k C ∨
              reg m e r0 (k+n+1) C = t
          rw [unproductive_stall m e r0 (k+n) heq C]
          exact hregmem
        · show ∀ s ∈ cellTokens m e r0 slots C (k+n+1),
              s = reg m e r0 k C ∨ s = t
          rw [cellTokens_stall m e r0 heq slots C]
          exact htokmem

/-- Register form of the singleton lock: from the moment a cell's
tokens are contained in `{t}`, its register takes at most two values,
ever. -/
theorem singleton_lock_reg (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (slots : List Nat) (hslots : ∀ j, e j ∈ slots)
    {C k t : Nat}
    (h1 : ∀ s ∈ cellTokens m e r0 slots C k, s = t)
    {j : Nat} (hj : k ≤ j) :
    reg m e r0 j C = reg m e r0 k C ∨ reg m e r0 j C = t := by
  obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
  exact (singleton_lock m e r0 hrun hr0 slots hslots h1 d).1

/-- **At most one token per cell, at every moment**: `bar` maps tokens
injectively to confirmed slots, and each cell confirms exactly one
slot.  So the machine's alternation capacity is bounded by the number
of cells, for all time. -/
theorem tokens_le_cells (slots : List Nat) (hnd : slots.Nodup)
    (cells : List Nat) (hcells : ∀ s, m.cellOf s ∈ cells) (k : Nat) :
    (tokenEnds m e r0 slots k).length ≤ cells.length := by
  have hinj : ∀ x ∈ tokenEnds m e r0 slots k,
      ∀ y ∈ tokenEnds m e r0 slots k,
      m.cellOf (m.bar x) = m.cellOf (m.bar y) → x = y := by
    intro x hx y hy hc
    rw [tokenEnds, List.mem_filter] at hx hy
    have hxT := (of_decide_eq_true hx.2).2
    have hyT := (of_decide_eq_true hy.2).2
    unfold Confirmed at hxT hyT
    rw [hc] at hxT
    have hbar : m.bar x = m.bar y := by rw [hxT] at hyT; exact hyT
    have := congrArg m.bar hbar
    rwa [m.bar_invol, m.bar_invol] at this
  have hndm := nodup_map_on hinj (nodup_filter _ hnd)
  have hmem : ∀ v ∈ (tokenEnds m e r0 slots k).map
      (fun s => m.cellOf (m.bar s)), v ∈ cells := by
    intro v hv
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hv
    exact hcells _
  have hle := nodup_subset_length hndm hmem
  rwa [List.length_map] at hle

end Echo
