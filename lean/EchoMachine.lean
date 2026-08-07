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

end Echo
