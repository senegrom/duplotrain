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

end Echo
