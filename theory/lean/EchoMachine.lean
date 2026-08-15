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

theorem nodup_subset_length {α : Type} [BEq α] [LawfulBEq α] :
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

/-! ### The pedigree theorems: the machine can never invent values

Where can a register value come from?  `token_pedigree`: every live
token traces back — it was already a token at any chosen base time, or
its slot has held its own cell's register somewhere in between (tokens
are re-emitted only at evicted registers, and dead edges never
revive).  `future_register`: consequently every value a cell's
register will EVER hold is either its value now or the slot of a token
alive now.  The token profile at any moment spans the machine's entire
future state space, and as tokens die the reachable space only
collapses.  Counted: σ(C) ≤ 1 + #tokens(C) per cell
(`repertoire_count`), and fresh values — values some cell has not held
at base time — are paid for one-for-one by base-time tokens
(`fresh_values_le_tokens`), hence by `tokens_le_cells` at most
`#cells` of them ever appear, in total, across all cells and all
future time. -/


theorem change_has_productive {c i : Nat} :
    ∀ d, reg m e r0 (i+d) c ≠ reg m e r0 i c →
      ∃ t, i ≤ t ∧ t < i + d ∧ ProductiveStep m e r0 t ∧
        m.cellOf (e (t+1)) = c := by
  intro d
  induction d with
  | zero => intro h; exact absurd rfl h
  | succ n ih =>
      intro h
      have h' : reg m e r0 (i+n+1) c ≠ reg m e r0 i c := h
      by_cases hc : m.cellOf (e (i+n+1)) = c
      · by_cases hp : ProductiveStep m e r0 (i+n)
        · exact ⟨i+n, Nat.le_add_right _ _, by omega, hp, hc⟩
        · have heq : e (i+n+1)
              = reg m e r0 (i+n) (m.cellOf (e (i+n+1))) := by
            by_cases hq : e (i+n+1)
                = reg m e r0 (i+n) (m.cellOf (e (i+n+1)))
            · exact hq
            · exact absurd hq hp
          rw [unproductive_stall m e r0 (i+n) heq c] at h'
          obtain ⟨t, h1, h2, h3, h4⟩ := ih h'
          exact ⟨t, h1, by omega, h3, h4⟩
      · rw [reg_skip m e r0 hc] at h'
        obtain ⟨t, h1, h2, h3, h4⟩ := ih h'
        exact ⟨t, h1, by omega, h3, h4⟩

/-- Arbitrary-time form: a register that differs at `i ≤ j` was moved
by a productive write of its own cell strictly inside `[i, j)`. -/
theorem change_has_productive_le {c i j : Nat} (hij : i ≤ j)
    (h : reg m e r0 j c ≠ reg m e r0 i c) :
    ∃ t, i ≤ t ∧ t < j ∧ ProductiveStep m e r0 t ∧
      m.cellOf (e (t+1)) = c := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  exact change_has_productive m e r0 d h


theorem quiet_reg {i : Nat} :
    ∀ d, (∀ t, i ≤ t → t < i + d → ¬ ProductiveStep m e r0 t) →
      ∀ c, reg m e r0 (i + d) c = reg m e r0 i c := by
  intro d
  induction d with
  | zero => intro _ c; rfl
  | succ n ih =>
      intro hq c
      have hun : e (i+n+1) = reg m e r0 (i+n) (m.cellOf (e (i+n+1))) := by
        by_cases hq2 : e (i+n+1) = reg m e r0 (i+n) (m.cellOf (e (i+n+1)))
        · exact hq2
        · exact absurd hq2 (hq (i+n) (Nat.le_add_right _ _) (by omega))
      calc reg m e r0 (i + (n+1)) c
          = reg m e r0 (i+n) c := unproductive_stall m e r0 (i+n) hun c
        _ = reg m e r0 i c := ih (fun t h1 h2 => hq t h1 (by omega)) c

/-- Under the (≤1, ≤1, 0, …) token shape at `K`, every snapshot from
`K` on is one of four explicit candidates: frozen cells keep their
`K`-registers and the two steering cells each hold their `K`-register
or their single token. -/
theorem token_shape_tail (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (slots : List Nat) (hslots : ∀ j, e j ∈ slots)
    {K C1 C2 t1 t2 : Nat}
    (h1 : ∀ s ∈ cellTokens m e r0 slots C1 K, s = t1)
    (h2 : ∀ s ∈ cellTokens m e r0 slots C2 K, s = t2)
    (h0 : ∀ C, C ≠ C1 → C ≠ C2 → ∀ s, s ∉ cellTokens m e r0 slots C K)
    (cells : List Nat) :
    ∀ j, K ≤ j → snap m e r0 cells j ∈
      [cells.map (fun c => if c = C1 then reg m e r0 K C1
          else if c = C2 then reg m e r0 K C2 else reg m e r0 K c),
       cells.map (fun c => if c = C1 then reg m e r0 K C1
          else if c = C2 then t2 else reg m e r0 K c),
       cells.map (fun c => if c = C1 then t1
          else if c = C2 then reg m e r0 K C2 else reg m e r0 K c),
       cells.map (fun c => if c = C1 then t1
          else if c = C2 then t2 else reg m e r0 K c)] := by
  intro j hj
  have hfrozen : ∀ c, c ≠ C1 → c ≠ C2 →
      reg m e r0 j c = reg m e r0 K c := by
    intro c hc1 hc2
    obtain ⟨d, hd⟩ : ∃ d, j = K + d := ⟨j - K, by omega⟩
    rw [hd]
    exact (freezeout m e r0 hrun hr0 slots hslots (h0 c hc1 hc2) d).2
  have hcand : snap m e r0 cells j
      = cells.map (fun c => if c = C1 then reg m e r0 j C1
          else if c = C2 then reg m e r0 j C2
          else reg m e r0 K c) := by
    unfold snap
    apply map_congr'
    intro c _
    by_cases hc1 : c = C1
    · rw [if_pos hc1, hc1]
    · rw [if_neg hc1]
      by_cases hc2 : c = C2
      · rw [if_pos hc2, hc2]
      · rw [if_neg hc2]
        exact hfrozen c hc1 hc2
  rw [hcand]
  have hL1 := singleton_lock_reg m e r0 hrun hr0 slots hslots h1 hj
  have hL2 := singleton_lock_reg m e r0 hrun hr0 slots hslots h2 hj
  rcases hL1 with ha | ha <;> rcases hL2 with hb | hb <;> rw [ha, hb]
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **The Gray tail.**  From any moment at which the token population
has the observed shape — at most one token in each of two cells, none
anywhere else — the machine visits at most **4** distinct register
snapshots, ever, on any cell support. -/
theorem gray_tail (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (slots : List Nat) (hslots : ∀ j, e j ∈ slots)
    {K C1 C2 t1 t2 : Nat}
    (h1 : ∀ s ∈ cellTokens m e r0 slots C1 K, s = t1)
    (h2 : ∀ s ∈ cellTokens m e r0 slots C2 K, s = t2)
    (h0 : ∀ C, C ≠ C1 → C ≠ C2 → ∀ s, s ∉ cellTokens m e r0 slots C K)
    (cells ks : List Nat)
    (hks : ∀ j ∈ ks, K ≤ j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ 4 := by
  have hle := nodup_subset_length hnd
    (fun v hv => by
      obtain ⟨j, hjks, rfl⟩ := List.mem_map.mp hv
      exact token_shape_tail m e r0 hrun hr0 slots hslots h1 h2 h0
        cells j (hks j hjks))
  rw [List.length_map] at hle
  exact hle

end Echo
