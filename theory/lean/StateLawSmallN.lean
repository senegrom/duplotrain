import VectorCount
import TrackTrace

/-!
# The `2^N` ceiling and the small-`N` legs of the sharp state law

The symbolic theorems prove `f(N) = N + 4` wherever `N + 4` is the binding
side of `min(2^N, N + 4)`, that is for `N ≥ 3`.  This file completes the
`min` formula in the same `Wiring`/`stepN` model:

* `state_law_two_pow` — the finite-state ceiling: any duplicate-free list of
  sampled restricted tongue vectors has length at most `2^N`, for every
  wiring and every start.  (Restricted vectors are length-`N` boolean lists;
  their binary values are distinct naturals below `2^N`.)
* `state_law_lower_bound_zero/_one/_two` — the ceiling is attained below
  the symbolic family's reach: the empty layout stands on its one vector,
  a teardrop on one switch visits `2^1 = 2`, and the dogbone on two
  switches walks the full Gray square, `2^2 = 4`.
* `add_four_le_two_pow` — `N + 4 ≤ 2^N` from three switches on, so the
  `min` in the state law selects `N + 4` exactly where the symbolic
  family takes over.

Together with `state_law_N_add_four` and `state_law_lower_bound` this
closes `f(N) = min(2^N, N + 4)` for every `N ≥ 1`.  The witness runs are
finite and checked by kernel `decide`; no `native_decide` is used.
-/

namespace GeneralN

/-! ## Binary value of a restricted tongue vector -/

/-- Little-endian binary value of a boolean list. -/
def boolsToNat : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * boolsToNat rest

theorem boolsToNat_lt_two_pow_length :
    ∀ l : List Bool, boolsToNat l < 2 ^ l.length
  | [] => by simp [boolsToNat]
  | b :: rest => by
    have ih := boolsToNat_lt_two_pow_length rest
    simp only [boolsToNat, List.length_cons]
    cases b <;> simp <;> omega

theorem boolsToNat_cons_mod (b : Bool) (l : List Bool) :
    boolsToNat (b :: l) % 2 = if b then 1 else 0 := by
  show ((if b then 1 else 0) + 2 * boolsToNat l) % 2 = _
  rw [Nat.add_mul_mod_self_left]
  cases b <;> rfl

theorem boolsToNat_cons_div (b : Bool) (l : List Bool) :
    boolsToNat (b :: l) / 2 = boolsToNat l := by
  show ((if b then 1 else 0) + 2 * boolsToNat l) / 2 = _
  rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
  cases b <;> simp

/-- On lists of equal length, the binary value is injective. -/
theorem boolsToNat_inj :
    ∀ {l1 l2 : List Bool}, l1.length = l2.length →
      boolsToNat l1 = boolsToNat l2 → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | b1 :: r1, b2 :: r2, hlen, heq => by
    have hmod := boolsToNat_cons_mod b1 r1
    rw [heq, boolsToNat_cons_mod b2 r2] at hmod
    have hb : b1 = b2 := by
      cases b1 <;> cases b2 <;> simp_all
    have hdiv := boolsToNat_cons_div b1 r1
    rw [heq, boolsToNat_cons_div b2 r2] at hdiv
    have hlen' : r1.length = r2.length := by simpa using hlen
    rw [hb, boolsToNat_inj hlen' hdiv.symm]

/-- A duplicate-free list of equal-length boolean vectors stays
duplicate-free under the binary value. -/
theorem nodup_map_boolsToNat {N : Nat} :
    ∀ {ls : List (List Bool)}, (∀ l ∈ ls, l.length = N) → ls.Nodup →
      (ls.map boolsToNat).Nodup
  | [], _, _ => by simp
  | l :: rest, hlen, hnd => by
    rw [List.map_cons, List.nodup_cons]
    rw [List.nodup_cons] at hnd
    refine ⟨?_, nodup_map_boolsToNat
      (fun x hx => hlen x (List.mem_cons_of_mem _ hx)) hnd.2⟩
    intro hmem
    obtain ⟨l', hl', heq⟩ := List.mem_map.mp hmem
    have hl'l : l' = l :=
      boolsToNat_inj
        ((hlen l' (List.mem_cons_of_mem _ hl')).trans
          (hlen l List.mem_cons_self).symm) heq
    exact hnd.1 (hl'l ▸ hl')

/-! ## The finite-state ceiling -/

/-- **The `2^N` ceiling.**  Any duplicate-free list of sampled restricted
tongue vectors has length at most `2^N` — for every wiring, every start,
and with no liveness assumption. -/
theorem state_law_two_pow (w : Wiring) (N : Nat) (c0 : Nat × Tongues)
    (ks : List Nat)
    (hnd : (ks.map fun k =>
      VectorCount.restrict N (tonguesAt w c0 k)).Nodup) :
    ks.length ≤ 2 ^ N := by
  have hlenAll : ∀ l ∈ ks.map fun k =>
      VectorCount.restrict N (tonguesAt w c0 k), l.length = N := by
    intro l hl
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hl
    simp [VectorCount.restrict]
  have hndN := nodup_map_boolsToNat hlenAll hnd
  have hltAll : ∀ x ∈ (ks.map fun k =>
      VectorCount.restrict N (tonguesAt w c0 k)).map boolsToNat,
      x < 2 ^ N := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    have hlt := boolsToNat_lt_two_pow_length l
    rwa [hlenAll l hl] at hlt
  have hcount := nodup_nat_lt_length hndN hltAll
  simpa using hcount

/-- `N + 4 ≤ 2^N` from three switches on: the `min` selects `N + 4`. -/
theorem add_four_le_two_pow : ∀ {N : Nat}, 3 ≤ N → N + 4 ≤ 2 ^ N
  | 0, h | 1, h | 2, h => by omega
  | 3, _ => by omega
  | n + 4, _ => by
    have ih := add_four_le_two_pow (N := n + 3) (by omega)
    rw [Nat.pow_succ]
    omega

/-! ## The empty layout: `2^0 = 1` state on zero switches -/

/-- The layout with no track at all. -/
def emptyWiring : Wiring := ⟨fun _ => none, by intro p q h; cases h⟩

/-- `f(0) ≥ 1`: the empty layout stands still on its single vector. -/
theorem state_law_lower_bound_zero :
    ∃ w : Wiring,
      (∀ p q, w.link p = some q → p < 3 * 0 ∧ q < 3 * 0) ∧
      ∃ (c0 : Nat × Tongues) (ks : List Nat),
        (∀ k ∈ ks, (stepN w k c0).isSome) ∧
        (ks.map fun k =>
          VectorCount.restrict 0 (tonguesAt w c0 k)).Nodup ∧
        ks.length = 2 ^ 0 := by
  refine ⟨emptyWiring, ?_, (0, fun _ => false), [0],
    by decide, by decide, by decide⟩
  intro p q h
  cases h

/-! ## The teardrop: `2^1 = 2` states on one switch -/

/-- One switch, stem linked to its own right branch, left branch capped. -/
def teardropLink : Nat → Option Nat
  | 0 => some 2
  | 2 => some 0
  | _ => none

/-- The teardrop's edges, exhaustively. -/
theorem teardropLink_cases (p q : Nat) (h : teardropLink p = some q) :
    (p, q) = (0, 2) ∨ (p, q) = (2, 0) := by
  match p, h with
  | 0, h => cases h; decide
  | 1, h => cases h
  | 2, h => cases h; decide
  | _ + 3, h => cases h

theorem teardrop_symm :
    ∀ p q, teardropLink p = some q → teardropLink q = some p := by
  intro p q h
  rcases teardropLink_cases p q h with h' | h' <;> cases h' <;> rfl

def teardropWiring : Wiring := ⟨teardropLink, teardrop_symm⟩

/-- `f(1) ≥ 2`: the teardrop flips its own switch on the first passage. -/
theorem state_law_lower_bound_one :
    ∃ w : Wiring,
      (∀ p q, w.link p = some q → p < 3 * 1 ∧ q < 3 * 1) ∧
      ∃ (c0 : Nat × Tongues) (ks : List Nat),
        (∀ k ∈ ks, (stepN w k c0).isSome) ∧
        (ks.map fun k =>
          VectorCount.restrict 1 (tonguesAt w c0 k)).Nodup ∧
        ks.length = 2 ^ 1 := by
  refine ⟨teardropWiring, ?_, (2, fun _ => false), [0, 1],
    by decide, by decide, by decide⟩
  intro p q h
  rcases teardropLink_cases p q h with h' | h' <;> cases h' <;> decide

/-! ## The dogbone: `2^2 = 4` states on two switches -/

/-- Two switches: a loop on switch 0's branches, a loop on switch 1's
branches, and a bar between the stems. -/
def dogboneLink : Nat → Option Nat
  | 0 => some 3
  | 3 => some 0
  | 1 => some 2
  | 2 => some 1
  | 4 => some 5
  | 5 => some 4
  | _ => none

/-- The dogbone's edges, exhaustively. -/
theorem dogboneLink_cases (p q : Nat) (h : dogboneLink p = some q) :
    (p, q) = (0, 3) ∨ (p, q) = (3, 0) ∨ (p, q) = (1, 2) ∨
      (p, q) = (2, 1) ∨ (p, q) = (4, 5) ∨ (p, q) = (5, 4) := by
  match p, h with
  | 0, h => cases h; decide
  | 1, h => cases h; decide
  | 2, h => cases h; decide
  | 3, h => cases h; decide
  | 4, h => cases h; decide
  | 5, h => cases h; decide
  | _ + 6, h => cases h

theorem dogbone_symm :
    ∀ p q, dogboneLink p = some q → dogboneLink q = some p := by
  intro p q h
  rcases dogboneLink_cases p q h with h' | h' | h' | h' | h' | h' <;>
    cases h' <;> rfl

def dogboneWiring : Wiring := ⟨dogboneLink, dogbone_symm⟩

/-- `f(2) ≥ 4`: the dogbone walks the full Gray square
`FF → TF → TT → FT`, one tongue flip every second step. -/
theorem state_law_lower_bound_two :
    ∃ w : Wiring,
      (∀ p q, w.link p = some q → p < 3 * 2 ∧ q < 3 * 2) ∧
      ∃ (c0 : Nat × Tongues) (ks : List Nat),
        (∀ k ∈ ks, (stepN w k c0).isSome) ∧
        (ks.map fun k =>
          VectorCount.restrict 2 (tonguesAt w c0 k)).Nodup ∧
        ks.length = 2 ^ 2 := by
  refine ⟨dogboneWiring, ?_, (0, fun _ => false), [0, 2, 4, 6],
    by decide, by decide, by decide⟩
  intro p q h
  rcases dogboneLink_cases p q h with h' | h' | h' | h' | h' | h' <;>
    cases h' <;> decide

end GeneralN
