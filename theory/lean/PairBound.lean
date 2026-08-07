import ReplayFacts

/-!
# Consecutive-pair accounting

A deliberately weaker route to a subexponential bound.  If the consecutive
entry pairs `(e k, e (k+1))` do not repeat inside a phase, then that phase has
at most `#slots^2` transitions.  Thus pair-uniqueness separately on the
transient and the eventual cycle would already give a polynomial bound.

The accounting below is unconditional; the structural task is solely to prove
pair-uniqueness for those two phases.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Encode a consecutive pair as a two-element list, avoiding any numerical
assumption on slot labels. -/
def pairTag (k : Nat) : List Nat := [e k, e (k+1)]

/-- All ordered pairs drawn from a finite slot universe. -/
def pairUniverse (slots : List Nat) : List (List Nat) :=
  slots.flatMap (fun a => slots.map (fun b => [a,b]))

private theorem nodup_subset_length_pair {l S : List (List Nat)}
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ S) : l.length ≤ S.length := by
  induction l generalizing S with
  | nil => exact Nat.zero_le _
  | cons x t ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ t, y ∈ S.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      have hlen : (S.erase x).length = S.length - 1 :=
        List.length_erase_of_mem hx
      rw [hlen] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

private theorem pairRect_length (xs ys : List Nat) :
    (xs.flatMap (fun a => ys.map (fun b => [a,b]))).length
      = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons a t ih =>
      simp [ih, Nat.add_mul]

private theorem pairUniverse_length (slots : List Nat) :
    (pairUniverse slots).length = slots.length * slots.length := by
  exact pairRect_length slots slots

/-- **Quadratic pair bound.** Any list of transition times with pairwise
 distinct consecutive entry pairs has length at most `#slots^2`, provided all
 entries of the run lie in `slots`. -/
theorem quadratic_pair_bound
    (slots : List Nat) (hslots : ∀ k, e k ∈ slots)
    (ks : List Nat) (hnd : (ks.map (pairTag e)).Nodup) :
    ks.length ≤ slots.length * slots.length := by
  have hmem : ∀ p ∈ ks.map (pairTag e), p ∈ pairUniverse slots := by
    intro p hp
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
    unfold pairTag pairUniverse
    apply List.mem_flatMap.mpr
    refine ⟨e k, hslots k, ?_⟩
    exact List.mem_map.mpr ⟨e (k+1), hslots (k+1), rfl⟩
  have hle := nodup_subset_length_pair hnd hmem
  rw [List.length_map, pairUniverse_length] at hle
  exact hle

end Echo
