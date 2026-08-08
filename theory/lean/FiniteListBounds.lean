/-!
# Shared finite-list counting helpers

Small generic lemmas used by the concrete overwrite bridge.  They are kept
public because several later modules need the same injection and fibre-sum
arguments.
-/

namespace FiniteListBounds

/-- If equality under `f` forces equality under `g` on a finite list, then
Nodupness of the `g`-image implies Nodupness of the `f`-image. -/
theorem nodup_map_of_fibre
    {α β γ : Type} (xs : List α)
    (f : α → β) (g : α → γ)
    (hfibre : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → g x = g y)
    (hnd : (xs.map g).Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      constructor
      · intro hmem
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
        have hgy : g x = g y :=
          hfibre x List.mem_cons_self y
            (List.mem_cons_of_mem _ hy) hfy.symm
        exact hnd.1 (List.mem_map.mpr ⟨y, hy, hgy.symm⟩)
      · exact ih
          (fun a ha b hb => hfibre a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb))
          hnd.2

/-- A finite sum is at most the list length times a common pointwise bound. -/
theorem sum_le_length_mul_bound
    (xs : List Nat) (B : Nat)
    (h : ∀ x ∈ xs, x ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hx := h x List.mem_cons_self
      have hr : ∀ y ∈ rest, y ≤ B := by
        intro y hy
        exact h y (List.mem_cons_of_mem _ hy)
      have hi := ih hr
      simp only [List.sum_cons, List.length_cons]
      calc
        x + rest.sum ≤ B + rest.length * B :=
          Nat.add_le_add hx hi
        _ = (rest.length + 1) * B := by
          simp [Nat.add_mul, Nat.add_comm]

end FiniteListBounds
