import TrackEndpointMatching
import ManufacturedPairNovelty

/-!
# Raw repeated-novelty decomposition

This file works directly over `GeneralN.Wiring` and `stepN`.  It isolates the
extra physical fact which is absent from an arbitrary word of bit flips:
every productive write to switch `C` leaves over the one fixed plain-track
edge `link (3*C)`.  Consequently all productive writes to the same switch
have the same post-write entry port.

The flip-label argument is formalised in two stages.

* A last-previous occurrence of a repeated novel writer cannot close with a
  productive-free interior.  Two flips of the same switch would restore the
  complete restricted tongue vector to the vector immediately before the
  first flip, contradicting novelty.
* Choose the last productive event in that interior.  Its writer is a
  different switch and its next entry is fixed by that switch's stem edge.
  Looking backwards to that rerouter's last previous write gives exactly
  three possibilities: a genuinely first writer, a crossing writer frame,
  or a strictly nested writer frame.

Thus the artificial word `1,...,N,1,...,N` cannot remain an unstructured
source of `N` repeated novelties: after its first repeated event, each next
rerouter exposes a crossing frame.  The remaining global theorem is to map
the raw crossing/nesting alternatives to the already proved restoration and
reflector novelty bounds.  No finite-`N` exhaustion is used here.
-/

namespace GeneralN


/-- If a live raw step is not productive, its represented tongue vector is
unchanged. -/
theorem restrictedTonguesAt_succ_eq_of_not_productive
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k+1) start).isSome)
    (hquiet : ¬ RawProductiveAt w N start k) :
    restrictedTonguesAt w N start (k+1) =
      restrictedTonguesAt w N start k := by
  apply Classical.byContradiction
  intro hne
  exact hquiet ⟨hlive, hne⟩

/-- Every prefix of a successful finite run is successful. -/
theorem restrictedTonguesAt_eq_of_quiet_interval
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {first span : Nat}
    (hfinish : stepN w (first + span) start = some finish)
    (hquiet : ∀ j, first ≤ j → j < first + span →
      ¬ RawProductiveAt w N start j) :
    restrictedTonguesAt w N start (first + span) =
      restrictedTonguesAt w N start first := by
  induction span generalizing finish with
  | zero => simp
  | succ n ih =>
      have hprefix : ∃ middle,
          stepN w (first + n) start = some middle :=
        stepN_prefix_some (by omega) hfinish
      obtain ⟨middle, hmiddle⟩ := hprefix
      have hprev := ih hmiddle
        (fun j hfirst hj => hquiet j hfirst (by omega))
      have hlive : (stepN w (first + n + 1) start).isSome := by
        have harith : first + (n+1) = first + n + 1 := by omega
        rw [← harith, hfinish]
        simp
      have hstep := restrictedTonguesAt_succ_eq_of_not_productive
        hlive (hquiet (first+n) (by omega) (by omega))
      have harith : first + (n+1) = first+n+1 := by omega
      rw [harith]
      exact hstep.trans hprev

/-- Restriction commutes with flipping a represented coordinate, even when
the two full tongue functions may differ outside the first `N` switches. -/
theorem restrict_flipAt_congr
    {N C : Nat} {u v : Tongues}
    (h : VectorCount.restrict N u = VectorCount.restrict N v) :
    VectorCount.restrict N (flipAt u C) =
      VectorCount.restrict N (flipAt v C) := by
  unfold VectorCount.restrict
  apply List.map_congr_left
  intro j hj
  have hjN : j < N := List.mem_range.mp hj
  have huv : u j = v j := restrict_eq_apply h hjN
  unfold flipAt
  by_cases hjC : j = C
  · subst j
    simp [huv]
  · simp [hjC, huv]

/-- A productive raw step flips exactly the represented bit named by its
writer. -/
theorem rawProductiveAt_restricted_flip
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    restrictedTonguesAt w N start (k+1) =
      VectorCount.restrict N
        (flipAt (tonguesAt w start k) (rawWriterAt w start k)) := by
  obtain ⟨cur, next, C, hC, hcur, hnext, _hstep,
      _hexit, hflip⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  subst C
  simp [restrictedTonguesAt, tonguesAt, hcur, hnext, hflip]

end GeneralN
