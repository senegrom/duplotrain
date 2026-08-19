import RepeatedNoveltyDecomposition

/-!
# What reuse of a discarded curve port really forces

`ReusedNovelStrictShrinkPortForcesReplay` asks for a *global* tongue-vector
replay when two strict self-shrinks discard the same physical curve port.
The local curve argument does not, by itself, freeze switches outside the
discarded component.  This file therefore proves the strongest raw
consequence available before any such global-freezing theorem is supplied.

If a port is absent immediately after one shrink and belongs to the train
curve again before a later shrink, there is a first step restoring that
port.  That step is necessarily a productive non-self pivot and hence a
strict curve-growth event.  Its state contribution has an exhaustive raw
trichotomy:

* it is the first productive write of its switch;
* its post-vector already occurred earlier; or
* it is an earlier repeated-writer novelty.

The final section makes the global-state issue explicit.  If a later vector
does not replay the first-restoration vector, some represented coordinate
which differs between them has a named productive writer in the intervening
raw interval.  Thus outside activity is not silently assumed away.

Everything here is general in `N` and stated over `Wiring`/`stepN`.  The file
does **not** assert `ReusedNovelStrictShrinkPortForcesReplay` or `StateLaw`.
-/

namespace GeneralN

/-! ## First restoration of one discarded physical port -/

/-- Every prefix of a successful raw run is successful. -/
private theorem prefix_isSome_of_later_isSome
    {w : Wiring} {start : Nat × Tongues} {d K : Nat}
    (hd : d ≤ K) (hK : (stepN w K start).isSome) :
    (stepN w d start).isSome := by
  obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hK
  let rest := K - d
  have hsplit : K = d + rest := by
    dsimp [rest]
    omega
  rw [hsplit, stepN_add] at hfinish
  cases hprefix : stepN w d start with
  | none => simp [hprefix] at hfinish
  | some middle => simp

/-- If coordinate `C` is never productively written on a live half-open
interval, its tongue is unchanged across that interval. -/
private theorem tongue_eq_of_no_writer_interval_reuse
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start finish : Nat × Tongues} {first span : Nat}
    (hfinish : stepN w (first + span) start = some finish)
    (hno : ∀ t, first ≤ t → t < first + span →
      RawProductiveAt w N start t → rawWriterAt w start t ≠ C) :
    (tonguesAt w start (first + span)) C =
      (tonguesAt w start first) C := by
  induction span generalizing finish with
  | zero => simp
  | succ n ih =>
      have hprefixSome : (stepN w (first + n) start).isSome :=
        prefix_isSome_of_later_isSome
          (d := first + n) (K := first + n + 1) (by omega) (by
          have harith : first + (n + 1) = first + n + 1 := by omega
          rw [← harith, hfinish]
          simp)
      obtain ⟨middle, hmiddle⟩ := Option.isSome_iff_exists.mp hprefixSome
      have hprev := ih hmiddle
        (fun t hfirst hbound hprod => hno t hfirst (by omega) hprod)
      have hlive : (stepN w (first + n + 1) start).isSome := by
        have harith : first + (n + 1) = first + n + 1 := by omega
        rw [← harith, hfinish]
        simp
      obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
        live_successor_configs hlive
      have hcurEq : cur = middle := by
        exact (Option.some.inj (hmiddle.symm.trans hcur)).symm
      subst cur
      have hfinish' : stepN w (first + n + 1) start = some finish := by
        have harith : first + (n + 1) = first + n + 1 := by omega
        rwa [← harith]
      have hnextEq : next = finish := by
        exact Option.some.inj (hnext.symm.trans hfinish')
      subst next
      have hbit : finish.2 C = middle.2 C := by
        apply Classical.byContradiction
        intro hchange
        obtain ⟨hprod, hwriter⟩ :=
          raw_tongue_change_is_productive_writer
            hC hmiddle hfinish' hstep hchange
        exact hno (first + n) (by omega) (by omega) hprod hwriter
      calc
        (tonguesAt w start (first + (n + 1))) C = finish.2 C := by
          simp [tonguesAt, hfinish]
        _ = middle.2 C := hbit
        _ = (tonguesAt w start (first + n)) C := by
          simp [tonguesAt, hmiddle]
        _ = (tonguesAt w start first) C := hprev

/-- A changed represented coordinate over a live interval has a concrete
productive write by that coordinate's switch in the interval. -/
theorem changed_coordinate_has_writer_between
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start finish : Nat × Tongues} {first span : Nat}
    (hfinish : stepN w (first + span) start = some finish)
    (hchange : (tonguesAt w start (first + span)) C ≠
      (tonguesAt w start first) C) :
    ∃ t, first ≤ t ∧ t < first + span ∧
      RawProductiveAt w N start t ∧ rawWriterAt w start t = C := by
  apply Classical.byContradiction
  intro hnone
  have hstable := tongue_eq_of_no_writer_interval_reuse hC hfinish
    (fun t hlo hhi hprod => by
      intro hwriter
      exact hnone ⟨t, hlo, hhi, hprod, hwriter⟩)
  exact hchange hstable

end GeneralN
