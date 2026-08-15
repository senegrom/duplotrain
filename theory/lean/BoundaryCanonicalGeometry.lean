import BoundaryDoubleDuplicate

/-!
# Geometry of the canonical productive boundary

At the canonical unchanged occurrence, the first manufactured flip
reflector's action switch is the initially written switch.  Its mouth is
therefore the source entry stem.  Symmetry of the entry edge then makes any
nonempty switch-simple runway return through its own first entry, contradicting
`PhysicalTrace.simple_last_exit_ne_first_entry`.

Thus the canonical runway is empty.  In particular, the two ends of the
source edge coincide and that edge is a literal self-link.  These are raw
physical consequences; they do not use a finite-instance argument.
-/

namespace GeneralN

/-- At the canonical unchanged occurrence, the manufactured mouth is exactly
the source entry stem. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_mouth_eq_entry
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    R.mouth = S.source.e := by
  have hk0 : S.source.k0 = R.actionSwitch :=
    O.switch_eq_action_of_before_length_eq_runway hcanonical
  have hstem := S.source.stem
  have hmouthStem := R.mouth_is_stem
  unfold ManufacturedFlipReflector.actionSwitch at hk0
  omega

/-- Canonical saturation leaves no runway before the first flip reflector.
Any nonempty runway would start at `g` and, by symmetry of the source entry
edge, have its last exit at the same port `g`, contradicting switch-simplicity.
-/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_runway_eq_nil
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    R.runway = [] := by
  have hmouth : R.mouth = S.source.e :=
    S.canonical_mouth_eq_entry R O hcanonical
  cases hrunway : R.runway with
  | nil => rfl
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have htrace := R.runwayTrace
      rw [hrunway] at htrace
      have hsimple : SwitchSimple ((p, x) :: rest) := by
        have hs := (ManufacturedReflector.flip R).runway_simple
        change SwitchSimple R.runway at hs
        rwa [hrunway] at hs
      have hfirst : p = S.source.g := by
        exact htrace.head_arrive.1.symm
      have hlast :
          w.link (lastPassageExit x rest) = some R.mouth :=
        htrace.last_link
      have hback :
          w.link R.mouth = some (lastPassageExit x rest) :=
        w.symm _ _ hlast
      have hentry : w.link R.mouth = some S.source.g := by
        simpa [hmouth] using S.source.entry
      have hfinal : lastPassageExit x rest = S.source.g := by
        rw [hentry] at hback
        exact (Option.some.inj hback).symm
      exact False.elim
        (htrace.simple_last_exit_ne_first_entry hsimple
          (hfinal.trans hfirst.symm))

/-- The canonical source is a literal self-linked stem: its two named ports
coincide, and the wiring pairs that port with itself. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_source_self_link
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    S.source.g = S.source.e /\
      w.link S.source.e = some S.source.e := by
  have hrunway := S.canonical_runway_eq_nil R O hcanonical
  have hmouth := S.canonical_mouth_eq_entry R O hcanonical
  have hsound := R.runwayTrace.sound
  rw [hrunway] at hsound
  have hconfig :
      (S.source.g, R.base) = (R.mouth, R.mouthState) := by
    simpa [stepN] using hsound
  have hge : S.source.g = S.source.e := by
    exact (congrArg Prod.fst hconfig).trans hmouth
  constructor
  · exact hge
  · simpa [hge] using S.source.entry

end GeneralN
