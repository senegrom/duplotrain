import SerialPairSupportContact
import OverlappingSerialWindows
import BABAInterlacementTail

/-!
# Canonical resolution of a changed-forward support contact

The support-contact reduction is geometric: one reflector's action switch
occurs on the other reflector's support. A changed-forward repair is the
dynamic form of that contact. This file places its changing passage at an
exact absolute raw time and then resolves that time against the six
consecutive repeated-writer novelties.

If the contact occurs by z5, it is either already paid by first-writer
history, is a literal replay, or is one of z0,...,z5. In the selected
case the open-frame decomposition gives either a first-writer interior
charge or an actual BABA interlacement. There is no compatibility
certificate or unproved continuation hypothesis in the statement.
-/

namespace GeneralN

/-- Membership in the canonical six-event window. -/
def RawSixSelectedTime
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    (k : Nat) : Prop :=
  k = R.z0 ∨ k = R.z1 ∨ k = R.z2 ∨
    k = R.z3 ∨ k = R.z4 ∨ k = R.z5

/-- A selected contact whose first parity-changing interior rerouter is a
globally first writer. This is the exact first-writer charge left by the
open-frame decomposition. -/
structure RawSelectedFirstCharge
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Type where
  contact : Nat
  selected : RawSixSelectedTime R contact
  event : RawRepeatedWriterNovelAt w N start contact
  left : Nat
  reroute : Nat
  outerFrame : RawLastWriterFrame w N start left contact
  reroute_productive : RawProductiveAt w N start reroute
  different_writers :
    rawWriterAt w start reroute ≠ rawWriterAt w start contact
  first_inside :
    ∀ j, left < j → j < reroute →
      RawProductiveAt w N start j →
      rawWriterAt w start j ≠ rawWriterAt w start reroute
  first_rerouter : RawFirstWriterAt w N start reroute

/-- A selected contact whose parity-changing interior rerouter has an older
writer. Its old frame crosses the selected contact's outer frame in literal
B A B A order. -/
structure RawSelectedBABA
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Type where
  contact : Nat
  selected : RawSixSelectedTime R contact
  event : RawRepeatedWriterNovelAt w N start contact
  prior : Nat
  second : Nat
  reroute : Nat
  crossing :
    RawBABAInterlacement w N start prior second reroute contact

/-- A changed-forward merge contains an exact productive contact in the
global raw run. The contact occurs during the fresh reflector's selected
route, not merely somewhere before its eventual periodic tail.

The proof extracts the plain-track edge after the protected passage from the
old reflector's physical trace. It then exposes the current and next raw
configurations and invokes the raw tongue-change theorem. -/
theorem ManufacturedReflector.ChangedForwardMerge.absolute_productive_contact
    {w : Wiring} {N g e shift : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.ChangedForwardMerge B)
    {start : Prod Nat Tongues}
    (hreach : stepN w shift start =
      some (g, B.activatedState)) :
    ∃ contact C,
      shift ≤ contact ∧
      contact + 1 ≤ shift + A.toSupported.travel ∧
      RawProductiveAt w N start contact ∧
      rawWriterAt w start contact = C := by
  obtain
      ⟨approach, p, x, suffix, u, v, _path, _old,
        oriented, _repaired, hsplit, happroach, hpaths,
        harrive, _hpath, _hold, _holdSwitch, hchanged,
        horiented, _horientedGroove, _horientedSwitch,
        hforward, _hrepair, _hrestored⟩ := hmerge
  rcases oriented with ⟨a, s⟩
  simp only at horiented hforward
  subst x
  obtain ⟨_hpBranch, hsEq, _hv, _hback⟩ :=
    changed_arrival_is_trailing harrive hchanged
  obtain ⟨before, after, hrouteSplit⟩ :=
    List.append_of_mem horiented
  have hroute := B.orientedRoute_trace u hpaths
  rw [hrouteSplit] at hroute
  obtain ⟨middle, _hbefore, hafter⟩ := hroute.split_append
  cases hafter with
  | @cons _ _ outside _ _ _ _ _ hmouth _ =>
      have hsBound : s < 3 * N := (hN s outside hmouth).1
      rw [hsEq] at hsBound
      have hC : p / 3 < N := by omega
      have hstep :
          step w (p, u) = some (outside, v) := by
        simp [step, harrive, hmouth]
      have hone :
          stepN w 1 (p, u) = some (outside, v) := by
        simpa [stepN] using hstep
      have hcur :
          stepN w (shift + approach.length) start =
            some (p, u) := by
        rw [stepN_add, hreach]
        exact happroach.sound
      have hnext :
          stepN w (shift + approach.length + 1) start =
            some (outside, v) := by
        rw [show shift + approach.length + 1 =
            shift + (approach.length + 1) by omega,
          stepN_add, hreach]
        simp only [Option.bind_some]
        rw [stepN_add, happroach.sound]
        exact hone
      have hraw :=
        raw_tongue_change_is_productive_writer
          hC hcur hnext hstep hchanged
      have hrouteLength :
          (A.orientedRoute B.activatedState).length =
            approach.length + 1 + suffix.length := by
        rw [hsplit]
        simp
        omega
      have hrouteLe :=
        A.orientedRoute_length_le_travel B.activatedState
      refine
        ⟨shift + approach.length, p / 3,
          Nat.le_add_right shift approach.length, ?_,
          hraw.1, hraw.2⟩
      omega

/-- Canonical resolution of the physical support contact.

Assume the complete fresh route containing a changed-forward support contact
finishes by z5+1. Then the exact contact has one of four unconditional
raw outcomes:

1. it is a first writer and its post-vector is in first-writer history;
2. its post-vector is a literal replay;
3. it is one of the six selected closes and pays a first-writer rerouter;
4. it is one of the six selected closes and contains a BABA crossing.

The last two alternatives retain the selected event itself. Thus a later
argument can spend the charge or consume the concrete crossing without
reconstructing the contact time. -/
theorem RawOverlappingFiveWindowReduction.changedForward_contact_resolution
    {w : Wiring} {N g e shift : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.ChangedForwardMerge B)
    (hreach : stepN w shift start =
      some (g, B.activatedState))
    (hbefore : shift + A.toSupported.travel ≤ R.z5 + 1) :
    (∃ contact,
      contact + 1 ≤ R.z5 + 1 ∧
      RawFirstWriterAt w N start contact ∧
      restrictedTonguesAt w N start (contact + 1) ∈
        rawFirstWriterHistory w N start (R.z5 + 1)) ∨
    (∃ contact,
      contact + 1 ≤ R.z5 + 1 ∧
      RawProductiveAt w N start contact ∧
      ¬ RawNovelAt w N start contact) ∨
    Nonempty (RawSelectedFirstCharge R) ∨
    Nonempty (RawSelectedBABA R) := by
  classical
  obtain ⟨contact, _C, _hshift, hcontactRoute,
      hproductive, _hwriter⟩ :=
    hmerge.absolute_productive_contact hN hreach
  have hcontactBound : contact + 1 ≤ R.z5 + 1 :=
    Nat.le_trans hcontactRoute hbefore
  have hcontactLe : contact ≤ R.z5 := by omega
  by_cases hfirst : RawFirstWriterAt w N start contact
  · apply Or.inl
    refine ⟨contact, hcontactBound, hfirst, ?_⟩
    unfold rawFirstWriterHistory
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨contact, ?_, rfl⟩
    exact mem_rawFirstWriterTimes_iff.mpr ⟨by omega, hfirst⟩
  · by_cases hnovel : RawNovelAt w N start contact
    · have Hevent : RawRepeatedWriterNovelAt w N start contact :=
        ⟨hproductive, hfirst, hnovel⟩
      have hselected : RawSixSelectedTime R contact := by
        simpa [RawSixSelectedTime] using
          R.repeated_novelty_at_most_z5 hcontactLe Hevent
      obtain ⟨left, reroute, outer, hreroute, hdiff,
          hfirstInside, shape⟩ :=
        Hevent.open_rerouting_decomposition hN
      cases shape with
      | fresh hfirstRerouter =>
          exact Or.inr (Or.inr (Or.inl ⟨{
            contact := contact
            selected := hselected
            event := Hevent
            left := left
            reroute := reroute
            outerFrame := outer
            reroute_productive := hreroute
            different_writers := hdiff
            first_inside := hfirstInside
            first_rerouter := hfirstRerouter
          }⟩))
      | @crossing prior inner order =>
          exact Or.inr (Or.inr (Or.inr ⟨{
            contact := contact
            selected := hselected
            event := Hevent
            prior := prior
            second := left
            reroute := reroute
            crossing := {
              prior_lt_second := order.1
              second_lt_reroute := order.2.1
              reroute_lt_third := order.2.2
              leftFrame := inner
              rightFrame := outer
              different_writers := hdiff
            }
          }⟩))
    · exact Or.inr (Or.inl
        ⟨contact, hcontactBound, hproductive, hnovel⟩)

end GeneralN
