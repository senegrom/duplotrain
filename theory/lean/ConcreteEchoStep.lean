import ConcreteEchoMachine

/-!
# The concrete last-writer echo step

Let `f` be the most recent ascent entry of one root tree.  After any finite
sequence of ascents of different roots, the pins laid by `f` remain intact.
Facing that tree's root therefore retraces the old cascade and exits at the
jump partner `wireBar f`.

The second theorem places this retrace immediately after a current ascent of
the mouth-partner tree.  It is the physical counterpart of
`Echo.return_jump`.
-/

namespace GeneralN

/-- A canonical free entry has the reverse branch-edge link required by
`retrace`. -/
theorem canonicalEchoSlot_reverse_link
    {w : Wiring} {f : Nat}
    (hf : IsCanonicalEchoSlot w f) :
    w.link (wireBar w f) = some f := by
  exact w.symm _ _ hf.2.2.1

end GeneralN
