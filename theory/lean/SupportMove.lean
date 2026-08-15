import SupportBound

/-!
# What a support-preserving productive step does

The monotone-support theorem says jump edges can disappear but never return.
This file identifies the local dynamics when an edge does *not* disappear.

A confirmed endpoint is a cell's selected register slot.  A jump edge is
`Full` when both endpoints are confirmed.  If a productive write replaces an
old register by an arrival on a genuinely different jump edge, and the old
edge remains occupied afterwards, then the old edge was Full before the step
and the arrival edge is Full afterwards.  In other words, inside a fixed
support epoch a productive non-lobe move transfers the redundancy from one
edge to an adjacent edge.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Two slots represent the same jump edge. -/
def SameEdge (s t : Nat) : Prop := t = s ∨ t = m.bar s
end Echo
