import TrackTrace

/-!
# Koizumi's curve-shrinking invariant

For a tongue state, the fixed external wiring and the selected internal
stem/branch pairs form an undirected graph of degree at most two.  This file
puts the local matching and pivot statements in the raw `GeneralN.Wiring`
language and isolates the finite descent used by Koizumi's train-free-curve
argument.

The file deliberately does **not** claim the sharp transient `N + 4` state
law.  The missing bridge is dynamic: extracting a tracked train-free curve
after every relevant raw pivot, including the self-pivot nesting case.
-/

namespace GeneralN

/-- The branch selected by switch `C` in tongue state `u`. -/
def curveSelectedBranch (u : Tongues) (C : Nat) : Nat :=
  branchPort C (u C)

/-- The unique unselected branch, hence the internal endpoint at switch `C`. -/
def curveEndpointBranch (u : Tongues) (C : Nat) : Nat :=
  branchPort C (!(u C))

/-- The selected internal stem/branch matching.  External track edges remain
in `Wiring.link`; their union is Koizumi's curve graph. -/
def selectedInternalMate (u : Tongues) (p : Nat) : Option Nat :=
  if p % 3 = 0 then
    some (curveSelectedBranch u (p / 3))
  else if bval p = u (p / 3) then
    some (3 * (p / 3))
  else
    none

@[simp] theorem selectedInternalMate_stem (u : Tongues) (C : Nat) :
    selectedInternalMate u (3 * C) = some (curveSelectedBranch u C) := by
  simp [selectedInternalMate, curveSelectedBranch]

@[simp] theorem selectedInternalMate_selected (u : Tongues) (C : Nat) :
    selectedInternalMate u (curveSelectedBranch u C) = some (3 * C) := by
  cases h : u C
  · have hdiv : (3 * C + 1) / 3 = C := by omega
    simp [selectedInternalMate, curveSelectedBranch, branchPort, bval, h,
      hdiv]
  · have hdiv : (3 * C + 2) / 3 = C := by omega
    simp [selectedInternalMate, curveSelectedBranch, branchPort, bval, h,
      hdiv]

@[simp] theorem selectedInternalMate_endpoint (u : Tongues) (C : Nat) :
    selectedInternalMate u (curveEndpointBranch u C) = none := by
  cases h : u C
  · have hdiv : (3 * C + 2) / 3 = C := by omega
    simp [selectedInternalMate, curveEndpointBranch, branchPort, bval, h,
      hdiv]
  · have hdiv : (3 * C + 1) / 3 = C := by omega
    simp [selectedInternalMate, curveEndpointBranch, branchPort, bval, h,
      hdiv]


structure CurveEndpointPivot (u : Tongues) (C : Nat) : Prop where
  oldStem : selectedInternalMate u (3 * C) =
    some (curveSelectedBranch u C)
  oldEndpoint : selectedInternalMate u (curveEndpointBranch u C) = none
  newStem : selectedInternalMate (flipAt u C) (3 * C) =
    some (curveEndpointBranch u C)
  newEndpoint : selectedInternalMate (flipAt u C)
    (curveSelectedBranch u C) = none
  away : ∀ p, p / 3 ≠ C →
    selectedInternalMate (flipAt u C) p = selectedInternalMate u p

/-- Flipping one tongue performs exactly Koizumi's endpoint pivot: the old
endpoint is attached to the stem, the old selected branch becomes the new
endpoint, and every other switch's internal matching is unchanged. -/
theorem flipAt_is_curve_endpoint_pivot (u : Tongues) (C : Nat) :
    CurveEndpointPivot u C := by
  refine {
    oldStem := selectedInternalMate_stem u C
    oldEndpoint := selectedInternalMate_endpoint u C
    newStem := ?_
    newEndpoint := ?_
    away := ?_
  }
  · cases h : u C
    · simp [selectedInternalMate, curveEndpointBranch, curveSelectedBranch,
        branchPort, flipAt, h]
    · simp [selectedInternalMate, curveEndpointBranch, curveSelectedBranch,
        branchPort, flipAt, h]
  · cases h : u C
    · have hdiv : (3 * C + 1) / 3 = C := by omega
      simp [selectedInternalMate, curveSelectedBranch, branchPort, bval,
        flipAt, h, hdiv]
    · have hdiv : (3 * C + 2) / 3 = C := by omega
      simp [selectedInternalMate, curveSelectedBranch, branchPort, bval,
        flipAt, h, hdiv]
  · intro p hp
    simp [selectedInternalMate, curveSelectedBranch, flipAt, hp]

/-! ## The finite strict-subcurve descent -/

/-- A tracked endpoint curve represented by the switches encountered along
its arc.  `Nodup` is the simple-curve condition. -/
structure TrackedEndpointCurve (N : Nat) where
  switches : List Nat
  simple : switches.Nodup
  inRange : ∀ C ∈ switches, C < N

theorem TrackedEndpointCurve.length_le (D : TrackedEndpointCurve N) :
    D.switches.length ≤ N :=
  nodup_nat_lt_length D.simple D.inRange

end GeneralN
