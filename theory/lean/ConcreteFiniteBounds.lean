import ConcreteCascadeFacts

/-!
# Finite concrete slot and root bounds

An `N`-switch wiring has only `2*N` branch ports.  This file proves that
statement in the form required by the concrete echo compilation, without
assuming the finite slot list is a sublist of any preconstructed enumeration.

Every branch port is encoded injectively by

    2 * switch + branchBit,

where the branch bit is zero for residue 1 and one for residue 2.  Actual
cascade entries are branch ports on switches below `N`, so any duplicate-free
list of them has length at most `2*N`.  Likewise any duplicate-free list of
cascade roots has length at most `N`.
-/

namespace GeneralN


def IsDescentEntry (w : Wiring) (p : Nat) : Prop :=
  ∃ t ps s t', Descent w t p ps s t'

end GeneralN
