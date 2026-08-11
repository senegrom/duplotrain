import CompleteRepairConstant

namespace GeneralN

example {w : Wiring} {g e : Nat}
    (R : ManufacturedStayReflector w g e) :
    (ManufacturedReflector.stay R).activatedState = R.returnState := by
  rfl

example {w : Wiring} {g e : Nat}
    (R : ManufacturedStayReflector w g e) :
    (ManufacturedReflector.stay R).preReturn = (R.arm, R.returnState) := by
  rfl

example {w : Wiring} {g e : Nat}
    (R : ManufacturedStayReflector w g e) (state : Tongues) :
    (ManufacturedReflector.stay R).toSupported.action.apply state = state := by
  rfl

example {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e) :
    (ManufacturedReflector.flip R).activatedState = R.afterReturn := by
  rfl

example {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e) :
    (ManufacturedReflector.flip R).preReturn =
      (R.secondArm, R.returnState) := by
  rfl

example {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e) (state : Tongues) :
    (ManufacturedReflector.flip R).toSupported.action.apply state =
      flipAt state R.actionSwitch := by
  rfl

end GeneralN
