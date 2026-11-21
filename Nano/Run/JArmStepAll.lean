/- `StepOK`: the 21 per-atom lemmas of the nano translator together (JArmStepA / B / C). -/
import Nano.Run.JArmStepA
import Nano.Run.JArmStepB
import Nano.Run.JArmStepC
namespace JT

/-- **every atom code of the nano translator agrees with the specification** -/
theorem stepOK : StepOK :=
  stepOK_of stepAt_1 stepAt_2 stepAt_3 stepAt_4 stepAt_5 stepAt_6 stepAt_7 stepAt_8 stepAt_9 stepAt_10 stepAt_11
    stepAt_12 stepAt_13 stepAt_14 stepAt_15 stepAt_16 stepAt_18 stepAt_19 stepAt_20 stepAt_21 stepAt_22

end JT
