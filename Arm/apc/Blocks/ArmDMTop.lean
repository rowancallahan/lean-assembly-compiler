/- **The C compiler (C → RISC-V words → rv2arm) is correct on DeepMind's AArch64 model** (`armDM`), for start states
whose loader maps the code executable and the data blocks readable+writable (`JT.ArmLoader XD WD`, a premise on the
start state; DeepMind's W^X permissions are not observable through `Spec`). From E's `C_correct_rv2arm` /
`C_runs_rv2arm` (Nano/V2Self/Proof/Main/ArmTop.lean) and `a64DM`. Interim target: the final theorem is on Sail. -/
import Nano.V2Self.Proof.Main.ArmTop
import Blocks.A64Inst
namespace Proven.Apc.Blocks
open Proven.Top NanoMain

theorem C_correct_armDM : CompileCorrectP armDM (JT.ArmLoader XD WD) (compileOn ArmRA.rv2arm) :=
  C_correct_rv2arm a64DM (by decide)

theorem C_runs_armDM : CompileRunsP armDM (JT.ArmLoader XD WD) (compileOn ArmRA.rv2arm) :=
  C_runs_rv2arm a64DM (by decide)

end Proven.Apc.Blocks
