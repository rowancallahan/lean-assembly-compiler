/- **The nano native AArch64 compiler on DeepMind's AArch64 model, with no premise left**: `C_correct_nano_armDM` /
`C_runs_nano_armDM` (ArmDMNanoTop.lean) with `JT.stepOK`.  Axioms: Blocks/AxiomsDMRelease.lean. -/
import Blocks.ArmDMNanoTop
import Nano.Main.NativeRelease
namespace Proven.Apc.Blocks
open Proven.Top Proven.Top.Alloc NanoMain

theorem C_correct_native_release_armDM :
    CompileCorrectLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable compileNano := C_correct_nano_armDM JT.stepOK

theorem C_runs_native_release_armDM :
    CompileRunsLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable compileNano := C_runs_nano_armDM JT.stepOK

end Proven.Apc.Blocks
