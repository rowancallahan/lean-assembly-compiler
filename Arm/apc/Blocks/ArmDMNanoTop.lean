/- **The nano native AArch64 compiler (`compileNano`: C's front end and Gen, then the J → AArch64 translator
`C.e64` of Nano/Codegen/JArm.lean, all in nano) on DeepMind's AArch64 model**, against `Proven.Top.armDM` as
`CompileCorrectLoaded` / `CompileRunsLoaded` like `C_correct_armDM` (ArmDMTop.lean), from the generic
`C_correct_nano` / `C_runs_nano` (Nano/Main/NativeNano.lean) and `a64DMN`.  Premise left: `StepOK` (the 21 per-atom
facts of the translator, Nano/Run/JArmStep.lean). -/
import Nano.Main.NativeNano
import Blocks.A64DMN
import Blocks.ArmDMTop
namespace Proven.Apc.Blocks
open Proven.Top Proven.Top.Alloc NanoMain

theorem C_correct_nano_armDM (S : JT.StepOK) :
    CompileCorrectLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable compileNano :=
  Eq.subst (motive := fun o => CompileCorrectLoaded (armDMWith o) ArmDMExecutable ArmDMWritable compileNano)
    (funext obs_spec) fun program compiled f eI eO a s call h1 h2 h3 hl h4 h5 =>
      C_correct_nano a64DMN S (by decide) program compiled f eI eO a s call h1 h2 h3 hl h4 h5

theorem C_runs_nano_armDM (S : JT.StepOK) :
    CompileRunsLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable compileNano :=
  Eq.subst (motive := fun o => CompileRunsLoaded (armDMWith o) ArmDMExecutable ArmDMWritable compileNano)
    (funext obs_spec) fun program compiled f eI eO a s call h1 h2 h3 hl h4 =>
      C_runs_nano a64DMN S (by decide) program compiled f eI eO a s call h1 h2 h3 hl h4

end Proven.Apc.Blocks
