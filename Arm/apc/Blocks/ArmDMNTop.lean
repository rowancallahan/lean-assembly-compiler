/- **The native AArch64 compile (`compileNative`: C's front end, then GenArm) on DeepMind's AArch64 model**, stated
against `Proven.Top.armDM` as `CompileCorrectLoaded` / `CompileRunsLoaded` like `C_correct_armDM` (ArmDMTop.lean), from
the generic `C_correct_native` / `C_runs_native` (Nano/Main/NativeTop.lean) and `a64DMN` (A64DMN.lean).  Still
parameterised by the bundle `NativeTemplatesOK armDM XD WD` (the template runs and the Gen/GenArm lockstep, M3). -/
import Nano.Main.NativeTop
import Blocks.A64DMN
import Blocks.ArmDMTop
namespace Proven.Apc.Blocks
open Proven.Top Proven.Top.Alloc NanoMain

theorem C_correct_native_armDM (H : NativeTemplatesOK armDM XD WD) :
    CompileCorrectLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable compileNative :=
  Eq.subst (motive := fun o => CompileCorrectLoaded (armDMWith o) ArmDMExecutable ArmDMWritable compileNative)
    (funext obs_spec) fun program compiled f eI eO a s call h1 h2 h3 hl h4 h5 =>
      C_correct_native a64DMN H (by decide) program compiled f eI eO a s call h1 h2 h3 hl h4 h5

theorem C_runs_native_armDM (H : NativeTemplatesOK armDM XD WD) :
    CompileRunsLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable compileNative :=
  Eq.subst (motive := fun o => CompileRunsLoaded (armDMWith o) ArmDMExecutable ArmDMWritable compileNative)
    (funext obs_spec) fun program compiled f eI eO a s call h1 h2 h3 hl h4 =>
      C_runs_native a64DMN H (by decide) program compiled f eI eO a s call h1 h2 h3 hl h4

end Proven.Apc.Blocks
