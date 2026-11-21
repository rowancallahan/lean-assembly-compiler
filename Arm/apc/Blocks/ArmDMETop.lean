/- **The native AArch64 compile, option E (`compileOn enc`: C, then a translator `enc` of Gen's bytes that meets
`EncOKN`, i.e. emits the specification encoder `natEncJ`'s bytes) on DeepMind's AArch64 model**, against
`Proven.Top.armDM` as `CompileCorrectLoaded` / `CompileRunsLoaded` like `C_correct_armDM` (ArmDMTop.lean), from the
generic `C_correct_nativeE` / `C_runs_nativeE` (Nano/Main/NativeEnc.lean) and `a64DMN`.  The only premise left is
`EncOKN enc` (the nano translator's program proof). -/
import Nano.Main.NativeEnc
import Blocks.A64DMN
import Blocks.ArmDMTop
namespace Proven.Apc.Blocks
open Proven.Top Proven.Top.Alloc NanoMain

theorem C_correct_nativeE_armDM (enc : List UInt8 → List UInt8) (hE : EncOKN enc) :
    CompileCorrectLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable (compileOn enc) :=
  Eq.subst (motive := fun o => CompileCorrectLoaded (armDMWith o) ArmDMExecutable ArmDMWritable (compileOn enc))
    (funext obs_spec) fun program compiled f eI eO a s call h1 h2 h3 hl h4 h5 =>
      C_correct_nativeE a64DMN enc hE (by decide) program compiled f eI eO a s call h1 h2 h3 hl h4 h5

theorem C_runs_nativeE_armDM (enc : List UInt8 → List UInt8) (hE : EncOKN enc) :
    CompileRunsLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable (compileOn enc) :=
  Eq.subst (motive := fun o => CompileRunsLoaded (armDMWith o) ArmDMExecutable ArmDMWritable (compileOn enc))
    (funext obs_spec) fun program compiled f eI eO a s call h1 h2 h3 hl h4 =>
      C_runs_nativeE a64DMN enc hE (by decide) program compiled f eI eO a s call h1 h2 h3 hl h4

end Proven.Apc.Blocks
