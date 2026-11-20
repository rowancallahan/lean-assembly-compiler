/- **The C compiler (C → RISC-V words → rv2arm) is correct on DeepMind's AArch64 model**, stated against
`Proven.Top.armDM` (Spec/ARM/DeepMind.lean) as `CompileCorrectLoaded` / `CompileRunsLoaded` (Spec/Loader.lean): for
start states whose loader maps the code executable and the data blocks readable+writable (DeepMind's W^X permissions
are not observable through `Spec`). Proved on the proof-side `armDM` (Blocks/ArmDM.lean) from E's
`C_correct_rv2arm` / `C_runs_rv2arm` (Nano/V2Self/Proof/Main/ArmTop.lean) and `a64DM`, then moved to the Spec
machine (`obs_spec`: the observations agree). Interim target: the final theorem is on Sail. -/
import Nano.V2Self.Proof.Main.ArmTop
import Blocks.A64Inst
import Spec.ARM.DeepMind
import Spec.Loader
namespace Proven.Apc.Blocks
open Proven.Top Proven.Top.Alloc NanoMain

theorem obs_spec (t : Arm64.State) : obsDM t = armDMObserve t := by
  simp only [obsDM, armDMObserve, abs]
  congr 1; funext r; by_cases h : r < 31 <;> simp [h]

/-- `Proven.Top.armDM` is `armDM` with `armDMObserve` for `obsDM` (all other fields agree by definition) -/
abbrev armDMWith (o : Arm64.State → MachineState) : Machine := { armDM with observe := o }

theorem C_correct_armDM : CompileCorrectLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable (compileOn ArmRA.rv2arm) :=
  Eq.subst (motive := fun o => CompileCorrectLoaded (armDMWith o) ArmDMExecutable ArmDMWritable (compileOn ArmRA.rv2arm))
    (funext obs_spec) fun program compiled f eI eO a s call h1 h2 h3 hl h4 h5 =>
      C_correct_rv2arm a64DM (by decide) program compiled f eI eO a s call h1 h2 h3 hl h4 h5

theorem C_runs_armDM : CompileRunsLoaded Proven.Top.armDM ArmDMExecutable ArmDMWritable (compileOn ArmRA.rv2arm) :=
  Eq.subst (motive := fun o => CompileRunsLoaded (armDMWith o) ArmDMExecutable ArmDMWritable (compileOn ArmRA.rv2arm))
    (funext obs_spec) fun program compiled f eI eO a s call h1 h2 h3 hl h4 =>
      C_runs_rv2arm a64DM (by decide) program compiled f eI eO a s call h1 h2 h3 hl h4

end Proven.Apc.Blocks
