/- **The nano native AArch64 compiler, with no premise left**: `compileNano` (C's front end and Gen, then the J → AArch64
translator of Nano/Codegen/JArm.lean; `genNano x = C.e71 x (AST x)`, exactly what the bootstrap program runs) is correct
on every machine with the abstract A64 steps `A64SemN` — `C_correct_nano` / `C_runs_nano` (NativeNano.lean) with the
translator's per-atom facts `JT.stepOK` (Nano/Run/JArmStepAll.lean) supplied. -/
import Nano.Main.NativeNano
import Nano.Run.JArmStepAll
namespace NanoMain
open Proven.Top Proven.Top.Alloc JT

variable {M : Machine} {X W : M.State → Nat → Prop}

/-- **the native compile is correct on AArch64** -/
theorem C_correct_native_release (A : A64SemN M X W) (hwin : 2 ^ 31 ≤ M.ramStart) :
    CompileCorrectP M (ArmLoader X W) compileNano := C_correct_nano A stepOK hwin

/-- **the native compile runs correctly on AArch64, with any work block** -/
theorem C_runs_native_release (A : A64SemN M X W) (hwin : 2 ^ 31 ≤ M.ramStart) :
    CompileRunsP M (ArmLoader X W) compileNano := C_runs_nano A stepOK hwin

end NanoMain
