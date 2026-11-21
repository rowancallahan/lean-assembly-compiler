/- C's top-level theorems on AArch64, modulo the abstract A64 steps: for ANY machine `M` with `A64Sem M X W`
(Machine/A64Sem.lean, over permission predicates X (executable) / W (readable-writable); supplied by a model: the
DeepMind surrogate, W^X, or the Sail ARM model, X = W = True), the ARM adapter `armTarget M X W` (Machine/ArmTarget.lean) satisfies the generic laws, so `C_correct_on` / `C_runs_on` give
`CompileCorrectP M (ArmLoader X W) (compileGen gen)` and `CompileRunsP M (ArmLoader X W) (compileGen gen)` for any
generator `gen` with `GenOK` (`C_correct_armG` / `C_runs_armG`: where a native ARM generator plugs in), in particular
(`compileOn enc`) for any byte translator `enc` that turns Gen's bytes into the adapter's blocks (`EncOK`, e.g. rv2arm).  Remaining premise `hwin : 2^31 ≤ ramStart`: the exact work
bound's position lemmas (D's `shiftInvL` lowers it to 2048; then it follows from `A64Sem.ram`). -/
import Nano.Main.TopOn
import Nano.Run.ArmTarget
import Nano.Run.ArmEncOK
namespace NanoMain
open Proven.Top Proven.Top.Alloc JT

/-- correct on AArch64 for any generator of the adapter's blocks (`GenOK`) -/
theorem C_correct_armG {M : Machine} {X W : M.State → Nat → Prop} (S : A64Sem M X W) (gen : List UInt8 → List UInt8)
    (hG : GenOK (armTarget M X W) gen) (hwin : 2 ^ 31 ≤ M.ramStart) : CompileCorrectP M (ArmLoader X W) (compileGen gen) :=
  C_correct_on (armLaws S) gen hG hwin

/-- runs correctly on AArch64, with any work block, for any generator of the adapter's blocks (`GenOK`) -/
theorem C_runs_armG {M : Machine} {X W : M.State → Nat → Prop} (S : A64Sem M X W) (gen : List UInt8 → List UInt8)
    (hG : GenOK (armTarget M X W) gen) (hwin : 2 ^ 31 ≤ M.ramStart) : CompileRunsP M (ArmLoader X W) (compileGen gen) :=
  C_runs_on (armLaws S) gen hG hwin

/-- **C is correct on AArch64** (given the A64 steps, for the start states that meet the LOADER CONTRACT `ArmLoader X W`
(code mapped executable, data blocks read-write; an assumption about the loader, always true for Sail), given the translator's `EncOK` and the
work window) -/
theorem C_correct_arm {M : Machine} {X W : M.State → Nat → Prop} (S : A64Sem M X W) (enc : List UInt8 → List UInt8) (hE : EncOK (armTarget M X W) enc)
    (hwin : 2 ^ 31 ≤ M.ramStart) : CompileCorrectP M (ArmLoader X W) (compileOn enc) :=
  C_correct_armG S _ (genOK_of_enc hE) hwin

/-- **C runs correctly on AArch64, with any work block** -/
theorem C_runs_arm {M : Machine} {X W : M.State → Nat → Prop} (S : A64Sem M X W) (enc : List UInt8 → List UInt8) (hE : EncOK (armTarget M X W) enc)
    (hwin : 2 ^ 31 ≤ M.ramStart) : CompileRunsP M (ArmLoader X W) (compileOn enc) :=
  C_runs_armG S _ (genOK_of_enc hE) hwin

/-- **C then rv2arm is correct on AArch64** (for start states meeting the loader contract `ArmLoader X W`): the compiler `compileOn rv2arm` (Gen's RISC-V bytes translated by the
rv2arm translator, as a Lean function, `ArmRA.rv2arm`), for any machine with the A64 steps and the work window -/
theorem C_correct_rv2arm {M : Machine} {X W : M.State → Nat → Prop} (S : A64Sem M X W) (hwin : 2 ^ 31 ≤ M.ramStart) :
    CompileCorrectP M (ArmLoader X W) (compileOn ArmRA.rv2arm) :=
  C_correct_arm S _ rv2arm_enc hwin

/-- **C then rv2arm runs correctly on AArch64, with any work block** -/
theorem C_runs_rv2arm {M : Machine} {X W : M.State → Nat → Prop} (S : A64Sem M X W) (hwin : 2 ^ 31 ≤ M.ramStart) :
    CompileRunsP M (ArmLoader X W) (compileOn ArmRA.rv2arm) :=
  C_runs_arm S _ rv2arm_enc hwin

end NanoMain
