/- C's top-level theorems on AArch64, modulo the abstract A64 steps: for ANY machine `M` with `A64Sem M`
(Machine/A64Sem.lean; supplied by a model: the DeepMind surrogate or the Sail ARM model), the ARM adapter
`armTarget M` (Machine/ArmTarget.lean) satisfies the generic laws, so `C_correct_on` / `C_runs_on` give
`CompileCorrect M (compileOn enc)` and `CompileRuns M (compileOn enc)` for any byte translator `enc` that turns Gen's
bytes into the adapter's blocks (`EncOK`, e.g. rv2arm).  Remaining premise `hwin : 2^31 ≤ ramStart`: the exact work
bound's position lemmas (D's `shiftInvL` lowers it to 2048; then it follows from `A64Sem.ram`). -/
import Nano.V2Self.Proof.Main.TopOn
import Nano.V2Self.Proof.Machine.ArmTarget
namespace NanoMain
open Proven.Top Proven.Top.Alloc JT

/-- **C is correct on AArch64** (given the A64 steps, the translator's `EncOK` and the work window) -/
theorem C_correct_arm {M : Machine} (S : A64Sem M) (enc : List UInt8 → List UInt8) (hE : EncOK (armTarget M) enc)
    (hwin : 2 ^ 31 ≤ M.ramStart) : CompileCorrect M (compileOn enc) :=
  C_correct_on (armLaws S) enc hE hwin

/-- **C runs correctly on AArch64, with any work block** -/
theorem C_runs_arm {M : Machine} (S : A64Sem M) (enc : List UInt8 → List UInt8) (hE : EncOK (armTarget M) enc)
    (hwin : 2 ^ 31 ≤ M.ramStart) : CompileRuns M (compileOn enc) :=
  C_runs_on (armLaws S) enc hE hwin

end NanoMain
