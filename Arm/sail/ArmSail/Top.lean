/- **The C compiler (C → RISC-V words → rv2arm) is correct on the official Sail ARM v9.4-A model** (`armSail`), as
`Spec`'s `CompileCorrect` / `CompileRuns` (no loader premise: Sail's permission predicates are `True`, so
`ArmLoader TT TT` always holds). From `C_correct_rv2arm` / `C_runs_rv2arm` (Nano/V2Self/Proof/Main/ArmTop.lean) and
`a64Sail`; the same route as `cc_of_P` / `cr_of_P` (TopOn.lean), with the loader premise discharged. -/
import Nano.V2Self.Proof.Main.ArmTop
import ArmSail.A64
namespace ArmSail
open Proven.Top NanoMain

theorem loader_ok (s : St) (call : Call) (code x : List UInt8) : JT.ArmLoader (M := armSail) TT TT s call code x :=
  ⟨fun _ _ _ => trivial, fun _ _ => trivial⟩

theorem C_correct_armSail : CompileCorrect armSail (compileOn ArmRA.rv2arm) :=
  fun program compiled f eI eO a s call h1 h2 h3 h4 h5 =>
    C_correct_rv2arm a64Sail (by decide) program compiled f eI eO a s call h1 h2 h3 (loader_ok _ _ _ _) h4 h5

theorem C_runs_armSail : CompileRuns armSail (compileOn ArmRA.rv2arm) :=
  fun program compiled f eI eO a s call h1 h2 h3 h4 =>
    C_runs_rv2arm a64Sail (by decide) program compiled f eI eO a s call h1 h2 h3 (loader_ok _ _ _ _) h4

end ArmSail
