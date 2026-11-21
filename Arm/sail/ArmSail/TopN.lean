/- **The nano native AArch64 compiler (C → J → the JArm translator) on the official Sail ARM v9.4-A model, with no
premise left**: the release theorems `C_correct_native_release` / `C_runs_native_release` (Nano/Main/NativeRelease.lean,
generic over `A64SemN`) instantiated with `a64SailN`, the loader contract discharged (`loader_ok`, Sail's permission
predicates are `True`), and moved to Spec's `Proven.Top.armSail` by `spec_eq`, as for rv2arm in Top.lean. -/
import ArmSail.Top
import ArmSail.A64N
import Nano.Main.NativeRelease
namespace ArmSail
open Proven.Top Proven.Top.Alloc NanoMain

theorem C_correct_native_release_armSail : CompileCorrect Proven.Top.armSail compileNano :=
  spec_eq ▸ show CompileCorrect ArmSail.armSail compileNano from fun program compiled f eI eO a s call h1 h2 h3 h4 h5 =>
    C_correct_native_release a64SailN (by decide) program compiled f eI eO a s call h1 h2 h3 (loader_ok _ _ _ _) h4 h5

theorem C_runs_native_release_armSail : CompileRuns Proven.Top.armSail compileNano :=
  spec_eq ▸ show CompileRuns ArmSail.armSail compileNano from fun program compiled f eI eO a s call h1 h2 h3 h4 =>
    C_runs_native_release a64SailN (by decide) program compiled f eI eO a s call h1 h2 h3 (loader_ok _ _ _ _) h4

end ArmSail
