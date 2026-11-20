/- Opus box E: `C_correctL` with `GenStage` discharged (`SimW.gen_stage`). What remains: `BndStage` and `DBStage`
(Gen's field bounds `DB` for accepted programs; both to come from O's `parsed_bnd`). -/
import Nano.V2Self.Proof.Main.MainTop
import Nano.V2Self.Proof.Main.GenStageE
open LeanRV64D
namespace NanoMain
open ParSpec Proven.Top Proven.Top.Alloc LeanRV64D

theorem genStage (HDB : DBStage) : GenStage := SimW.gen_stage HDB

/-- codegen with the explicit exact work bound -/
theorem genStageM (HDB : DBStage) : GenStageM := fun c ts p hp hts hL h =>
  gen_implementsMD c hp hts hL h (HDB c ts p hp hts hL h)

/-- **C is correct**, given the size bounds -/
theorem C_correctLE (HB : BndStage) (HDB : DBStage) : CompileCorrect riscv compileC :=
  C_correctL HB (genStageM HDB)

end NanoMain
