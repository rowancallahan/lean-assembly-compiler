/- Opus box E: `C_correctL` with `GenStage` discharged (`SimW.gen_stage`). What remains: `BndStage` and `DBStage`
(Gen's field bounds `DB` for accepted programs; both to come from O's `parsed_bnd`). -/
import Nano.V2Self.Proof.MainTop
import Nano.V2Self.Proof.GenStageE
open LeanRV64D
namespace NanoMain
open ParSpec Proven.Top Proven.Top.Alloc LeanRV64D

/-- the field bounds `DB` (fields < 2^32, `NB`) for every program Gen accepts -/
def DBStage : Prop := ∀ (c : List UInt8) (ts : List UInt64) (p : List DefA), ParsesProgram ts p →
  ts.length < 2 ^ 24 → LinearK p → C.g41 c (serialize p) ≠ [] → ∀ d ∈ p, Templates.DB d

theorem genStage (HDB : DBStage) : GenStage := SimW.gen_stage HDB

/-- codegen with the explicit exact work bound -/
theorem genStageM (HDB : DBStage) : GenStageM := fun c ts p hp hts hL h =>
  gen_implementsMD c hp hts hL h (HDB c ts p hp hts hL h)

/-- **C is correct**, given the size bounds -/
theorem C_correctLE (HB : BndStage) (HDB : DBStage) : CompileCorrect riscv compileC :=
  C_correctL HB (genStageM HDB)

end NanoMain
