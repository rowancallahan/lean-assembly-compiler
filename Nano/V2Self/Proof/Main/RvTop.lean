/- The RISC-V instance of the generic top theorems (Main/TopOn.lean): Gen's bytes ARE the RISC-V code bytes of its J
program (`rv_enc`), and `compileOn id = compileC`, so `CompileCorrect riscv compileC` and `CompileRuns riscv compileC`
follow from `rvLaws`. -/
import Nano.V2Self.Proof.Main.TopOn
import Nano.V2Self.Proof.Machine.RvTarget
namespace NanoMain
open Proven.Top Proven.Top.Alloc JT

theorem le4_wbyte (v : UInt64) :
    SimW.le4 v = [wbyte (BitVec.ofNat 32 v.toNat) 0, wbyte (BitVec.ofNat 32 v.toNat) 1,
      wbyte (BitVec.ofNat 32 v.toNat) 2, wbyte (BitVec.ofNat 32 v.toNat) 3] := by
  simp only [SimW.le4, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.1 <;>
    simp [wbyte, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, UInt64.toNat_shiftRight] <;> omega

theorem flat_rv : ∀ (Cj : List CallProbe.J), (Cj.map CallProbe.encG).map UInt64.toNat = Cj.map SimW.encJX →
    (Cj.map CallProbe.encG).flatMap SimW.le4 = tbytes rvTarget Cj
  | [], _ => rfl
  | j :: Cj, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have ih := flat_rv Cj h.2
    unfold tbytes at ih ⊢
    simp only [List.map_cons, List.flatMap_cons, ih, le4_wbyte, h.1]
    rfl

/-- Gen's bytes are the RISC-V code bytes of its J program -/
theorem rv_enc : EncOK rvTarget id := by
  intro c Cj hc hw
  have e0 : (0 : UInt64) = UInt64.ofNat 0 := rfl
  rw [id, e0, SimW.g40_bytes c _ (by rw [List.length_map]; omega) 16777216 0 [] (by rw [List.length_map]; omega)
    (by omega)]
  simpa using flat_rv Cj hw

theorem compileOn_id : compileOn id = compileC := by
  funext s; unfold compileOn compileC; rw [id_eq]

/-- **C is correct** (RISC-V): the generic `C_correct_on` for `rvTarget` -/
theorem C_correctLO : CompileCorrect riscv compileC := by
  rw [← compileOn_id]; exact C_correct_on rvLaws id rv_enc (by decide)

/-- **C runs correctly with any work block** (owner's `CompileRuns`, RISC-V: the generic `C_runs_on` for `rvTarget`):
return to the caller, memory changed only in the work block and the result prefix of the output block, callee-saved
registers kept, configured, and out of memory reported (a0 = −1) exactly when the work block is smaller than
`memoryNeeded`. -/
theorem C_runsO : CompileRuns riscv compileC := by
  rw [← compileOn_id]; exact C_runs_on rvLaws id rv_enc (by decide)

/-- `C_runsO` under the former premise `ShiftInv` (D's `shiftInv` proves it; kept as a REVIEW root) -/
theorem C_runs (_HS : ShiftInv) : CompileRuns riscv compileC := C_runsO

end NanoMain
