/- **The optimising compiler on RISC-V**: `compileOpt` (expressions), `compileOptS` (loops), `compileOptA`
(byte arrays), each a pure function to `Except String (List (BitVec 32))`, each with ONE theorem of the
shape of the unoptimised one (`compile_ok`, `compileF_ok`, `compileAF_ok`): if the compiler returns words,
the Sail model running them computes the source semantics.  The passes are in `Compiler/Opt/` (proved
against the `Wide` interface); here only the instance `rvw` and the conversion to the RISC-V statements. -/
import Riscv.Back.Wide
import Riscv.Back.Exp
import Riscv.Back.Stmt
import Compiler.Opt.Stmt
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven
open Mach Mach.Riscv

def ofOpt (what : String) : Option (List (BitVec 32)) → Except String (List (BitVec 32))
  | some ws => .ok ws
  | none => .error s!"{what}: out of temporaries, or a branch out of range, or a block variable assigned"

theorem ofOpt_ok {what : String} {o : Option (List (BitVec 32))} {ws : List (BitVec 32)}
    (h : ofOpt what o = .ok ws) : o = some ws := by
  cases o with
  | none => exact nomatch h
  | some w => cases h; rfl

/-- **The optimising `Exp` compiler.** -/
def compileOpt (e : Exp) : Except String (List (BitVec 32)) := ofOpt "compileOpt" (rvw.optE e)

/-- **`compileOpt` is correct** (the statement of `compile_ok` for the words it returns). -/
theorem compileOpt_ok (e : Exp) {ws : List (BitVec 32)} (hc : compileOpt e = .ok ws) {s : St} (h : Cfg s)
    {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hcode : codeAt s pc ws) (hok : codeOK pc ws.length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      getX s' 10 = e.denote (fun i => getX s (A i)) ∧ Cfg s' ∧ s'.mem = s.mem ∧
      calleeSavedKept s s' := by
  refine runsTo_mono (rvw.optE_ok e (ofOpt_ok hc) ⟨h, hpc, hcode, hok⟩ hra) fun s' ⟨p, v, c, m, k⟩ =>
    ⟨p, ?_, c, mem_of m, calleeSaved_of_frame h (frame_of c (mem_of m) k)⟩
  have e1 : phys (rk 11) = 10 := by decide
  have e2 : (fun i => rvw.get s (v4 i)) = fun i : Fin 4 => getX s (A i) := funext fun i => by
    show getX s (phys (v4 i)) = _; rw [phys_v4]
  have : getX s' (phys (rk 11)) = _ := v
  rwa [e1, e2] at this

/-- **The optimising loop compiler.** -/
def compileOptS (p : Proven.Stmt) : Except String (List (BitVec 32)) := ofOpt "compileOptS" (rvw.optS (toM p))

/-- **`compileOptS` is correct** (the statement of `compileF_ok` for the words it returns). -/
theorem compileOptS_ok {p : Proven.Stmt} {ws : List (BitVec 32)} (hc : compileOptS p = .ok ws) {σ' : Proven.Env}
    {s : St} (hex : Proven.Exec p (fun i => getX s (A i)) σ') (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hcode : codeAt s pc ws) (hok : codeOK pc ws.length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ (∀ i : Fin 4, getX s' (A i) = σ' i) ∧ Cfg s' ∧
      s'.mem = s.mem ∧ calleeSavedKept s s' := by
  have e : (fun i : Fin 4 => getX s (A i)) = fun i => rvw.get s (v4 i) := funext fun i => by
    show _ = getX s (phys (v4 i)); rw [phys_v4]
  rw [e] at hex
  refine runsTo_mono (rvw.optS_ok (ofOpt_ok hc) (exec_toM hex) ⟨h, hpc, hcode, hok⟩ hra)
    fun s' ⟨p', v, c, m, k⟩ => ⟨p', fun i => ?_, c, mem_of m, calleeSaved_of_frame h (frame_of c (mem_of m) k)⟩
  have := v i
  rwa [show rvw.get s' (v4 i) = getX s' (A i) by show getX s' (phys (v4 i)) = _; rw [phys_v4]] at this

/-! ## Drop-in replacements: total functions with the statements of the unoptimised theorems
(optimised words when the optimiser succeeds, the old words otherwise) -/

/-- drop-in for `compile` -/
def compileO (e : Exp) : List (BitVec 32) := match compileOpt e with | .ok ws => ws | .error _ => compile e

/-- the statement of `compile_ok` for `compileO` -/
theorem compileO_ok (e : Exp) (he : e.depth < 11) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileO e))
    (hok : codeOK pc (compileO e).length) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      getX s' 10 = e.denote (fun i => getX s (A i)) ∧ Cfg s' ∧ s'.mem = s.mem ∧
      calleeSavedKept s s' := by
  unfold compileO at hc hok
  cases hx : compileOpt e with
  | ok ws => rw [hx] at hc hok; exact compileOpt_ok e hx h hpc hc hok hra
  | error _ => rw [hx] at hc hok; exact compile_ok' e he h hpc hc hok hra

/-- drop-in for `compileF` -/
def compileFO (p : Proven.Stmt) : List (BitVec 32) := match compileOptS p with | .ok ws => ws | .error _ => compileF p

/-- the statement of `compileF_ok` for `compileFO` -/
theorem compileFO_ok {p : Proven.Stmt} (hp : p.wf) {σ' : Proven.Env} {s : St}
    (hex : Proven.Exec p (fun i => getX s (A i)) σ') (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileFO p))
    (hok : codeOK pc (compileFO p).length) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ (∀ i : Fin 4, getX s' (A i) = σ' i) ∧ Cfg s' ∧
      s'.mem = s.mem ∧ calleeSavedKept s s' := by
  unfold compileFO at hc hok
  cases hx : compileOptS p with
  | ok ws => rw [hx] at hc hok; exact compileOptS_ok hx hex h hpc hc hok hra
  | error _ => rw [hx] at hc hok; exact compileF_ok' hp hex h hpc hc hok hra

end Proven
