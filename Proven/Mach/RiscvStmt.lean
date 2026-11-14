/- `compileS_ok`, `compileF_ok`, `gcd_ok`, `sum_ok` re-derived through the interface: `Proven.Stmt` is mapped
to the model-free copy `Mach.Stmt`, the middle theorems `Machine.execS_ok` / `Machine.compF_ok` are
instantiated with `rv`, and the abstract code is shown to encode to exactly `compileS` / `compileF`. -/
import Proven.Mach.RiscvExp
import Proven.Mach.Stmt
import Proven.LoopExamples

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

def toM : Proven.Stmt → Mach.Stmt
  | .assign v e => .assign v e
  | .seq a b => .seq (toM a) (toM b)
  | .loop c b => .loop c (toM b)

theorem exec_toM : ∀ {p : Proven.Stmt} {σ σ' : Proven.Env}, Proven.Exec p σ σ' → Mach.Exec (toM p) σ σ'
  | _, _, _, .assign => .assign
  | _, _, _, .seq a b => .seq (exec_toM a) (exec_toM b)
  | _, _, _, .loopF h => .loopF h
  | _, _, _, .loopT h b l => .loopT h (exec_toM b) (exec_toM l)

theorem code_compS : ∀ p : Proven.Stmt, p.wf → rv.code (rv.compS (toM p)) = compileS p ∧ rv.wf (toM p)
  | .assign v e, hp => by
    refine ⟨?_, hp⟩
    simp only [toM, Machine.compS, compileS, Machine.code_append, Machine.code_one, code_genE e 0 (by
      simp only [Stmt.wf] at hp; omega)]
    show _ ++ [encR 0 0 (phys (v4 v)) 0 (phys (rk 0))] = _
    rw [phys_v4, show phys (rk 0) = 5 by decide]; rfl
  | .seq a b, hp => by
    obtain ⟨ea, wa⟩ := code_compS a hp.1
    obtain ⟨eb, wb⟩ := code_compS b hp.2
    exact ⟨by simp only [toM, Machine.compS, compileS, Machine.code_append, ea, eb], wa, wb⟩
  | .loop c b, hp => by
    obtain ⟨hp1, hp2, hp3⟩ := hp
    obtain ⟨eb, wb⟩ := code_compS b hp2
    have ec := code_genE c 0 (by omega)
    refine ⟨?_, hp1, wb, ?_, ?_⟩
    · rw [toM, Machine.code_loop, eb, ec]; rfl
    · show 2 * ((rv.code (rv.compS (toM b))).length + 1 + 1) < 2048
      rw [eb]; omega
    · show 0 < (rv.code (mgenE c 0)).length + 1 + (rv.code (rv.compS (toM b))).length ∧
        2 * ((rv.code (mgenE c 0)).length + 1 + (rv.code (rv.compS (toM b))).length) ≤ 2 ^ 19
      rw [eb, ec]; omega

/-- **`compileS_ok`, re-derived** through the interface (same statement as `Proven.compileS_ok`). -/
theorem compileS_ok' {p : Proven.Stmt} (hp : p.wf) {σ σ' : Proven.Env} (hex : Proven.Exec p σ σ') {s : St} (h : Cfg s)
    {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileS p))
    (hok : codeOK pc (compileS p).length) (henv : ∀ i : Fin 4, getX s (A i) = σ i) :
    runsTo s fun s' => s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (compileS p).length)) ∧
      (∀ i : Fin 4, getX s' (A i) = σ' i) ∧ Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s' := by
  obtain ⟨ec, wf⟩ := code_compS p hp
  rw [← ec] at hc hok ⊢
  refine runsTo_mono (rv.execS_ok (exec_toM hex) wf ⟨h, hpc, hc, hok⟩ fun i => by
    show getX s (phys (v4 i)) = _; rw [phys_v4]; exact henv i) fun s' ⟨d, m, v⟩ =>
    ⟨d.hpc, fun i => by have := v i; rwa [show rv.get s' (v4 i) = getX s' (A i) by
      show getX s' (phys (v4 i)) = _; rw [phys_v4]] at this, d.ok, mem_of m,
      calleeSaved_of_frame h (frame_of d.ok (mem_of m) d.keep)⟩

theorem code_compF (p : Proven.Stmt) (hp : p.wf) : rv.code (rv.compF (toM p)) = compileF p := by
  rw [Machine.compF, Machine.code_append, (code_compS p hp).1]; rfl

/-- **`compileF_ok`, re-derived** through the interface (same statement as `Proven.compileF_ok`). -/
theorem compileF_ok' {p : Proven.Stmt} (hp : p.wf) {σ' : Proven.Env} {s : St}
    (hex : Proven.Exec p (fun i => getX s (A i)) σ') (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileF p))
    (hok : codeOK pc (compileF p).length) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ (∀ i : Fin 4, getX s' (A i) = σ' i) ∧ Cfg s' ∧
      s'.mem = s.mem ∧ calleeSavedKept s s' := by
  rw [← code_compF p hp] at hc hok
  have e : (fun i : Fin 4 => getX s (A i)) = fun i => rv.get s (v4 i) := funext fun i => by
    show _ = getX s (phys (v4 i)); rw [phys_v4]
  rw [e] at hex
  refine runsTo_mono (rv.compF_ok (code_compS p hp).2 (exec_toM hex) ⟨h, hpc, hc, hok⟩ hra)
    fun s' ⟨p', v, c, m, k⟩ => ⟨p', fun i => ?_, c, mem_of m, calleeSaved_of_frame h (frame_of c (mem_of m) k)⟩
  have := v i
  rwa [show rv.get s' (v4 i) = getX s' (A i) by show getX s' (phys (v4 i)) = _; rw [phys_v4]] at this

/-- `gcd_ok`, re-derived (same statement as `Proven.gcd_ok`). -/
theorem gcd_ok' {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileF gcdProg)) (hok : codeOK pc (compileF gcdProg).length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 10 = gcdSub (getX s 10) (getX s 11) ∧
      Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s' := by
  obtain ⟨σ', hex, hv⟩ := gcdProg_exec (fun i => getX s (A i))
  exact runsTo_mono (compileF_ok' gcdProg_wf hex h hpc hc hok hra) fun s' ⟨h1, h2, h3⟩ =>
    ⟨h1, (h2 0).trans hv, h3⟩

/-- `sum_ok`, re-derived (same statement as `Proven.sum_ok`). -/
theorem sum_ok' {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileF sumProg)) (hok : codeOK pc (compileF sumProg).length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 10 = sumDown (getX s 10) (getX s 11) ∧
      Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s' := by
  obtain ⟨σ', hex, hv⟩ := sumProg_exec (fun i => getX s (A i))
  exact runsTo_mono (compileF_ok' sumProg_wf hex h hpc hc hok hra) fun s' ⟨h1, h2, h3⟩ =>
    ⟨h1, (h2 0).trans hv, h3⟩

end Proven.Mach.Riscv

/-! Same statements as the originals (checked by the elaborator): -/
example : type_of% @Proven.Mach.Riscv.compileS_ok' = type_of% @Proven.compileS_ok := rfl
example : type_of% @Proven.Mach.Riscv.compileF_ok' = type_of% @Proven.compileF_ok := rfl
example : type_of% @Proven.Mach.Riscv.gcd_ok' = type_of% @Proven.gcd_ok := rfl
example : type_of% @Proven.Mach.Riscv.sum_ok' = type_of% @Proven.sum_ok := rfl
