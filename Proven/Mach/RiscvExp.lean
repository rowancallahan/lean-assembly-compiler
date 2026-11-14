/- `compile_ok` re-derived through the interface: the middle theorem `Machine.compile_ok` instantiated
with the RISC-V machine `rv`, plus the proof that the abstract code encodes to exactly the words of the
existing `compile`. -/
import Proven.Mach.Riscv

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

theorem A8_A : ∀ i : Fin 4, A8 ⟨i.val, by omega⟩ = A i.val := by decide

/-- the abstract code of `mgen8` encodes to `gen8` -/
theorem code_gen8 : ∀ (e : AExp) (k : Nat), k + e.depth < 11 → rv.code (mgen8 e k) = gen8 e k
  | .var i, k, hk => by
    simp only [mgen8, gen8, Machine.code_one]
    show [encR 0 0 (phys (rk k)) 0 (phys (avar i))] = [iVar8 i k]
    rw [phys_rk (by simp only [AExp.depth] at hk; omega), phys_avar]; rfl
  | .const c, k, hk => by
    simp only [mgen8, gen8, Machine.code_one]
    show genConst (rk k).val c.toNat = _
    rw [rk_val (by simp only [AExp.depth] at hk; omega)]
  | .bin op a b, k, hk => by
    simp only [AExp.depth] at hk
    simp only [mgen8, gen8, Machine.code_append, Machine.code_one, code_gen8 a k (by omega),
      code_gen8 b (k + 1) (by omega)]
    show _ ++ opCode op (rk k).val = _
    rw [rk_val (by omega)]
  | .ite c a b, k, hk => by
    simp only [AExp.depth] at hk
    simp only [mgen8, gen8, Machine.code_append, Machine.code_one, code_gen8 c k (by omega),
      code_gen8 a (k + 1) (by omega), code_gen8 b (k + 2) (by omega)]
    show _ ++ selCode (rk k).val = _
    rw [rk_val (by omega)]

theorem gen8_toA : ∀ (e : Exp) (k : Nat), gen8 (toA e) k = gen e k
  | .var i, k => by
    simp only [toA, gen8, gen]
    show [encR 0 0 (T k) 0 (A8 ⟨i.val, _⟩)] = [encR 0 0 (T k) 0 (A i.val)]
    rw [A8_A]
  | .const _, _ => rfl
  | .bin op a b, k => by simp only [toA, gen8, gen, gen8_toA a, gen8_toA b]
  | .ite c a b, k => by simp only [toA, gen8, gen, gen8_toA c, gen8_toA a, gen8_toA b]

theorem code_genE (e : Exp) (k : Nat) (hk : k + e.depth < 11) : rv.code (mgenE e k) = gen e k := by
  rw [mgenE, code_gen8 _ _ (by rw [toA_depth]; exact hk), gen8_toA]

theorem code_compile (e : Exp) (he : e.depth < 11) : rv.code (mcompile e) = compile e := by
  simp only [mcompile, compile, Machine.code_append, code_genE e 0 (by omega)]
  rfl

theorem phys_img : ∀ r : Reg, (∃ i : Fin 11, phys r = T i.val) ∨ ∃ i : Fin 4, phys r = A i.val := by decide

/-- `keep` gives the frame of `Proven/Loop.lean` -/
theorem frame_of {s s' : St} (h : Cfg s') (hm : s'.mem = s.mem) (k : rv.keep s s') : Frame s s' :=
  ⟨h, hm, fun j h1 h2 => k j fun r e => by
    rcases phys_img r with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact h1 i.val i.2 (e.trans hi)
    · exact h2 i (e.trans hi)⟩

theorem mem_of {s s' : St} (m : rv.mem s' = rv.mem s) : s'.mem = s.mem :=
  Std.ExtHashMap.ext_getElem? fun a => congrFun m a

/-- **`compile_ok`, re-derived** from the middle-layer theorem `Machine.compile_ok` and the RISC-V
interface laws.  Same statement as `Proven.compile_ok`. -/
theorem compile_ok' (e : Exp) (he : e.depth < 11) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compile e))
    (hok : codeOK pc (compile e).length) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      getX s' 10 = e.denote (fun i => getX s (A i)) ∧ Cfg s' ∧ s'.mem = s.mem ∧
      calleeSavedKept s s' := by
  rw [← code_compile e he] at hc hok
  refine runsTo_mono (rv.compile_ok e he ⟨h, hpc, hc, hok⟩ hra) fun s' ⟨p, v, c, m, k⟩ =>
    ⟨p, ?_, c, mem_of m, calleeSaved_of_frame h (frame_of c (mem_of m) k)⟩
  have e1 : phys (rk 11) = 10 := by decide
  have e2 : (fun i => rv.get s (v4 i)) = fun i : Fin 4 => getX s (A i) := funext fun i => by
    show getX s (phys (v4 i)) = _; rw [phys_v4]
  have : getX s' (phys (rk 11)) = _ := v
  rwa [e1, e2] at this

end Proven.Mach.Riscv

/-- Same statement as the original (checked by the elaborator). -/
example : type_of% @Proven.Mach.Riscv.compile_ok' = type_of% @Proven.compile_ok := rfl
