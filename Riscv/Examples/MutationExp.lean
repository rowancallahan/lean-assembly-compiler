/- Mutation testing of the expression specification (the statement of `compile_ok`): three one-word mutants
(change `add` → `sub`, `sltu` → `slt`, drop an `addi`) are rejected.

`ExpSpec code f` is `compile_ok`'s conclusion for arbitrary code: from every `Cfg` state with the code at `pc`
and an even `ra`, the machine returns to `ra` with `a0 = f (a0..a3)`, memory unchanged, callee-saved kept.
`compile_spec` restates `compile_ok`.  Each mutant is `compile e'` for a source `e'`, so `compile_ok` gives its
actual result; with `ra` parked (`jal x0, 0`) the run is unique (`runsTo_unique`) and the two values of `a0` must
agree, which fails on the chosen inputs. -/
import Riscv.Examples.VacuityExp
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Proven.Vacuity

def ExpSpec (code : List (BitVec 32)) (f : (Fin 4 → BitVec 64) → BitVec 64) : Prop :=
  ∀ (s : St) (pc : BitVec 64), Cfg s → s.regs.get? .PC = some pc → codeAt s pc code → codeOK pc code.length →
    (getX s 1).toNat % 2 = 0 →
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 10 = f (fun i => getX s (A i)) ∧
      Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s'

theorem compile_spec (e : Exp) (he : e.depth < 11) : ExpSpec (compile e) e.denote :=
  fun _ _ h hpc hc hok hra => compile_ok e he h hpc hc hok hra

/-- the inputs `a0..a3` of the witness `sC code a0 a1` -/
def envC (a0 a1 : BitVec 64) : Fin 4 → BitVec 64 := fun i => if i = 0 then a0 else if i = 1 then a1 else 0

theorem sC_env (code : List (BitVec 32)) (a0 a1 : BitVec 64) :
    (fun i : Fin 4 => getX (sC code a0 a1) (A i)) = envC a0 a1 := by
  funext i; rw [sC_x]
  obtain ⟨n, hn⟩ := i
  rcases n with _ | _ | _ | _ | n <;> first | omega | rfl

/-- **The kill lemma** for expression code. -/
theorem kill_exp {code : List (BitVec 32)} {f : (Fin 4 → BitVec 64) → BitVec 64} (e' : Exp)
    (hcode : compile e' = code) (he' : e'.depth < 11) (hlen : code.length ≤ 1000) (a0 a1 : BitVec 64)
    (hne : e'.denote (envC a0 a1) ≠ f (envC a0 a1)) : ¬ ExpSpec code f := by
  intro H; subst hcode
  have r1 := H (sC (compile e') a0 a1) pc0 (sC_cfg ..) (sC_pc ..) (sC_code hlen a0 a1) (codeOK_pc0 hlen)
    (sC_ra_even ..)
  have r2 := compile_spec e' he' (sC (compile e') a0 a1) pc0 (sC_cfg ..) (sC_pc ..) (sC_code hlen a0 a1)
    (codeOK_pc0 hlen) (sC_ra_even ..)
  have park : ∀ t : St, Cfg t → t.regs.get? .PC = some (getX (sC (compile e') a0 a1) 1) →
      t.mem = (sC (compile e') a0 a1).mem → Cfg t ∧ t.regs.get? .PC = some ra0 ∧ instrAt t ra0 park :=
    fun t h1 h2 h3 => ⟨h1, by rw [h2, sC_ra], by unfold instrAt; rw [h3]; exact sC_park hlen a0 a1⟩
  obtain ⟨t₁, t₂, p₁, p₂, -, hx⟩ := runsTo_unique pcOK_ra0 r1 r2
    (fun t ⟨q1, _, q3, q4, _⟩ => park t q3 q1 q4) (fun t ⟨q1, _, q3, q4, _⟩ => park t q3 q1 q4)
  apply hne
  have e1 := p₁.2.1; have e2 := p₂.2.1; rw [sC_env] at e1 e2; dsimp only at e1 e2
  rw [← e2, ← e1, hx]

/-! ## The mutants -/

open Exp in
/-- `a0 + a1` -/
def eAdd : Exp := bin .add (var 0) (var 1)
open Exp in
/-- `min_u (a0, a1)` -/
def eMin : Exp := ite (bin .ult (var 0) (var 1)) (var 0) (var 1)
open Exp in
/-- `a0 + 5` -/
def eAdd5 : Exp := bin .add (var 0) (const 5)

/-- X1: `add t0, t0, t1` → `sub t0, t0, t1` -/
theorem mutX1_diff : compile (.bin .sub (.var 0) (.var 1)) = (compile eAdd).set 2 (iOp .sub 0) ∧
    compile eAdd ≠ (compile eAdd).set 2 (iOp .sub 0) := by decide +kernel
/-- X2: `sltu t0, t0, t1` → `slt t0, t0, t1` -/
theorem mutX2_diff :
    compile (.ite (.bin .slt (.var 0) (.var 1)) (.var 0) (.var 1)) = (compile eMin).set 2 (iOp .slt 0) ∧
    compile eMin ≠ (compile eMin).set 2 (iOp .slt 0) := by decide +kernel
/-- X3: drop the last `addi t1, t1, 1` of the constant `5` (so the code builds `4`) -/
theorem mutX3_diff : compile (.bin .add (.var 0) (.const 4)) = (compile eAdd5).eraseIdx 6 := by decide +kernel

/-- **X1 is rejected**: on `a0 = 5, a1 = 3` it returns `2`, not `8`. -/
theorem mutX1_killed : ¬ ExpSpec ((compile eAdd).set 2 (iOp .sub 0)) eAdd.denote :=
  kill_exp (.bin .sub (.var 0) (.var 1)) mutX1_diff.1 (by decide) (by decide +kernel) 5 3 (by decide)
/-- **X2 is rejected**: on `a0 = -1, a1 = 1` (unsigned min `1`) it returns `-1`. -/
theorem mutX2_killed : ¬ ExpSpec ((compile eMin).set 2 (iOp .slt 0)) eMin.denote :=
  kill_exp (.ite (.bin .slt (.var 0) (.var 1)) (.var 0) (.var 1)) mutX2_diff.1 (by decide) (by decide +kernel)
    (-1) 1 (by decide)
/-- **X3 is rejected**: on `a0 = 0` it returns `4`, not `5`. -/
theorem mutX3_killed : ¬ ExpSpec ((compile eAdd5).eraseIdx 6) eAdd5.denote :=
  kill_exp (.bin .add (.var 0) (.const 4)) mutX3_diff (by decide) (by decide +kernel) 0 0 (by decide)

/-- and the originals do satisfy it -/
theorem exp_originals : ExpSpec (compile eAdd) eAdd.denote ∧ ExpSpec (compile eMin) eMin.denote ∧
    ExpSpec (compile eAdd5) eAdd5.denote :=
  ⟨compile_spec _ (by decide), compile_spec _ (by decide), compile_spec _ (by decide)⟩

end Proven.Vacuity
