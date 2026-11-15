/- gcd by repeated subtraction with gcc's loop structure, through the optimising back end (`compileFO`):
```
  a2 := a1 ? a0 : 0; a1 := a1 ? a1 : a0        -- b = 0: swap, so the loop never runs with b = 0, x ≠ 0
  while a2 ≠ 0 { while a2 < a1 { a1 := a1 - a2 }; a2 := a2 - a1 }
  a0 := a1
```
-/
import Riscv.Back.Opt
import Riscv.Examples.LoopExamples

set_option linter.unusedVariables false

namespace Proven

open Exp in
def gcdProg2 : Stmt :=
  .seq (.assign 2 (ite (var 1) (var 0) (const 0))) (.seq (.assign 1 (ite (var 1) (var 1) (var 0)))
  (.seq (.loop (var 2) (.seq (.loop (bin .ult (var 2) (var 1)) (.assign 1 (bin .sub (var 1) (var 2))))
    (.assign 2 (bin .sub (var 2) (var 1)))))
  (.assign 0 (var 1))))

theorem gcdSub_zero_left (b : BitVec 64) : gcdSub 0 b = b := by rw [gcdSub.eq_def]; simp

theorem gcdSub_zero_right (a : BitVec 64) : gcdSub a 0 = a := by
  rw [gcdSub.eq_def]; split
  · next h => exact h.symm
  · simp

theorem gcdSub_lt {a b : BitVec 64} (ha : a ≠ 0) (hb : b ≠ 0) (h : a < b) : gcdSub a b = gcdSub a (b - a) := by
  rw [gcdSub.eq_def a b, if_neg ha, if_neg hb, if_pos h]

theorem gcdSub_ge {a b : BitVec 64} (ha : a ≠ 0) (hb : b ≠ 0) (h : ¬ a < b) : gcdSub a b = gcdSub (a - b) b := by
  rw [gcdSub.eq_def a b, if_neg ha, if_neg hb, if_neg h]

theorem toNat_ne {a : BitVec 64} (h : a ≠ 0) : a.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))

/-- the reference is `Nat.gcd` on the 64-bit inputs -/
theorem gcdSub_toNat (a b : BitVec 64) : (gcdSub a b).toNat = Nat.gcd a.toNat b.toNat := by
  by_cases ha : a = 0
  · subst ha; rw [gcdSub_zero_left]; simp
  by_cases hb : b = 0
  · subst hb; rw [gcdSub_zero_right]; simp
  have ha' := toNat_ne ha; have hb' := toNat_ne hb
  by_cases h : a < b
  · have hle : a.toNat ≤ b.toNat := by rw [BitVec.lt_def] at h; omega
    rw [gcdSub_lt ha hb h, gcdSub_toNat a (b - a), BitVec.toNat_sub_of_le (BitVec.le_of_lt h),
      Nat.gcd_sub_self_right hle]
  · have hle : b.toNat ≤ a.toNat := by rw [BitVec.lt_def] at h; omega
    rw [gcdSub_ge ha hb h, gcdSub_toNat (a - b) b,
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), Nat.gcd_sub_self_left hle]
termination_by a.toNat + b.toNat
decreasing_by
  all_goals rw [BitVec.toNat_sub]; rw [BitVec.lt_def] at *; omega

open Exp in
theorem gcdProg2_exec (σ : Env) : ∃ σ', Exec gcdProg2 σ σ' ∧ σ' 0 = gcdSub (σ 0) (σ 1) := by
  let G := gcdSub (σ 0) (σ 1)
  -- the inner loop `while a2 < a1 { a1 := a1 - a2 }`
  have inner : ∀ τ : Env, gcdSub (τ 2) (τ 1) = G → τ 2 ≠ 0 → τ 1 ≠ 0 →
      ∃ τ', Exec (.loop (bin .ult (var 2) (var 1)) (.assign 1 (bin .sub (var 1) (var 2)))) τ τ' ∧
        gcdSub (τ' 2) (τ' 1) = G ∧ τ' 2 = τ 2 ∧ τ' 1 ≠ 0 ∧ ¬ τ' 2 < τ' 1 ∧ (τ' 1).toNat ≤ (τ 1).toNat := by
    intro τ0 hG h2 h1
    exact Exec.loop_inv (c := bin .ult (var 2) (var 1)) (b := .assign 1 (bin .sub (var 1) (var 2)))
      (fun τ => gcdSub (τ 2) (τ 1) = G ∧ τ 2 = τ0 2 ∧ τ 1 ≠ 0 ∧ (τ 1).toNat ≤ (τ0 1).toNat)
      (fun τ => gcdSub (τ 2) (τ 1) = G ∧ τ 2 = τ0 2 ∧ τ 1 ≠ 0 ∧ ¬ τ 2 < τ 1 ∧ (τ 1).toNat ≤ (τ0 1).toNat)
      (fun τ => (τ 1).toNat)
      (fun τ ⟨hG, e2, h1, hle⟩ hc => by
        have hlt : τ 2 < τ 1 :=
          Classical.byContradiction fun hn => hc (by simp [Exp.denote, Op.eval, hn])
        have hx : τ 2 ≠ 0 := e2 ▸ h2
        have hl' : (τ 2).toNat < (τ 1).toNat := BitVec.lt_def.1 hlt
        have hx' := toNat_ne hx
        refine ⟨_, .assign, ?_⟩
        simp only [Env.set, Exp.denote, Op.eval, show (2 : Fin 4) ≠ 1 by decide, if_false, if_true]
        refine ⟨⟨?_, e2, ?_, ?_⟩, ?_⟩
        · rw [← hG, gcdSub_lt hx h1 hlt]
        · intro e; have := congrArg BitVec.toNat e; rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)] at this
          simp at this; omega
        · rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)]; omega
        · rw [BitVec.toNat_sub_of_le (BitVec.le_of_lt hlt)]; omega)
      (fun τ ⟨hG, e2, h1, hle⟩ hc => ⟨hG, e2, h1, fun hlt => by simp [Exp.denote, Op.eval, hlt] at hc, hle⟩)
      τ0 ⟨hG, rfl, h1, Nat.le_refl _⟩
  -- the outer loop
  let σ₁ : Env := σ.set 2 ((ite (var 1) (var 0) (const 0)).denote σ)
  let σ₂ : Env := σ₁.set 1 ((ite (var 1) (var 1) (var 0)).denote σ₁)
  have hI₂ : gcdSub (σ₂ 2) (σ₂ 1) = G ∧ (σ₂ 2 ≠ 0 → σ₂ 1 ≠ 0) := by
    by_cases h1 : σ 1 = 0
    · simp [σ₂, σ₁, Env.set, Exp.denote, h1, G]; exact (gcdSub_zero_left _).trans (gcdSub_zero_right _).symm
    · have h1' : ¬ σ 1 = 0#64 := h1
      simp [σ₂, σ₁, Env.set, Exp.denote, h1', G]
  obtain ⟨σ₃, hl, hq⟩ := Exec.loop_inv (c := var 2)
    (b := .seq (.loop (bin .ult (var 2) (var 1)) (.assign 1 (bin .sub (var 1) (var 2))))
      (.assign 2 (bin .sub (var 2) (var 1))))
    (fun τ => gcdSub (τ 2) (τ 1) = G ∧ (τ 2 ≠ 0 → τ 1 ≠ 0)) (fun τ => τ 1 = G)
    (fun τ => (τ 2).toNat + (τ 1).toNat)
    (fun τ ⟨hG, hnz⟩ hc => by
      have h2 : τ 2 ≠ 0 := hc
      obtain ⟨τ', hx, hG', e2, h1', hge, hle⟩ := inner τ hG h2 (hnz h2)
      have hx2 : τ' 2 ≠ 0 := e2 ▸ h2
      have hge' : (τ' 1).toNat ≤ (τ' 2).toNat := by rw [BitVec.lt_def] at hge; omega
      have hb' := toNat_ne h1'
      refine ⟨_, .seq hx .assign, ?_⟩
      simp only [Env.set, Exp.denote, Op.eval, show (1 : Fin 4) ≠ 2 by decide, if_false, if_true]
      refine ⟨⟨?_, fun _ => h1'⟩, ?_⟩
      · rw [← hG', gcdSub_ge hx2 h1' hge]
      · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), ← e2]; omega)
    (fun τ ⟨hG, _⟩ hc => by
      have h2 : τ 2 = 0 := by simpa [Exp.denote] using hc
      rw [← hG, h2, gcdSub_zero_left])
    σ₂ hI₂
  exact ⟨_, .seq .assign (.seq .assign (.seq hl .assign)), by simp [Env.set, Exp.denote, hq, G]⟩

theorem gcdProg2_wf : gcdProg2.wf := by simp only [gcdProg2, Stmt.wf]; decide +kernel

/-- gcd, optimised: `compileFO gcdProg2` (13 words) -/
def gcdCodeO : List (BitVec 32) := compileFO gcdProg2

/-- **gcd, optimised**: the statement of `gcd_ok` for `gcdCodeO` -/
theorem gcdO_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc gcdCodeO) (hok : codeOK pc gcdCodeO.length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 10 = gcdSub (getX s 10) (getX s 11) ∧
      Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s' := by
  obtain ⟨σ', hex, hv⟩ := gcdProg2_exec (fun i => getX s (A i))
  exact runsTo_mono (compileFO_ok gcdProg2_wf hex h hpc hc hok hra) fun s' ⟨h1, h2, h3⟩ =>
    ⟨h1, (h2 0).trans hv, h3⟩

/-- the same with `Nat.gcd` -/
theorem gcdO_ok_nat {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc gcdCodeO) (hok : codeOK pc gcdCodeO.length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      (getX s' 10).toNat = Nat.gcd (getX s 10).toNat (getX s 11).toNat ∧
      Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s' :=
  runsTo_mono (gcdO_ok h hpc hc hok hra) fun s' ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, gcdSub_toNat], h3⟩

end Proven
