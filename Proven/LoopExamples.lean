/- Two loops proved end to end: ordinary tail-recursive Lean functions, `Stmt` programs, proofs that the
programs compute the functions, and the machine theorems on the Sail model. -/
import Proven.Loop
open LeanRV64D

namespace Proven

/-! ## Generic facts about `Exec` -/

theorem Exec.det : ∀ {p : Stmt} {σ σ₁ σ₂ : Env}, Exec p σ σ₁ → Exec p σ σ₂ → σ₁ = σ₂
  | _, _, _, _, .assign, .assign => rfl
  | _, _, _, _, .seq a b, .seq a' b' => by cases Exec.det a a'; exact Exec.det b b'
  | _, _, _, _, .loopF _, .loopF _ => rfl
  | _, _, _, _, .loopF h, .loopT h' _ _ => absurd h h'
  | _, _, _, _, .loopT h _ _, .loopF h' => absurd h' h
  | _, _, _, _, .loopT _ b l, .loopT _ b' l' => by cases Exec.det b b'; exact Exec.det l l'

/-- Hoare-style loop rule with a user-supplied invariant `I` and measure `μ` -/
theorem Exec.loop_inv {c : Exp} {b : Stmt} (I Q : Env → Prop) (μ : Env → Nat)
    (hstep : ∀ σ, I σ → c.denote σ ≠ 0 → ∃ σ₁, Exec b σ σ₁ ∧ I σ₁ ∧ μ σ₁ < μ σ)
    (hexit : ∀ σ, I σ → c.denote σ = 0 → Q σ) : ∀ σ, I σ → ∃ σ', Exec (.loop c b) σ σ' ∧ Q σ' := by
  intro σ
  induction h : μ σ using Nat.strongRecOn generalizing σ with
  | ind n ih =>
    intro hI
    by_cases hc : c.denote σ = 0
    · exact ⟨σ, .loopF hc, hexit σ hI hc⟩
    · obtain ⟨σ₁, hb, hI₁, hlt⟩ := hstep σ hI hc
      obtain ⟨σ', hl, hQ⟩ := ih _ (h ▸ hlt) σ₁ rfl hI₁
      exact ⟨σ', .loopT hc hb hl, hQ⟩

theorem Exec.seq_assign {a : Stmt} {σ σ₁ : Env} (h : Exec a σ σ₁) (v : Fin 4) (e : Exp) :
    Exec (.seq a (.assign v e)) σ (σ₁.set v (e.denote σ₁)) := .seq h .assign

theorem sub_one_lt {n : BitVec 64} (h : n ≠ 0) : (n - 1).toNat < n.toNat := by
  have : n.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [BitVec.toNat_sub]; simp; omega

/-! ## (a) sum `n + (n-1) + ... + 1` (mod 2^64), counting down -/

def sumDown (n acc : BitVec 64) : BitVec 64 := if n = 0 then acc else sumDown (n - 1) (acc + n)
termination_by n.toNat
decreasing_by exact sub_one_lt ‹_›

/-- `0 + 1 + ... + n` mod 2^64 -/
def sum (n : BitVec 64) : BitVec 64 := sumDown n 0

open Exp in
/-- `while a0 ≠ 0 do (a1 := a1 + a0; a0 := a0 - 1); a0 := a1` -/
def sumProg : Stmt :=
  .seq (.loop (var 0) (.seq (.assign 1 (bin .add (var 1) (var 0))) (.assign 0 (bin .sub (var 0) (const 1)))))
    (.assign 0 (var 1))

theorem sumProg_exec (σ : Env) : ∃ σ', Exec sumProg σ σ' ∧ σ' 0 = sumDown (σ 0) (σ 1) := by
  obtain ⟨σ₁, hl, hq⟩ := Exec.loop_inv (c := .var 0)
    (b := .seq (.assign 1 (.bin .add (.var 1) (.var 0))) (.assign 0 (.bin .sub (.var 0) (.const 1))))
    (fun τ => sumDown (τ 0) (τ 1) = sumDown (σ 0) (σ 1)) (fun τ => τ 1 = sumDown (σ 0) (σ 1))
    (fun τ => (τ 0).toNat)
    (fun τ hI hc => ⟨_, .seq .assign .assign, by
      simp only [Exp.denote] at hc
      refine ⟨?_, ?_⟩
      · rw [← hI, sumDown.eq_def (τ 0), if_neg hc]; simp [Env.set, Exp.denote, Op.eval]
      · simp [Env.set, Exp.denote, Op.eval]; exact sub_one_lt hc⟩)
    (fun τ hI hc => by
      simp only [Exp.denote] at hc
      rw [← hI, sumDown.eq_def, if_pos hc])
    σ rfl
  exact ⟨_, .seq hl .assign, by simp [Env.set, Exp.denote, hq]⟩

/-! ## (b) gcd by repeated subtraction -/

def gcdSub (a b : BitVec 64) : BitVec 64 :=
  if a = 0 then b else if b = 0 then a else if a < b then gcdSub a (b - a) else gcdSub (a - b) b
termination_by a.toNat + b.toNat
decreasing_by
  all_goals have ha : a.toNat ≠ 0 := fun e => ‹¬a = 0› (BitVec.eq_of_toNat_eq (by simpa using e))
  all_goals have hb : b.toNat ≠ 0 := fun e => ‹¬b = 0› (BitVec.eq_of_toNat_eq (by simpa using e))
  · have := ‹a < b›; rw [BitVec.lt_def] at this; rw [BitVec.toNat_sub]; omega
  · have := ‹¬a < b›; rw [BitVec.lt_def] at this; rw [BitVec.toNat_sub]; omega

open Exp in
/-- `while (a0 ≠ 0 ∧ a1 ≠ 0) do (a2 := a0 <u a1; a1 := a2 ? a1 - a0 : a1; a0 := a2 ? a0 : a0 - a1);
a0 := a0 | a1` -/
def gcdProg : Stmt :=
  .seq (.loop (ite (var 0) (var 1) (const 0))
      (.seq (.assign 2 (bin .ult (var 0) (var 1)))
        (.seq (.assign 1 (ite (var 2) (bin .sub (var 1) (var 0)) (var 1)))
          (.assign 0 (ite (var 2) (var 0) (bin .sub (var 0) (var 1)))))))
    (.assign 0 (bin .or (var 0) (var 1)))

theorem gcdProg_exec (σ : Env) : ∃ σ', Exec gcdProg σ σ' ∧ σ' 0 = gcdSub (σ 0) (σ 1) := by
  obtain ⟨σ₁, hl, hq⟩ := Exec.loop_inv (c := Exp.ite (.var 0) (.var 1) (.const 0))
    (b := .seq (.assign 2 (.bin .ult (.var 0) (.var 1)))
        (.seq (.assign 1 (.ite (.var 2) (.bin .sub (.var 1) (.var 0)) (.var 1)))
          (.assign 0 (.ite (.var 2) (.var 0) (.bin .sub (.var 0) (.var 1))))))
    (fun τ => gcdSub (τ 0) (τ 1) = gcdSub (σ 0) (σ 1)) (fun τ => τ 0 ||| τ 1 = gcdSub (σ 0) (σ 1))
    (fun τ => (τ 0).toNat + (τ 1).toNat)
    (fun τ hI hc => ⟨_, .seq .assign (.seq .assign .assign), by
      have ha : τ 0 ≠ 0 := fun e => hc (by simp [Exp.denote, e])
      have hb : τ 1 ≠ 0 := fun e => hc (by simp [Exp.denote, e])
      have ha' : (τ 0).toNat ≠ 0 := fun e => ha (BitVec.eq_of_toNat_eq (by simpa using e))
      have hb' : (τ 1).toNat ≠ 0 := fun e => hb (BitVec.eq_of_toNat_eq (by simpa using e))
      rw [← hI, gcdSub.eq_def (τ 0), if_neg ha, if_neg hb]
      by_cases hlt : τ 0 < τ 1
      · simp [Env.set, Exp.denote, Op.eval, hlt]
        rw [BitVec.lt_def] at hlt; omega
      · simp [Env.set, Exp.denote, Op.eval, hlt]
        rw [BitVec.lt_def] at hlt; omega⟩)
    (fun τ hI hc => by
      rw [← hI, gcdSub.eq_def]
      by_cases ha : τ 0 = 0
      · simp [ha]
      · have hb : τ 1 = 0 := by simp [Exp.denote] at hc; exact hc ha
        simp [ha, hb])
    σ rfl
  exact ⟨_, .seq hl .assign, by simp [Env.set, Exp.denote, Op.eval, hq]⟩

/-! ## Machine theorems -/

theorem sumProg_wf : sumProg.wf := by simp only [sumProg, Stmt.wf]; decide +kernel
theorem gcdProg_wf : gcdProg.wf := by simp only [gcdProg, Stmt.wf]; decide +kernel

/-- `compileF sumProg`, called with `a0 = n`, `a1 = acc`, returns `sumDown n acc` in `a0`
(so `sum n` when `a1 = 0`). -/
theorem sum_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileF sumProg)) (hok : codeOK pc (compileF sumProg).length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 10 = sumDown (getX s 10) (getX s 11) ∧
      Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s' := by
  obtain ⟨σ', hex, hv⟩ := sumProg_exec (fun i => getX s (A i))
  exact runsTo_mono (compileF_ok sumProg_wf hex h hpc hc hok hra) fun s' ⟨h1, h2, h3⟩ =>
    ⟨h1, (h2 0).trans hv, h3⟩

/-- `compileF gcdProg`, called with `a0 = a`, `a1 = b`, returns `gcdSub a b` in `a0`. -/
theorem gcd_ok {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileF gcdProg)) (hok : codeOK pc (compileF gcdProg).length)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ getX s' 10 = gcdSub (getX s 10) (getX s 11) ∧
      Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s' := by
  obtain ⟨σ', hex, hv⟩ := gcdProg_exec (fun i => getX s (A i))
  exact runsTo_mono (compileF_ok gcdProg_wf hex h hpc hc hok hra) fun s' ⟨h1, h2, h3⟩ =>
    ⟨h1, (h2 0).trans hv, h3⟩

end Proven
