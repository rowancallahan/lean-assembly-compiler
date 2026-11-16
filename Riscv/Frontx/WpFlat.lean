/- Paged arrays (NOTES section 35): flat guards.  A paged program guards each stage by `vOk` (`guard S =
v8 := vOk; while v8 { S; v8 := 0 }`), and the next stage sits inside the guard of the one before, so the outermost
guard's loop body is the whole rest of the program; the back end's loop exit is a 12-bit branch (`wfB`: bodies below
about 1000 instructions).  `flatG` rewrites `guard (A; guard B)` into `guard A; guard B` everywhere: the same
result (`flatG_exec`), and each guard's body is one stage. -/
import Riscv.Frontx.WaExp

namespace Proven.WA
open Proven.Mach

/-- `guard Y` -/
def guardS (Y : Mach.BStmt) : Mach.BStmt :=
  .seq (.assign 8 (.var 7)) (.loop (.var 8) (.seq Y (.assign 8 (.const 0))))

/-- one level of `guard (A; guard B) ⇒ guard A; guard B`, with `f` on the parts -/
def flatStep (f : Mach.BStmt → Mach.BStmt) : Mach.BStmt → Mach.BStmt
  | .seq (.assign 8 (.var 7)) (.loop (.var 8) (.seq (.seq A (.seq (.assign 8 (.var 7))
      (.loop (.var 8) (.seq B (.assign 8 (.const z1)))))) (.assign 8 (.const z2)))) =>
    if z1 = 0 ∧ z2 = 0 then
      .seq (guardS (f A)) (f (.seq (.assign 8 (.var 7)) (.loop (.var 8) (.seq B (.assign 8 (.const 0))))))
    else .seq (.assign 8 (.var 7)) (.loop (.var 8) (f (.seq (.seq A (.seq (.assign 8 (.var 7))
      (.loop (.var 8) (.seq B (.assign 8 (.const z1)))))) (.assign 8 (.const z2)))))
  | .seq p q => .seq (f p) (f q)
  | .loop c b => .loop c (f b)
  | s => s

/-- `flatStep` to depth `n` (structural on `n`, so that `decide` reduces it; at depth 0 nothing changes) -/
def flatGF : Nat → Mach.BStmt → Mach.BStmt
  | 0, p => p
  | n + 1, p => flatStep (flatGF n) p

def flatG (p : Mach.BStmt) : Mach.BStmt := flatGF 1000 p

theorem set_same (env : Mach.BEnv) (v : Nat) : env.set v (env v) = env := by
  funext j; simp only [Mach.BEnv.set]; split <;> simp_all

theorem set_set (env : Mach.BEnv) (v : Nat) (a b : BitVec 64) : (env.set v a).set v b = env.set v b := by
  funext j; simp only [Mach.BEnv.set]; split <;> simp_all

theorem set_eq' (env : Mach.BEnv) (v : Nat) (a : BitVec 64) : env.set v a v = a := by simp [Mach.BEnv.set]

theorem set_ne' (env : Mach.BEnv) {v j : Nat} (a : BitVec 64) (h : j ≠ v) : env.set v a j = env j := by
  simp [Mach.BEnv.set, h]

/-- a loop whose body ends with `v8 := 0` runs at most once and ends with `v8 = 0` -/
theorem when8_exec {S : Mach.BStmt} {σ σ' : Mach.BState} (h : Mach.BExec (.loop (.var 8) (.seq S (.assign 8 (.const 0)))) σ σ') :
    (σ.env 8 = 0 ∧ σ' = σ) ∨ (σ.env 8 ≠ 0 ∧ ∃ σ₁, Mach.BExec S σ σ₁ ∧ σ' = ⟨σ₁.env.set 8 0, σ₁.heap, σ₁.wheap⟩) := by
  cases h with
  | loopF hc => exact .inl ⟨hc, rfl⟩
  | loopT hc hb hl =>
    cases hb with
    | seq hS ha =>
      cases ha
      cases hl with
      | loopF _ => exact .inr ⟨hc, _, hS, rfl⟩
      | loopT hc2 _ _ => exact absurd (by simp [Mach.BExp.denote, set_eq']) hc2

theorem when8_of {S : Mach.BStmt} {σ σ₁ : Mach.BState} (hc : σ.env 8 ≠ 0) (hS : Mach.BExec S σ σ₁) :
    Mach.BExec (.loop (.var 8) (.seq S (.assign 8 (.const 0)))) σ ⟨σ₁.env.set 8 0, σ₁.heap, σ₁.wheap⟩ := by
  refine .loopT hc (.seq hS .assign) (.loopF ?_)
  simp [Mach.BExp.denote, set_eq']

theorem when8_skip {S : Mach.BStmt} {σ : Mach.BState} (hc : σ.env 8 = 0) :
    Mach.BExec (.loop (.var 8) (.seq S (.assign 8 (.const 0)))) σ σ := .loopF hc

theorem when8_zero {S : Mach.BStmt} {σ σ' : Mach.BState} (h : Mach.BExec (.loop (.var 8) (.seq S (.assign 8 (.const 0)))) σ σ') :
    σ'.env 8 = 0 := by
  rcases when8_exec h with ⟨hc, rfl⟩ | ⟨-, σ₁, -, rfl⟩
  · exact hc
  · show σ₁.env.set 8 0 8 = 0; exact set_eq' _ _ _

theorem state_fix {σ : Mach.BState} (h : σ.env 8 = 0) : (⟨σ.env.set 8 0, σ.heap, σ.wheap⟩ : Mach.BState) = σ := by
  rw [← h, set_same]

/-- the guard rewrite, one level -/
theorem guard_flat {A A' G' B : Mach.BStmt} {σ σ' : Mach.BState}
    (h : Mach.BExec (.seq (.assign 8 (.var 7)) (.loop (.var 8) (.seq (.seq A (.seq (.assign 8 (.var 7))
      (.loop (.var 8) (.seq B (.assign 8 (.const 0)))))) (.assign 8 (.const 0))))) σ σ')
    (hA : ∀ σ σ', Mach.BExec A σ σ' → Mach.BExec A' σ σ')
    (hG : ∀ σ σ', Mach.BExec (.seq (.assign 8 (.var 7)) (.loop (.var 8) (.seq B (.assign 8 (.const 0))))) σ σ' →
      Mach.BExec G' σ σ') :
    Mach.BExec (.seq (.seq (.assign 8 (.var 7)) (.loop (.var 8) (.seq A' (.assign 8 (.const 0))))) G') σ σ' := by
  cases h with
  | seq h1 h2 =>
    cases h1
    rcases when8_exec h2 with ⟨hc, rfl⟩ | ⟨hc, σ₁, hS, rfl⟩
    · -- `vOk = 0`: nothing runs
      refine .seq (.seq .assign (when8_skip hc)) (hG _ _ ?_)
      refine .seq .assign ?_
      simp only [Mach.BExp.denote, set_ne' _ _ (show (7 : Nat) ≠ 8 by decide), set_set] at hc ⊢
      exact when8_skip hc
    · cases hS with
      | seq hA1 hrest =>
        cases hrest with
        | seq ha hw =>
          cases ha
          refine .seq (.seq .assign (when8_of hc (hA _ _ hA1))) (hG _ _ ?_)
          have hz := when8_zero hw
          refine .seq .assign ?_
          simp only [Mach.BExp.denote, set_ne' _ _ (show (7 : Nat) ≠ 8 by decide), set_set]
          simp only [Mach.BExp.denote] at hw
          rw [state_fix hz]
          exact hw

theorem loop_mono {c : Mach.BExp} {b b' : Mach.BStmt} (hb : ∀ σ σ', Mach.BExec b σ σ' → Mach.BExec b' σ σ')
    {σ σ' : Mach.BState} (h : Mach.BExec (.loop c b) σ σ') : Mach.BExec (.loop c b') σ σ' := by
  generalize hl : Mach.BStmt.loop c b = l at h
  induction h with
  | loopF hc => cases hl; exact .loopF hc
  | loopT hc h1 _ _ ih2 => cases hl; exact .loopT hc (hb _ _ h1) (ih2 rfl)
  | _ => cases hl

theorem guardS_mono' {X Y : Mach.BStmt} (h : ∀ σ σ', Mach.BExec X σ σ' → Mach.BExec Y σ σ') {σ σ' : Mach.BState}
    (hx : Mach.BExec (guardS X) σ σ') : Mach.BExec (guardS Y) σ σ' := by
  cases hx with
  | seq h1 h2 => exact .seq h1 (loop_mono (fun _ _ hb => by
      cases hb with
      | seq hb1 hb2 => exact .seq (h _ _ hb1) hb2) h2)

theorem flatStep_exec {f : Mach.BStmt → Mach.BStmt}
    (hf : ∀ (p : Mach.BStmt) {σ σ' : Mach.BState}, Mach.BExec p σ σ' → Mach.BExec (f p) σ σ')
    (p : Mach.BStmt) {σ σ' : Mach.BState} (h : Mach.BExec p σ σ') : Mach.BExec (flatStep f p) σ σ' := by
  unfold flatStep
  split
  · next A B z1 z2 =>
    split
    · next hz =>
      obtain ⟨rfl, rfl⟩ := hz
      exact guard_flat h (fun _ _ ha => hf A ha) (fun _ _ hg => hf _ hg)
    · cases h with
      | seq h1 h2 => exact .seq h1 (loop_mono (fun _ _ hb => hf _ hb) h2)
  · next p q _ =>
    cases h with
    | seq h1 h2 => exact .seq (hf p h1) (hf q h2)
  · next c b => exact loop_mono (fun _ _ hb => hf b hb) h
  · exact h

theorem flatGF_exec : ∀ n (p : Mach.BStmt) {σ σ' : Mach.BState}, Mach.BExec p σ σ' → Mach.BExec (flatGF n p) σ σ'
  | 0, _, _, _, h => h
  | n + 1, p, _, _, h => flatStep_exec (flatGF_exec n) p h

theorem flatG_exec (p : Mach.BStmt) {σ σ' : Mach.BState} (h : Mach.BExec p σ σ') : Mach.BExec (flatG p) σ σ' :=
  flatGF_exec _ p h

end Proven.WA
