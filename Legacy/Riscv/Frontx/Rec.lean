/- Non-tail recursion with real calls: from generated pieces to `Implements1`, once.

* `piece_lift`: a generated program `q` (a `Proven.BStmt` whose assigned variables are all `≥ S`), preceded by
  copies `l` into its parameter variables, run inside a function with more blocks: its result in `v_S`, every
  variable below `S` kept (the hypotheses `hGO`/`hARG`/`hCOMB` of `rec_ok`, `Compiler/Rec.lean`).
* `implements1_rec`: the entry function `main := (v4 := fi(args); store the result bytes)` of a program `P`
  (plain back end `compP`, `Riscv/Back/CallsImpl1.lean`) ⇒ `Implements1` with `space n = need n + 32`. -/
import Legacy.Compiler.Rec
import Legacy.Riscv.Back.CallsImpl1
import Legacy.Riscv.Frontx.Impl1
import Legacy.Riscv.Frontx.For

set_option linter.unusedVariables false

namespace Proven.Frontx
open Proven Proven.Mach Proven.Mach.Riscv LeanRV64D

theorem piece_lift {q : Proven.BStmt} {l : List (Nat × Proven.BExp)} {S : Nat}
    (hq : ∀ v ∈ (initS l q).assigns, S ≤ v) {E : Mach.BEnv} {H0 X : Heap} {W : Mach.WHeap} {x : BitVec 64}
    (hrun : ∃ σ', Proven.BExec q ⟨seqSet E l, H0⟩ σ' ∧ σ'.env S = x ∧ σ'.heap = H0) :
    ∃ E', Mach.BExec (toMS (initS l q)) ⟨E, H0 ++ X, W⟩ ⟨E', H0 ++ X, W⟩ ∧ E' S = x ∧
      ∀ v, v < S → E' v = E v := by
  obtain ⟨σ', hx, h1, h2⟩ := hrun
  have hx' := initS_exec l E hx
  refine ⟨σ'.env, by have := exec_up hx' X W; rw [h2] at this; exact this, h1, fun v hv => ?_⟩
  exact Proven.BExec.env_keep hx' (fun hm => by have := hq v hm; omega)

theorem rB_ne (b : Bool) : rB b ≠ 0 ↔ b = true := by cases b <;> decide

/-- the entry function: `v4 := fi(args)`, then the `k + 1` result bytes to the output block -/
def recMain (fi : Nat) (args : List Mach.BExp) (k : Nat) : Fn :=
  ⟨0, 0, .seq (.call 4 fi args) (.base (store8 k)), .var 4⟩

/-- **Generated recursive program ⇒ `Implements1`.** -/
theorem implements1_rec {β : Type} [Res β] (g : ByteArray → β) (P : Prog) (main fi : Nat) (args : List Mach.BExp)
    (hm : main < P.length) (hP : P[main] = recMain fi args (Res.k β)) (hwf : WfProg1 P 4 main) (need : Nat → Nat)
    (hcall : ∀ (xs : ByteArray) (out : List (BitVec 8)) (env : Mach.BEnv), env 1 = rN xs.size →
      xs.size < 2 ^ 32 →
      CExec P (need xs.size) (.call 4 fi args) ⟨env, [blk xs, out], []⟩ ⟨env.set 4 (Res.repr (g xs)), [blk xs, out], []⟩) :
    Implements1With (fun xs : ByteArray => xs.data.toList) Res.enc (callsCode1 P 4 main) g (fun n => need n + 8 + 24) := by
  refine implements1_of_cexec _ Res.enc g P 4 main hwf (by decide) (fun n => need n + 8) _ false ?_
  intro a out env h1 hmax hlt hol hout
  have hsz : a.data.toList.length = a.size := Array.length_toList
  rw [hsz] at h1 hlt ⊢
  have hc := hcall a out (Mach.callEnv env []) (by simp only [Mach.callEnv]; exact h1) hlt
  have hlen : (Res.enc (g a)).length = Res.k β + 1 := by
    have := congrArg List.length (Res.henc (g a)); simpa using this
  rw [hlen] at hol ⊢
  obtain ⟨out', hst, hl', hb', hu⟩ := store8_exec (Res.repr (g a)) (Res.k β) Res.hk
    ⟨(Mach.callEnv env []).set 4 (Res.repr (g a)), [blk a, out], []⟩ _ out rfl (by simp [Mach.BEnv.set]) (by omega) rfl
  have hb := CExec.call (P := P) (res := 4) (args := []) (σ := ⟨env, [blk a, out], []⟩) (k := need a.size + 8)
    (k' := need a.size) hm (by rw [hP]; rfl) (by rw [hP]; simp [recMain, Fn.frame]; omega)
    (by rw [hP]; exact .seq hc (.base hst))
  refine ⟨_, out', hb, rfl, ?_, ?_, fun h => nomatch h⟩
  · apply List.ext_getElem?; intro i
    rw [Res.henc]
    by_cases hi : i < Res.k β + 1
    · rw [List.getElem?_take_of_lt hi, hb' i (by omega), List.getElem?_map, List.getElem?_range hi]; rfl
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  · exact List.ext_getElem? fun i => by rw [List.getElem?_drop, List.getElem?_drop]; exact hu _ (by omega)

end Proven.Frontx
