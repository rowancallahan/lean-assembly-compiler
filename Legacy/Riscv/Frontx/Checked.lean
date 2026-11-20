/- Entry points whose plain fallback words are not well-formed (a loop body over 1024 plain words, e.g.
`tinyCompile`): the optimised words `compBFC` for a register choice found at elaboration time (`pickC`) and checked by
the kernel (`optB` accepts it, `decide +kernel`); no `wf`.  Same `Implements1With` shape as `frontx_implements_list`. -/
import Legacy.Riscv.Frontx.Impl1

set_option linter.unusedVariables false

namespace Proven.Frontx
open Lean Elab Command Term Proven Proven.Mach Proven.Mach.Riscv

/-- a register table with `Nat` registers -/
def toTbl (l : List (Nat × Nat)) : List (Nat × Reg) := l.map fun q => (q.1, rk q.2)

/-- the program `listCode` compiles -/
def listProg (p : Proven.BStmt) : Mach.BStmt := .seq (toMS p) (.assign 1 (.var 4))

/-- the checked words of an entry point with a list result -/
def listCodeC (N : Nat) (t : List (Nat × Nat)) (spl : List Nat) (p : Proven.BStmt) : List (BitVec 32) :=
  compBFC N [0, 3] [2] (toTbl t) spl (listProg p)

/-- **Generated program with a list result ⇒ `Implements1` with `retLen`, checked words.** -/
theorem implements1_listC (f : ByteArray → List UInt8) (N : Nat) (hN : N ≤ NS) (p : Proven.BStmt)
    (t : List (Nat × Nat)) (spl : List Nat)
    (hc : (rvwF.optB scB (tblG (toTbl t)) (fun j => spl.contains j) N [0, 3] [2] (listProg p)).isSome = true)
    (hex : ∀ (xs : ByteArray) (out : List (BitVec 8)) (env : BEnv), env 1 = rN xs.size → xs.size < 2 ^ 32 →
      (∀ j, 8 ≤ j → env j = 0) → (f xs).length ≤ out.length → out.length < 2 ^ 32 →
      ∃ σ', Proven.BExec p ⟨env, [blk xs, out]⟩ σ' ∧ σ'.env 4 = rN (f xs).length ∧
        σ'.heap = [blk xs, wrO out 0 (f xs)]) :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (listCodeC N t spl p) f
      (fun _ => 8 * (N + 1) + 7) (retLen := true) := by
  refine implements1_of_execC _ (fun l => l) f N hN (listProg p) _ _ hc (fun _ => 0) _
    (fun n => by (try dsimp only); omega) _ true ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  have hsz : a.data.toList.length = a.size := Array.length_toList
  obtain ⟨σ', hx, h4, hh⟩ := hex a out env (by rw [h1, hsz]; rfl) (by rw [← hsz]; exact hlt) h8 hout hol
  have hx' := exec_up hx [] [tbl]
  rw [hh] at hx'
  simp only [List.append_nil] at hx'
  refine ⟨_, wrO out 0 (f a), .seq hx' .assign, rfl, wrO_take _ _ hout, wrO_drop _ _, fun _ => ?_⟩
  show (σ'.env.set 1 _) 1 = _
  simp only [Mach.BEnv.set, Mach.BExp.denote]
  rw [h4]; rfl

/-- the choice for `listProg p` with `Nat` registers (untrusted) -/
def pickListC (N : Nat) (p : Proven.BStmt) : Option (List (Nat × Nat) × List Nat) :=
  (pickC N [0, 3] [2] (listProg p)).map fun (t, spl) => (t.map fun q => (q.1, q.2.val), spl)

unsafe def evalChoiceU (stx : Syntax) : TermElabM (Option (List (Nat × Nat) × List Nat)) := do
  Term.evalTerm _ (← Term.elabType (← `(Option (List (Nat × Nat) × List Nat)))) stx
@[implemented_by evalChoiceU] opaque evalChoice (stx : Syntax) : TermElabM (Option (List (Nat × Nat) × List Nat))

/-- `frontx_implements_listC g` (after `frontx_entry g`, list result): `g.tbl`, `g.spl`, `g.code` and
`g.implements1` (`retLen := true`), the words checked by the kernel instead of `wf` -/
elab "frontx_implements_listC " g:ident : command => do
  let n := g.getId
  let prog := mkIdent (n ++ `prog); let slots := mkIdent (n ++ `slots)
  let exec := mkIdent (n ++ `exec); let code := mkIdent (n ++ `code)
  let tbl := mkIdent (n ++ `tbl); let spl := mkIdent (n ++ `spl)
  let thm := mkIdent (n ++ `implements1)
  let some (t, sp) ← liftTermElabM (evalChoice (← `(pickListC $slots $prog)))
    | throwError "frontx_implements_listC: no register choice passed optB"
  let ts ← t.toArray.mapM fun (a, b) => `(($(quote a), $(quote b)))
  let ss : Array Term := sp.toArray.map fun j => quote j
  elabCommand (← `(def $tbl : List (Nat × Nat) := [$ts,*]))
  elabCommand (← `(def $spl : List Nat := [$ss,*]))
  elabCommand (← `(def $code : List (BitVec 32) := listCodeC $slots $tbl $spl $prog))
  elabCommand (← `(theorem $thm : Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) $code $g
        (fun _ => 8 * ($slots + 1) + 7) (retLen := true) :=
      implements1_listC $g $slots (by decide) $prog $tbl $spl (by decide +kernel) $exec))

/-! ## Scalar results with checked words (programs with `BStmt.mop`, NOTES section 22: no plain fallback) -/

/-- the program `entryCode` compiles -/
def resProg (β : Type) [Res β] (p : Proven.BStmt) : Mach.BStmt := .seq (toMS p) (store8 (Res.k β))

def resCodeC (β : Type) [Res β] (N : Nat) (t : List (Nat × Nat)) (spl : List Nat) (p : Proven.BStmt) :
    List (BitVec 32) :=
  compBFC N [0, 3] [2] (toTbl t) spl (resProg β p)

/-- **Generated program with a scalar result ⇒ `Implements1`, checked words.** -/
theorem implements1_resC {β : Type} [Res β] (f : ByteArray → β) (N : Nat) (hN : N ≤ NS) (p : Proven.BStmt)
    (t : List (Nat × Nat)) (spl : List Nat)
    (hc : (rvwF.optB scB (tblG (toTbl t)) (fun j => spl.contains j) N [0, 3] [2] (resProg β p)).isSome = true)
    (hex : ∀ (xs : ByteArray) (env : BEnv), env 1 = rN xs.size → xs.size < 2 ^ 32 → (∀ j, 8 ≤ j → env j = 0) →
      ∃ σ', Proven.BExec p ⟨env, [blk xs]⟩ σ' ∧ σ'.env 4 = Res.repr (f xs) ∧ σ'.heap = [blk xs]) :
    Implements1With (fun xs : ByteArray => xs.data.toList) Res.enc (resCodeC β N t spl p) f
      (fun _ => 8 * (N + 1) + 7) := by
  have hk := Res.hk (β := β)
  refine implements1_of_execC _ Res.enc f N hN (resProg β p) _ _ hc (fun _ => 0) _
    (fun n => by (try dsimp only); omega) _ false ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  have hsz : a.data.toList.length = a.size := Array.length_toList
  obtain ⟨σ', hx, h4, hh⟩ := hex a env (by rw [h1, hsz]; rfl) (by rw [← hsz]; exact hlt) h8
  have hx' := exec_up hx [out] [tbl]
  rw [hh] at hx'
  have hlen : (Res.enc (f a)).length = Res.k β + 1 := by
    have := congrArg List.length (Res.henc (f a)); simpa using this
  rw [hlen] at hout ⊢
  obtain ⟨out', hst, hl', hb', hu⟩ := store8_exec (Res.repr (f a)) (Res.k β) hk ⟨σ'.env, [blk a, out], [tbl]⟩ _ out
    rfl h4 (by omega) rfl
  refine ⟨_, out', .seq hx' hst, rfl, ?_, ?_, fun h => nomatch h⟩
  · apply List.ext_getElem?; intro i
    rw [Res.henc]
    by_cases hi : i < Res.k β + 1
    · rw [List.getElem?_take_of_lt hi, hb' i (by omega), List.getElem?_map, List.getElem?_range hi]; rfl
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  · exact List.ext_getElem? fun i => by rw [List.getElem?_drop, List.getElem?_drop]; exact hu _ (by omega)

/-- the choice for `resProg β p` with `Nat` registers (untrusted) -/
def pickResC (β : Type) [Res β] (N : Nat) (p : Proven.BStmt) : Option (List (Nat × Nat) × List Nat) :=
  (pickC N [0, 3] [2] (resProg β p)).map fun (t, spl) => (t.map fun q => (q.1, q.2.val), spl)

def pickResCOf {β : Type} [Res β] (_f : ByteArray → β) (N : Nat) (p : Proven.BStmt) :
    Option (List (Nat × Nat) × List Nat) := pickResC β N p
def resCodeCOf {β : Type} [Res β] (_f : ByteArray → β) (N : Nat) (t : List (Nat × Nat)) (spl : List Nat)
    (p : Proven.BStmt) : List (BitVec 32) := resCodeC β N t spl p

/-- `frontx_implementsC g` (after `frontx_entry g`, scalar result): `g.tbl`, `g.spl`, `g.code` and `g.implements1`,
the words checked by the kernel instead of `wf` (needed for multiply / divide, `BStmt.mop`) -/
elab "frontx_implementsC " g:ident : command => do
  let n := g.getId
  let prog := mkIdent (n ++ `prog); let slots := mkIdent (n ++ `slots)
  let exec := mkIdent (n ++ `exec); let code := mkIdent (n ++ `code)
  let tbl := mkIdent (n ++ `tbl); let spl := mkIdent (n ++ `spl)
  let thm := mkIdent (n ++ `implements1)
  let some (t, sp) ← liftTermElabM (evalChoice (← `(pickResCOf $g $slots $prog)))
    | throwError "frontx_implementsC: no register choice passed optB"
  let ts ← t.toArray.mapM fun (a, b) => `(($(quote a), $(quote b)))
  let ss : Array Term := sp.toArray.map fun j => quote j
  elabCommand (← `(def $tbl : List (Nat × Nat) := [$ts,*]))
  elabCommand (← `(def $spl : List Nat := [$ss,*]))
  elabCommand (← `(def $code : List (BitVec 32) := resCodeCOf $g $slots $tbl $spl $prog))
  elabCommand (← `(theorem $thm : Implements1With (fun xs : ByteArray => xs.data.toList) Res.enc $code $g
        (fun _ => 8 * ($slots + 1) + 7) :=
      implements1_resC $g $slots (by decide) $prog $tbl $spl (by decide +kernel) $exec))

end Proven.Frontx
