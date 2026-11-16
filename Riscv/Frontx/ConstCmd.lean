/- `frontx_const f [on T]`: a 0-ary definition folded at compile time and emitted as data (NOTES section 35).

1. `f` must have no arguments (a function is never folded).
2. The result encoding: `Nat` = 64-bit word (`encWord`, with the theorem `f < 2^64`), `Fin k` (`k ≤ 256`) = one byte,
   a type declared by `frontx_ind_type T` (`on T`: the root or a nested type of `T`) = its `enc`, else a `Bytes`
   instance.  The input: `T`'s root with `T.enc` (`on T`), else raw bytes; it is ignored.
3. Candidate bytes `encB f` by evaluation (untrusted; at most `capBytes` of them, else rejected).
4. The KERNEL checks `encB f = bytes` (the only trusted step; a well-founded definition that does not reduce, or a
   value over the budget, fails here) (`decide`, a proof `of_decide_eq_true rfl` added with `addDecl` under the
   heartbeat budget `kernelBudget`).  Failure: rejected.
5. Generated: `f.data.enc_eq`, `f.data.code`, `f.data.implements1` (from `data_implements1`), for `Nat` `f.data.lt`. -/
import Riscv.Frontx.Const
import Riscv.Frontx.IndCmd

namespace Proven.Frontx.ConstCmd
open Lean Meta Elab Command Term Proven.Frontx.IndCmd

/-- heartbeats (in thousands) for the kernel's check of the equation -/
def kernelBudget : Nat := 50000

/-- the encoder of the result type (text), and whether it is `Nat` (word) -/
def encOf (ty : Expr) (Tn? : Option Name) : MetaM (String × Bool × Option Name) := do
  let ty' ← whnfR ty
  if ty'.isConstOf ``Nat then return ("Proven.Frontx.Const.encWord", true, none)
  if ty'.isAppOfArity ``Fin 1 then
    let some k := (← whnf ty'.appArg!).rawNatLit? | throwError "frontx_const: `Fin` of a non-literal size"
    unless k ≤ 256 do throwError "frontx_const: `Fin {k}` does not fit a byte"
    return ("Proven.Frontx.Const.encFin", false, none)
  if let some Tn := Tn? then
    for n in #[Tn] ++ nestedNames (← getEnv) Tn do
      let d := (← inferType (← mkConstWithLevelParams (n ++ `emb))).bindingDomain!
      if ← isDefEq d ty then return (s!"{n}.enc", false, some n)
  if (← synthInstance? (mkApp (mkConst ``Proven.Bytes) ty)).isSome then return ("Proven.Bytes.enc", false, none)
  throwError "frontx_const: no encoding for the result type {ty}"

def elabT (s : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term s | throwError "frontx_const: does not parse: {s}"
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- add `name : prop` with the proof `of_decide_eq_true rfl`, checked by the kernel under `kernelBudget` -/
def addDecideThm (name : Name) (propS : String) : CommandElabM Unit := do
  liftTermElabM do
    let p ← elabT propS
    let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
    let pf := mkApp3 (mkConst ``of_decide_eq_true) p inst (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    withOptions (fun o => (maxHeartbeats.set o kernelBudget).setBool `Elab.async false) do
      withTheReader Core.Context (fun c => { c with maxHeartbeats := kernelBudget * 1000 }) do
        try addDecl (.thmDecl { name, levelParams := [], type := p, value := pf })
        catch ex => throwError "frontx_const: the kernel does not confirm{indentExpr p}\n({ex.toMessageData})" 

syntax "frontx_const " ident (" on " ident)? : command
elab_rules : command
  | `(frontx_const $f:ident $[on $T:ident]?) => do
    let fN ← liftCoreM (realizeGlobalConstNoOverloadWithInfo f)
    let Tn? ← T.mapM fun T => do
      return (← liftCoreM (realizeGlobalConstNoOverloadWithInfo (mkIdentFrom T (T.getId ++ `emb)))).getPrefix
    let (encB, isNat, kn, bytes, encA, inTy) ← liftTermElabM do
      let ci ← getConstInfo fN
      unless ci.levelParams.isEmpty do throwError "frontx_const: {fN} is universe polymorphic"
      if (← whnfR ci.type).isForall then throwError "frontx_const: {fN} has arguments; only 0-ary definitions are folded"
      let (encB, isNat, kn) ← encOf ci.type Tn?
      let e ← elabT s!"({encB} {fN} : List UInt8)"
      -- candidate bytes by evaluation (untrusted: the kernel checks them below)
      let bytes := (← unsafe Meta.evalExpr (List UInt8) (mkApp (mkConst ``List [0]) (mkConst ``UInt8)) e).toArray.map (·.toNat)
      unless bytes.size ≤ Proven.Frontx.Const.capBytes do
        throwError "frontx_const: {bytes.size} bytes, over the cap of {Proven.Frontx.Const.capBytes}" 
      let (encA, inTy) ← match Tn? with
        | some Tn => pure (s!"{Tn}.enc", ← ppFull (← inferType (← mkConstWithLevelParams (Tn ++ `emb))).bindingDomain!)
        | none => pure ("Proven.Frontx.Const.encIn", "List UInt8")
      return (encB, isNat, kn, bytes, encA, inTy)
    let ys := "[" ++ ", ".intercalate (bytes.toList.map toString) ++ "]"
    if isNat then addDecideThm (fN ++ `data ++ `lt) s!"{fN} < 2 ^ 64"
    match kn, Tn? with
    | some kn, some Tn =>
      -- a declared type: the kernel checks the structural form `encS` (`C.sb` is well-founded)
      addDecideThm (fN ++ `data ++ `encS_eq)
        s!"Proven.Frontx.Const.encS {Tn}.sh ({kn}.emb {fN}) = ({ys} : List UInt8)"
      runCmd s!"theorem _root_.{fN}.data.enc_eq : ({encB} {fN} : List UInt8) = ({ys} : List UInt8) :=
  Proven.Frontx.Const.enc_of_encS {fN}.data.encS_eq"
    | _, _ => addDecideThm (fN ++ `data ++ `enc_eq) s!"({encB} {fN} : List UInt8) = ({ys} : List UInt8)"
    let d := fN ++ `data
    runCmd s!"def _root_.{d}.bytes : List UInt8 := {ys}"
    runCmd s!"def _root_.{d}.code : List (BitVec 32) := Proven.Mach.Riscv.rvF.codeF (Proven.Mach.Riscv.rvF.compBF 0 [0, 3] [2] (Proven.Frontx.Const.dataB {d}.bytes))"
    runCmd s!"theorem _root_.{d}.implements1 : Proven.Implements1With {encA} {encB} {d}.code (fun (_ : {inTy}) => {fN}) (fun _ => 15) (2 ^ 20) true :=
  Proven.Frontx.Const.data_implements1 {encA} {encB} {fN} {d}.bytes {d}.enc_eq (2 ^ 20) true"
    logInfo m!"frontx_const: {fN}: {bytes.size} bytes as data"

end Proven.Frontx.ConstCmd
