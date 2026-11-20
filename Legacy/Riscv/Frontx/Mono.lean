/- `frontx_mono f at τ₁ … τₖ on T [using U…]`: monomorphisation of type variables (round 1, feature B; NOTES section 36).

`f : {ρ₁ … ρₖ : Type} → …` (leading type parameters, e.g. the register type of `Ir.Tst ρ`, `Mach.IR.Ins α`) is
specialised at the use site: generated

  `f.at_τ : <type of f with ρᵢ := τᵢ> := fun xs => @f τ₁ … τₖ xs`     (the specialised copy)
  `f.at_τ.eq : f.at_τ = @f τ₁ … τₖ`                                    (the equation to the original, `rfl`)

and the copy is compiled by `frontx_ind f.at_τ on T [using U…]` (the source of `f` is used verbatim, through its
own equations, with the type arguments fixed), which proves `f.at_τ.implements1`.  Through `.eq` this is the
statement about `@f τ₁ … τₖ`. -/
import Legacy.Riscv.Frontx.IndCmd

namespace Proven.Frontx.Mono
open Lean Meta Elab Command Term Proven.Frontx.IndCmd

/-- a name component for a type (`Nat` → `Nat`, `List Nat` → `List_Nat`) -/
def tyTag (e : Expr) : MetaM String := do
  let s := toString (← ppExpr e)
  return String.map (fun c => if c.isAlphanum then c else '_') s

syntax "frontx_mono " ident " at " term:max+ " on " ident (" using " ident+)? : command
elab_rules : command
  | `(frontx_mono $f:ident at $tys:term* on $T:ident $[using $Us*]?) => do
    let fN ← liftCoreM (realizeGlobalConstNoOverloadWithInfo f)
    let cN : Name × String × String ← liftTermElabM do
      let ci ← getConstInfo fN
      let tyEs ← tys.mapM fun t => do
        let e ← Term.elabType t
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
      let lvls := ci.levelParams.map mkLevelParam
      -- the leading type parameters
      forallBoundedTelescope ci.type tyEs.size fun ps _ => do
        unless ps.size == tyEs.size do throwError "frontx_mono: {fN} has fewer than {tyEs.size} parameters"
        for p in ps do
          unless (← inferType p).isSort do throwError "frontx_mono: parameter {p} of {fN} is not a type"
      let ty ← instantiateForall ci.type tyEs
      let tag := "_".intercalate (← tyEs.toList.mapM fun e => (tyTag e : MetaM String))
      let cN := fN ++ Name.mkSimple s!"at_{tag}"
      -- the text of the copy: explicit binders `(x_i : A_i)`, body `@f τ… x_i…`
      let (bs, rS, n) ← forallTelescope ty fun xs r => do
        let mut bs := ""
        for i in [0:xs.size] do bs := bs ++ s!" (x_{i} : {← ppFull (← inferType xs[i]!)})"
        return (bs, ← ppFull r, xs.size)
      let tysS ← tyEs.toList.mapM fun e => do return s!"({← ppFull e})"
      let args := " ".intercalate ((List.range n).map fun i => s!"x_{i}")
      return (cN, s!"def _root_.{cN}{bs} : {rS} := @{fN} {" ".intercalate tysS} {args}",
        s!"theorem _root_.{cN}.eq : @{cN} = @{fN} {" ".intercalate tysS} := rfl")
    let (cN, defS, eqS) := cN
    unless (← getEnv).contains cN do
      runCmd defS
      runCmd eqS
    -- visible caveat: fields that `frontx_ind_type` leaves out of the byte format (e.g. a `BitVec 64` immediate)
    let embN ← liftCoreM (realizeGlobalConstNoOverloadWithInfo (mkIdentFrom T (T.getId ++ `emb)))
    let mut tns := #[embN.getPrefix]
    for U in Us.getD #[] do
      tns := tns.push (← liftCoreM (realizeGlobalConstNoOverloadWithInfo (mkIdentFrom U (U.getId ++ `emb)))).getPrefix
    for tn in tns do
      for n in #[tn] ++ nestedNames (← getEnv) tn do
        let r ← liftTermElabM (rTyOfName n)
        for i in [0:r.ti.ctors.size] do
          if r.ti.roles[i]!.contains .drop then
            logWarning m!"frontx_mono: {r.ti.ctors[i]!} has a field that is not in the byte format of {n} (dropped by frontx_ind_type): the theorem is about an encoding that forgets it"
    let c := mkIdentFrom f cN
    elabCommand (← `(frontx_ind $c:ident on $T:ident $[using $Us*]?))

end Proven.Frontx.Mono
