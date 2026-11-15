/- `frontx_ind_type T := ty` and `frontx_ind f on T`: user inductives compiled as cells (`Riscv/Frontx/Ind.lean`).

`frontx_ind_type T := ty` (`ty` an inductive type, e.g. `BinTree Nat`): per constructor (tag = its index) the fields
in declaration order; a field of type `ty` is a child (`l`, then `r`; at most two), a `Nat` / `UInt64` / `Bool`
field the scalar `x` (at most one), any other field is DROPPED (not in the byte format; a function reading it is
rejected).  Generated: `T.sh` (the shape), `T.emb : ty → C`, `T.emb_wf`, `T.enc` (the input format: `C.enc T.sh ∘
T.emb`: tag byte, then the fields, `x` 8 bytes little-endian mod `2^64`), `T.enc2` (two values one after another).

`frontx_ind f on T`: `f` is either structurally recursive over `ty` (one equation per constructor, from the
equation compiler), with at most one scalar parameter (`a`) and one more `ty` parameter (`b`, the second input), or
non-recursive with body `g c₁ …` for such a `g` (the scalar argument a literal, the `ty` argument a nullary
constructor).  The arms are read off `g`'s equations (`E` terms: fields, parameters, literals, `+`, `||`, `&&`, `!`,
constructors of `ty`, recursive calls on the children; calls in tail position become loops).  Generated, all proved
automatically: `f.pg`, `f.sem` (the program's meaning is `g`'s), `f.wf`, `f.code` and `f.implements1`. -/
import Riscv.Frontx.Ind
import Riscv.Back.Calls

namespace Proven.Frontx.IndCmd
open Lean Meta Elab Command Term

def runCmd (s : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command ("set_option linter.unusedSimpArgs false in\n" ++ s) with
  | .ok stx => elabCommand stx
  | .error e => throwError "frontx_ind: generated text does not parse ({e}):\n{s}"

inductive Sc where | nat | u64 | bool
  deriving BEq, Inhabited

def scOf? (t : Expr) : MetaM (Option Sc) := do
  let t ← whnfR t
  if t.isConstOf ``Nat then return some .nat
  if t.isConstOf ``UInt64 then return some .u64
  if t.isConstOf ``Bool then return some .bool
  return none

/-- the word of a scalar `v` -/
def Sc.rep : Sc → String → String
  | .nat, v => s!"(BitVec.ofNat 64 {v})"
  | .u64, v => s!"({v}).toBitVec"
  | .bool, v => s!"(Proven.Frontx.Ind.bw {v})"

/-- a field's role: child `l` / `r`, scalar `x`, dropped -/
inductive Role where | l | r | x (s : Sc) | drop
  deriving BEq, Inhabited

structure TyInfo where
  ty : Expr
  ind : Name
  params : Array Expr
  ctors : Array Name
  roles : Array (Array Role)
  ftys : Array (Array String)

def analyze (ty : Expr) : MetaM TyInfo := do
  let ty ← whnfR ty
  let .const ind _ := ty.getAppFn | throwError "frontx_ind_type: not an inductive type{indentExpr ty}"
  let some (.inductInfo iv) := (← getEnv).find? ind | throwError "frontx_ind_type: not an inductive type{indentExpr ty}"
  let params := ty.getAppArgs
  unless params.size == iv.numParams && iv.numIndices == 0 do throwError "frontx_ind_type: indexed families are not supported"
  let mut roles := #[]
  let mut ftys := #[]
  let us := ty.getAppFn.constLevels!
  for c in iv.ctors do
    let cty ← inferType (mkAppN (mkConst c us) params)
    let (rs, fts) ← forallTelescope cty fun xs _ => do
      let mut rs := #[]
      let mut fts := #[]
      let mut kids := 0
      let mut scal := false
      for x in xs do
        let ft ← inferType x
        fts := fts.push (toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr ft)))
        if ← isDefEq ft ty then
          rs := rs.push (if kids == 0 then Role.l else Role.r)
          kids := kids + 1
          if kids > 2 then throwError "frontx_ind_type: {c}: more than two recursive fields"
        else match ← scOf? ft with
          | some s =>
            if scal then throwError "frontx_ind_type: {c}: more than one scalar field"
            rs := rs.push (Role.x s); scal := true
          | none => rs := rs.push Role.drop
      return (rs, fts)
    roles := roles.push rs
    ftys := ftys.push fts
  return { ty, ind, params, ctors := iv.ctors.toArray, roles, ftys }

def roleFld : Role → Option String
  | .l => some ".l" | .r => some ".r" | .x _ => some ".x" | .drop => none

/-- the type of a constant, its universe parameters fresh metavariables -/
def typeOfM (n : Name) : MetaM Expr := do
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  return ci.instantiateTypeLevelParams us

def ppFull (e : Expr) : MetaM String := do
  return toString (← withOptions (fun o => o.setBool `pp.fullNames true)
    (ppExpr e))

/-- the cell of constructor `i` with field texts `fs` -/
def cellS (ti : TyInfo) (i : Nat) (fs : Array String) (emb : String → String) : String := Id.run do
  let rs := ti.roles[i]!
  let mut x := "0"; let mut l := "Proven.Mach.Ind.C.z"; let mut r := "Proven.Mach.Ind.C.z"
  for j in [0:rs.size] do
    match rs[j]! with
    | .l => l := emb fs[j]!
    | .r => r := emb fs[j]!
    | .x s => x := s.rep fs[j]!
    | .drop => pure ()
  return s!"(Proven.Mach.Ind.C.c {i} {x} {l} {r})"

syntax "frontx_ind_type " ident " := " term : command
elab_rules : command
  | `(frontx_ind_type $T:ident := $ty:term) => do
  let Tn := T.getId
  let (tyS, ti) ← liftTermElabM do
    let tyE ← elabType ty
    synthesizeSyntheticMVarsNoPostponing
    let tyE ← instantiateMVars tyE
    return (← ppFull tyE, ← analyze tyE)
  let shS := ", ".intercalate (ti.roles.toList.map fun rs =>
    "[" ++ ", ".intercalate (rs.toList.filterMap roleFld) ++ "]")
  runCmd s!"def {Tn}.sh : Proven.Mach.Ind.Shape := [{shS}]"
  let mut alts := ""
  for i in [0:ti.ctors.size] do
    let fs := (List.range ti.roles[i]!.size).toArray.map fun j => s!"f{j}"
    let pat := s!"@{ti.ctors[i]!} " ++ " ".intercalate ((List.replicate ti.params.size "_") ++ fs.toList)
    alts := alts ++ s!"\n  | {pat} => {cellS ti i fs fun v => s!"({Tn}.emb {v})"}"
  runCmd s!"def {Tn}.emb : {tyS} → Proven.Mach.Ind.C{alts}"
  -- the range hypothesis of functions comparing `Nat`s: every `Nat` field is below `2^64`
  let mut salts := ""
  for i in [0:ti.ctors.size] do
    let rs := ti.roles[i]!
    let fs := (List.range rs.size).toArray.map fun j => s!"f{j}"
    let pat := s!"@{ti.ctors[i]!} " ++ " ".intercalate ((List.replicate ti.params.size "_") ++ fs.toList)
    let mut cs : Array String := #[]
    for j in [0:rs.size] do
      match rs[j]! with
      | .l | .r => cs := cs.push s!"{Tn}.small {fs[j]!}"
      | .x .nat => cs := cs.push s!"{fs[j]!} < 2 ^ 64"
      | _ => pure ()
    salts := salts ++ s!"\n  | {pat} => {if cs.isEmpty then "True" else " ∧ ".intercalate cs.toList}"
  runCmd s!"/-- every `Nat` field of the value is below `2^64` -/
def {Tn}.small : {tyS} → Prop{salts}"
  for i in [0:ti.ctors.size] do
    if ti.roles[i]!.contains .drop then continue
    let fs := (List.range ti.roles[i]!.size).toArray.map fun j => s!"f{j}"
    let bs := " ".intercalate ((List.range fs.size).map fun j => s!"({fs[j]!} : {ti.ftys[i]![j]!})")
    let app := s!"(@{ti.ctors[i]!} " ++ " ".intercalate ((List.replicate ti.params.size "_") ++ fs.toList) ++ ")"
    runCmd s!"theorem {Tn}.fold{i} : {if fs.isEmpty then "" else "∀ " ++ bs ++ ","} {cellS ti i fs fun v => s!"({Tn}.emb {v})"} = {Tn}.emb {app} := {if fs.isEmpty then "rfl" else "fun " ++ " ".intercalate fs.toList ++ " => rfl"}"
  runCmd s!"theorem {Tn}.emb_wf : ∀ t : {tyS}, ({Tn}.emb t).wf {Tn}.sh := by
  intro t; induction t <;> simp_all [{Tn}.emb, Proven.Mach.Ind.C.wf, {Tn}.sh]"
  runCmd s!"/-- the input format of `{tyS}` -/
def {Tn}.enc (t : {tyS}) : List UInt8 := ({Tn}.emb t).enc {Tn}.sh"
  runCmd s!"/-- two values of `{tyS}`, one after the other -/
def {Tn}.enc2 (p : {tyS} × {tyS}) : List UInt8 := ({Tn}.emb p.1).enc {Tn}.sh ++ ({Tn}.emb p.2).enc {Tn}.sh"
  logInfo m!"frontx_ind_type: {Tn} := {tyS}, shape {shS}"

/-! ## reading the equations -/

structure Ctx where
  g : Name
  nargs : Nat
  ti : TyInfo
  /-- fields of the matched constructor: fvar ↦ `.x` / `.l` / `.r` -/
  fields : Array (Expr × String)
  sIdx : Nat
  aIdx : Option Nat
  bIdx : Option Nat
  params : Array Expr
  /-- set when a comparison of `Nat`s is translated (the theorem then needs the range hypothesis `T.small`) -/
  small : IO.Ref Bool

/-- `Nat` or a fixed-width scalar type whose comparisons are translated (`Nat` sets `small`) -/
def cmpTy (c : Ctx) (t : Expr) : MetaM Unit := do
  match ← scOf? t with
  | some .nat => c.small.set true
  | some _ => pure ()
  | none => throwError "frontx_ind: comparison of an unsupported type{indentExpr t}"

mutual
/-- a decidable proposition as a `0`/`1` word -/
partial def reifyP (c : Ctx) (p : Expr) : MetaM String := do
  let p := p.consumeMData
  let args := p.getAppArgs
  match p.getAppFn.constName?, args.size with
  | some ``LT.lt, 4 => cmpTy c args[0]!; return s!"(.bin .ult {← reify c args[2]!} {← reify c args[3]!})"
  | some ``GT.gt, 4 => cmpTy c args[0]!; return s!"(.bin .ult {← reify c args[3]!} {← reify c args[2]!})"
  | some ``LE.le, 4 => cmpTy c args[0]!; return s!"(.bin .xor (.bin .ult {← reify c args[3]!} {← reify c args[2]!}) (.k 1))"
  | some ``GE.ge, 4 => cmpTy c args[0]!; return s!"(.bin .xor (.bin .ult {← reify c args[2]!} {← reify c args[3]!}) (.k 1))"
  | some ``Eq, 3 => cmpTy c args[0]!; return s!"(.bin .eq {← reify c args[1]!} {← reify c args[2]!})"
  | some ``Ne, 3 => cmpTy c args[0]!; return s!"(.bin .xor (.bin .eq {← reify c args[1]!} {← reify c args[2]!}) (.k 1))"
  | some ``Not, 1 => return s!"(.bin .xor {← reifyP c args[0]!} (.k 1))"
  | some ``And, 2 => return s!"(.bin .and {← reifyP c args[0]!} {← reifyP c args[1]!})"
  | some ``Or, 2 => return s!"(.bin .or {← reifyP c args[0]!} {← reifyP c args[1]!})"
  | _, _ => throwError "frontx_ind: unsupported condition{indentExpr p}"

/-- a `match` on a `Bool` or an enumeration: one branch per constructor, as `ite`s on the tag -/
partial def reifyMatch (c : Ctx) (e : Expr) : MetaM (Option String) := do
  let some m ← matchMatcherApp? e | return none
  unless m.discrs.size == 1 do return none
  let d := m.discrs[0]!
  let dt ← whnfR (← inferType d)
  let .const tn us := dt.getAppFn | return none
  let some (.inductInfo iv) := (← getEnv).find? tn | return none
  -- only constructors without fields
  for cn in iv.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? cn | return none
    unless ci.numFields == 0 do return none
  let mut branches := #[]
  for cn in iv.ctors do
    let ce := mkAppN (mkConst cn us) dt.getAppArgs
    let app := mkAppN (mkAppN (mkAppN (mkAppN (mkConst m.matcherName m.matcherLevels.toList) m.params)
      #[m.motive]) #[ce]) (m.alts ++ m.remaining)
    match ← reduceMatcher? app with
    | .reduced e' => branches := branches.push (← reify c e'.headBeta)
    | _ => return none
  let ds ← if tn == ``Bool then reify c d else
    throwError "frontx_ind: a match on an enumeration other than Bool{indentExpr e}"
  -- Bool: `true` is constructor 1
  if tn == ``Bool then return some s!"(.ite {ds} {branches[1]!} {branches[0]!})"
  return none

partial def reify (c : Ctx) (e : Expr) : MetaM String := do
  let e := e.consumeMData
  if e.isFVar || e.isMVar then
    if let some (_, s) := c.fields.find? (·.1 == e) then return s
    if let some i := c.aIdx then if c.params[i]! == e then return ".a"
    if let some i := c.bIdx then if c.params[i]! == e then return ".b"
    throwError "frontx_ind: unsupported variable (a dropped field?){indentExpr e}"
  if let some n := e.rawNatLit? then return s!"(.k (BitVec.ofNat 64 {n}))"
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (e.getArg! 1).rawNatLit? then return s!"(.k (BitVec.ofNat 64 {n}))"
  if e.isConstOf ``Nat.zero || e.isConstOf ``Bool.false then return "(.k 0)"
  if e.isConstOf ``Bool.true then return "(.k 1)"
  if e.isAppOfArity ``Nat.succ 1 then return s!"(.bin .add {← reify c e.appArg!} (.k 1))"
  if e.isAppOfArity ``HAdd.hAdd 6 && (← whnfR (e.getArg! 0)).isConstOf ``Nat then
    return s!"(.bin .add {← reify c (e.getArg! 4)} {← reify c (e.getArg! 5)})"
  if e.isAppOfArity ``or 2 then return s!"(.bin .or {← reify c (e.getArg! 0)} {← reify c (e.getArg! 1)})"
  if e.isAppOfArity ``and 2 then return s!"(.bin .and {← reify c (e.getArg! 0)} {← reify c (e.getArg! 1)})"
  if e.isAppOfArity ``not 1 then return s!"(.bin .xor {← reify c (e.getArg! 0)} (.k 1))"
  if e.isAppOfArity ``ite 5 then
    return s!"(.ite {← reifyP c (e.getArg! 1)} {← reify c (e.getArg! 3)} {← reify c (e.getArg! 4)})"
  if e.isAppOfArity ``cond 4 then
    return s!"(.ite {← reify c (e.getArg! 1)} {← reify c (e.getArg! 2)} {← reify c (e.getArg! 3)})"
  if e.isAppOfArity ``Decidable.decide 2 then return ← reifyP c (e.getArg! 0)
  if e.isAppOfArity ``BEq.beq 4 then
    cmpTy c (e.getArg! 0); return s!"(.bin .eq {← reify c (e.getArg! 2)} {← reify c (e.getArg! 3)})"
  if e.isAppOfArity ``bne 4 then
    cmpTy c (e.getArg! 0); return s!"(.bin .xor (.bin .eq {← reify c (e.getArg! 2)} {← reify c (e.getArg! 3)}) (.k 1))"
  if let some s ← reifyMatch c e then return s
  let fn := e.getAppFn
  if fn.isConstOf c.g && e.getAppNumArgs == c.nargs then
    let args := e.getAppArgs
    let s := args[c.sIdx]!.consumeMData
    let ch ← match c.fields.find? (fun (x, _) => s == x) with
      | some (_, ".l") => pure "false"
      | some (_, ".r") => pure "true"
      | _ => throwError "frontx_ind: a recursive call not on a child{indentExpr e}"
    let a ← match c.aIdx with | some i => reify c args[i]! | none => pure "(.k 0)"
    let b ← match c.bIdx with | some i => reify c args[i]! | none => pure ".nul"
    return s!"(.call {ch} {a} {b})"
  if let .const cn _ := fn then
    if let some i := c.ti.ctors.findIdx? (· == cn) then
      let args := e.getAppArgs
      let fs := args.extract c.ti.params.size args.size
      let rs := c.ti.roles[i]!
      unless fs.size == rs.size do throwError "frontx_ind: partial constructor application{indentExpr e}"
      let mut x := "(.k 0)"; let mut l := ".nul"; let mut r := ".nul"
      for j in [0:rs.size] do
        match rs[j]! with
        | .l => l ← reify c fs[j]!
        | .r => r ← reify c fs[j]!
        | .x _ => x ← reify c fs[j]!
        | .drop => pure ()  -- not in the byte format (`T.emb` ignores it)
      return s!"(.mk {i} {x} {l} {r})"
  throwError "frontx_ind: unsupported term{indentExpr e}"
end

/-- the arms of `g`, one per constructor, from its equations -/
def armsOf (g : Name) (ti : TyInfo) : MetaM (Nat × Option Nat × Option Nat × Option Sc × Array String × Bool) := do
  let some eqns ← getEqnsFor? g | throwError "frontx_ind: no equations for {g}"
  let small ← IO.mkRef false
  let mut arms : Array (Option String) := ti.ctors.map fun _ => none
  let mut info : Option (Nat × Option Nat × Option Nat × Option Sc) := none
  for eqn in eqns do
    let r ← do
      let (hs, _, ty) ← forallMetaTelescope (← typeOfM eqn)
      let some (_, lhs, _) := ty.eq? | throwError "frontx_ind: bad equation {eqn}"
      let args := lhs.getAppArgs
      -- the structural argument: a constructor application of `ty`
      let mut sIdx? := none
      let mut ctorI := 0
      for j in [0:args.size] do
        if let .const cn _ := args[j]!.getAppFn then
          if let some i := ti.ctors.findIdx? (· == cn) then sIdx? := some j; ctorI := i
      let some sIdx := sIdx? | throwError "frontx_ind: equation {eqn} has no constructor pattern"
      unless (← isDefEq (← inferType args[sIdx]!) ti.ty) do throwError "frontx_ind: {g} is not over the type"
      let ty ← instantiateMVars ty
      let some (_, lhs, rhs) := ty.eq? | throwError "frontx_ind: bad equation {eqn}"
      let args := lhs.getAppArgs
      for h in hs do
        if (← inferType h).isProp then throwError "frontx_ind: overlapping patterns ({eqn} has hypotheses)"
      let sa := args[sIdx]!.getAppArgs
      let fs := sa.extract ti.params.size sa.size
      let mut fields := #[]
      for j in [0:fs.size] do
        unless fs[j]!.isMVar do throwError "frontx_ind: nested patterns are not supported ({eqn})"
        if let some s := roleFld ti.roles[ctorI]![j]! then fields := fields.push (fs[j]!, s)
      -- the other explicit arguments: one scalar, one more value of the type
      let mut aIdx := none; let mut bIdx := none; let mut aSc := none
      for j in [0:args.size] do
        if j == sIdx then continue
        let t ← inferType args[j]!
        if (← isProp t) || (← isType args[j]!) || t.isSort then continue
        if !(args[j]!.isMVar) then continue
        if ← isDefEq t ti.ty then
          if bIdx.isSome then throwError "frontx_ind: more than one extra parameter of the type"
          bIdx := some j
        else match ← scOf? t with
          | some s =>
            if aIdx.isSome then throwError "frontx_ind: more than one scalar parameter"
            aIdx := some j; aSc := some s
          | none =>
            if (← isClass? t).isSome then continue
            if (← whnfR t).isConstOf ``Unit || (← whnfR t).isConstOf ``PUnit then continue
            throwError "frontx_ind: unsupported parameter type{indentExpr t}"
      let c : Ctx := { g, nargs := args.size, ti, fields, sIdx, aIdx, bIdx, params := args, small }
      pure (ctorI, (sIdx, aIdx, bIdx, aSc), ← reify c rhs)
    let (i, inf, s) := r
    arms := arms.set! i (some s)
    info := some inf
  let some (sIdx, aIdx, bIdx, aSc) := info | throwError "frontx_ind: no equations"
  let arms' ← arms.mapIdxM fun i a => match a with
    | some s => pure s
    | none => throwError "frontx_ind: no equation for constructor {ti.ctors[i]!}"
  return (sIdx, aIdx, bIdx, aSc, arms', ← small.get)

/-- the explicit binders of `f` (types instantiated by unification with `ty` where they are implicit) -/
def resKind (ti : TyInfo) (r : Expr) : MetaM (String × Option Sc) := do
  if ← isDefEq r ti.ty then return (".t", none)
  match ← scOf? r with
  | some s => return (".w", some s)
  | none => throwError "frontx_ind: unsupported result type{indentExpr r}"

def wfDefs : List String := ["Proven.Mach.Ind.indProg", "Proven.Mach.Ind.mainFn", "Proven.Mach.Ind.decFn",
  "Proven.Mach.Ind.encFn", "Proven.Mach.Ind.fFn", "Proven.Mach.Ind.fLoop", "Proven.Mach.Ind.disp",
  "Proven.Mach.Ind.arm", "Proven.Mach.Ind.comp", "Proven.Mach.Ind.E.tail?", "Proven.Mach.Ind.loads",
  "Proven.Mach.Ind.dDisp", "Proven.Mach.Ind.dFlds", "Proven.Mach.Ind.dFld", "Proven.Mach.Ind.eDisp",
  "Proven.Mach.Ind.eFlds", "Proven.Mach.Ind.eFld", "Proven.Mach.Ind.rdB", "Proven.Mach.Ind.wrB",
  "Proven.Mach.Ind.alloc", "Proven.Mach.Ind.stW", "Proven.Mach.Ind.vE", "Proven.Mach.Ind.kE",
  "Proven.Mach.Ind.addE", "Proven.Mach.Ind.asg", "Proven.Mach.Ind.eqE"]

syntax "frontx_ind " ident " on " ident : command
elab_rules : command
  | `(frontx_ind $f:ident on $T:ident) => do
  let t0 ← IO.monoMsNow
  let embN ← liftCoreM (realizeGlobalConstNoOverloadWithInfo (mkIdentFrom T (T.getId ++ `emb)))
  let Tn := embN.getPrefix
  let fN ← liftCoreM (realizeGlobalConstNoOverloadWithInfo f)
  let fS := toString fN
  let r ← liftTermElabM do
    let embTy ← inferType (← mkConstWithLevelParams (Tn ++ `emb))
    let tyE := embTy.bindingDomain!
    let tyS ← ppFull tyE
    let ti ← analyze tyE
    let finfo ← getConstInfo fN
    -- the recursive function and the entry arguments
    -- `f` recursive (it has equations), or an entry `f xs = g c₁ …`
    let recur ← match ← getEqnsFor? fN with
      | none => pure false
      | some eqns => eqns.anyM fun eqn => do
        let (_, _, ty) ← forallMetaTelescope (← typeOfM eqn)
        let some (_, lhs, _) := ty.eq? | pure false
        return lhs.getAppArgs.any fun a => a.getAppFn.isConst && ti.ctors.contains a.getAppFn.constName!
    let (gN, entry) ← if recur then pure (fN, none) else
      forallTelescope finfo.type fun xs _ => do
        let some v := finfo.value? | throwError "frontx_ind: {fN} has no definition"
        let body := (← instantiateLambda v xs).consumeMData
        let .const gN _ := body.getAppFn | throwError "frontx_ind: {fN} is neither recursive nor `g c₁ …`"
        unless (← getEqnsFor? gN).isSome do throwError "frontx_ind: {gN} has no equations"
        return (gN, some body.getAppArgs)
    let (sIdx, aIdx, bIdx, aSc, arms, small) ← armsOf gN ti
    -- the result kind
    let gInfo ← getConstInfo gN
    let (rkS, rSc) ← do
      let (xs, _, res) ← forallMetaTelescope (← typeOfM gN)
      -- instantiate the type parameters through the structural argument
      unless ← isDefEq (← inferType xs[sIdx]!) ti.ty do throwError "frontx_ind: type mismatch"
      resKind ti (← instantiateMVars res)
    -- the entry: inputs, the constant arguments
    let (bi, a0, aConst, bConst, twoIn) ← match entry with
      | none => pure ((if bIdx.isSome then "Proven.Mach.Ind.BIn.inp" else "Proven.Mach.Ind.BIn.none"), "0", none,
          none, bIdx.isSome)
      | some eargs => do
        let mut aC := none; let mut bC := none; let mut bi := "Proven.Mach.Ind.BIn.none"
        if let some i := aIdx then
          let some n := (← whnf eargs[i]!).rawNatLit? <|> (eargs[i]!.getArg! 1).rawNatLit?
            | throwError "frontx_ind: the scalar argument of the entry must be a literal{indentExpr eargs[i]!}"
          aC := some n
        if let some i := bIdx then
          let .const cn _ := eargs[i]!.getAppFn | throwError "frontx_ind: the second argument must be a nullary constructor"
          let some ci := ti.ctors.findIdx? (· == cn) | throwError "frontx_ind: the second argument must be a constructor"
          unless eargs[i]!.getAppNumArgs == ti.params.size do throwError "frontx_ind: the second argument must be nullary"
          bi := s!"(Proven.Mach.Ind.BIn.ctor {ci})"; bC := some ci
        pure (bi, toString (aC.getD 0), aC, bC, false)
    return (tyS, ti, gN, entry.isSome, sIdx, aIdx, bIdx, aSc, arms, rkS, rSc, bi, a0, aConst, bConst, twoIn, small)
  let (tyS, ti, gN, isEntry, sIdx, aIdx, bIdx, aSc, arms, rkS, rSc, bi, a0, aConst, bConst, twoIn, small) := r
  let gS := toString gN
  let nargs ← liftTermElabM do forallTelescope (← getConstInfo gN).type fun xs _ => return xs.size
  let P := s!"{fS}.ind"
  runCmd s!"def _root_.{P}.pg : Proven.Mach.Ind.Pg {rkS} := ⟨[{", ".intercalate arms.toList}]⟩"
  runCmd s!"theorem _root_.{P}.arms : {P}.pg.arms = [{", ".intercalate arms.toList}] := rfl"
  -- the meaning: `g` applied to `t`, `a`, `b` in its own argument order (explicit arguments only)
  let gExpl ← liftTermElabM do forallTelescope (← getConstInfo gN).type fun xs _ => xs.mapM fun x => do
    return (← x.fvarId!.getBinderInfo).isExplicit
  let gUnit ← liftTermElabM do
    let (xs, _, _) ← forallMetaTelescope (← typeOfM gN)
    discard <| isDefEq (← inferType xs[sIdx]!) ti.ty
    xs.mapM fun x => do
      let t ← whnfR (← instantiateMVars (← inferType x))
      return t.isConstOf ``Unit || t.isConstOf ``PUnit
  let mut gArgs := #[]
  for j in [0:nargs] do
    if !gExpl[j]! then continue
    if j == sIdx then gArgs := gArgs.push "t"
    else if aIdx == some j then gArgs := gArgs.push "a"
    else if bIdx == some j then gArgs := gArgs.push "b"
    else if gUnit[j]! then gArgs := gArgs.push "()"
    else throwError "frontx_ind: unexpected explicit argument {j} of {gN}"
  let aTy := match aSc with | some .nat => "Nat" | some .u64 => "UInt64" | some .bool => "Bool" | none => "BitVec 64"
  let aRep := match aSc with | some s => s.rep "a" | none => "a"
  let bTy := if bIdx.isSome then tyS else "Proven.Mach.Ind.C"
  let bRep := if bIdx.isSome then s!"({Tn}.emb b)" else "b"
  let gApp := s!"({gS} {" ".intercalate gArgs.toList})"
  let resRep := if rkS == ".t" then s!"({Tn}.emb {gApp})" else rSc.get!.rep gApp
  let folds := ", ".intercalate ((List.range ti.ctors.size).filter (fun i => !ti.roles[i]!.contains .drop) |>.map
    fun i => s!"{Tn}.fold{i}")
  let words := "Proven.Frontx.Ind.bw_or, Proven.Frontx.Ind.bw_and, Proven.Frontx.Ind.bw_not, " ++
    "Proven.Frontx.Ind.bw_true, Proven.Frontx.Ind.bw_false, Proven.Frontx.Ind.nat_add"
  let words0 := words
  let cmpW := "Proven.Frontx.Ind.nat_ult, Proven.Frontx.Ind.nat_eq, Proven.Frontx.Ind.bw_eq0, Proven.Frontx.Ind.bw_eq0', " ++
    "Proven.Frontx.Ind.u64_ult, Proven.Frontx.Ind.u64_eq, Proven.Frontx.Ind.bool_eq"
  -- comparisons of `Nat`s: the scalars are below `2^64` (`T.small`; `a < 2^64`)
  let hyps := if !small then "" else
    s!"{Tn}.small t → " ++ (if aSc == some .nat then "a < 2 ^ 64 → " else "") ++
      (if bIdx.isSome then s!"{Tn}.small b → " else "")
  let words := if small then words ++ s!", {Tn}.small, {cmpW}" else words ++ s!", {cmpW}"
  runCmd s!"theorem _root_.{P}.sem : ∀ (t : {tyS}) (a : {aTy}) (b : {bTy}), {hyps}{P}.pg.sem ({Tn}.emb t) {aRep} {bRep} = {resRep} := by
  intro t; induction t <;> intro a b <;> intros <;>
  first
  | (simp_all [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {Tn}.emb, {words}]; done)
  | (simp only [{Tn}.emb, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Bool.false_eq_true, if_true, if_false]
     simp only [{gS}]
     split <;> simp_all [{Tn}.emb, {words}]; done)
  | (simp only [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {Tn}.emb, {Tn}.small,
      List.getElem?_cons_succ, List.getElem?_cons_zero] at *
     try simp (disch := omega) only [{cmpW}, decide_eq_false_iff_not, {words0}]
     repeat' split
     all_goals simp_all [{Tn}.emb, {words}]
     all_goals omega)
  | (simp only [{Tn}.emb, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Bool.false_eq_true, if_true, if_false, {words}]
     try simp only [{folds}, Proven.Frontx.Ind.nat_add]
     try simp only [*]
     simp [{gS}, {Tn}.emb, {words}]; done)"
  let nb := match rSc with | some .bool => 1 | _ => 8
  let res := if rkS == ".t" then 1 else 7
  let progS := s!"(Proven.Mach.Ind.indProg {Tn}.sh {P}.pg {bi} (BitVec.ofNat 64 {a0}) {nb})"
  let wfT := s!"wf_calls [{", ".intercalate (wfDefs ++ [s!"{Tn}.sh", s!"{P}.pg"])}]"
  runCmd s!"set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem _root_.{P}.wf : Proven.Mach.Riscv.WfProg1W {progS} (if {rkS} = Proven.Mach.Ind.Kd.t then 1 else 7) 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 := by simp [Proven.Mach.Ind.indProg] at hf; omega
    rcases this with rfl | rfl | rfl | rfl <;> {wfT}
  · {wfT}"
  runCmd s!"def _root_.{fS}.code : List (BitVec 32) := Proven.Mach.Riscv.callsCode1W {progS} {res} 0"
  -- the machine theorem
  let encA := if twoIn then s!"{Tn}.enc2" else s!"{Tn}.enc"
  let inTy := if twoIn then s!"{tyS} × {tyS}" else tyS
  let fApp := if isEntry then s!"(fun t : {tyS} => {fS} t)" else
    if twoIn then
      -- `f`'s explicit arguments: the structural one is the first input, the other one the second
      s!"(fun p : {tyS} × {tyS} => {gS} {" ".intercalate (gArgs.toList.map fun s => if s == "t" then "p.1" else "p.2")})"
    else s!"(fun t : {tyS} => {gS} {" ".intercalate gArgs.toList})"
  let encB := if rkS == ".t" then s!"{Tn}.enc" else match rSc with
    | some .bool => "(fun b : Bool => [if b then (1 : UInt8) else 0])"
    | _ => "(fun n : Nat => leN 8 n)"
  let v1 := if twoIn then s!"(fun p : {inTy} => {Tn}.emb p.1)" else s!"{Tn}.emb"
  let v2 := if twoIn then s!"(fun p : {inTy} => {Tn}.emb p.2)" else s!"(fun _ : {inTy} => Proven.Mach.Ind.C.z)"
  let hencT := if twoIn then "fun g => rfl" else "fun g => rfl"
  let hw2T := if twoIn then s!"fun _ g => {Tn}.emb_wf g.2" else "fun h => nomatch h"
  let unfoldEntry := if isEntry then s!"show {encB} ({gS} {" ".intercalate (gArgs.toList.map fun s =>
    if s == "t" then "g" else if s == "a" then toString (aConst.getD 0) else "_")}) = _; " else ""
  if aIdx.isSome && aConst.isNone then throwError "frontx_ind: a scalar parameter needs an entry `f xs = {gN} n xs`"
  let aS := match aConst with | some n => toString n | none => "(BitVec.ofNat 64 0)"
  let bS := if twoIn then "g.2" else match bConst with
    | some ci => s!"(@{ti.ctors[ci]!} {" ".intercalate (List.replicate ti.params.size "_")})"
    | none => "Proven.Mach.Ind.C.z"
  let semArgs := s!"{if twoIn then "g.1" else "g"} {aS} {bS}"
  -- with the range hypothesis: the input is the subtype `{g // T.small g}`
  let semArgs := if !small then semArgs else
    semArgs ++ (if twoIn then " hg.1" else " hg") ++ (if aSc == some .nat then " (by decide)" else "") ++
      (if bIdx.isSome then (if twoIn then " hg.2" else s!" (by simp [{Tn}.small])") else "")
  let smallP := if twoIn then s!"{Tn}.small g.1 ∧ {Tn}.small g.2" else s!"{Tn}.small g"
  let sub (fn : String) : String := if small then s!"(fun g : \{g : {inTy} // {smallP}} => {fn} g.1)" else fn
  let encA' := sub encA
  let fApp' := sub fApp
  let v1 := sub v1
  let v2 := sub v2
  let hw2T := if small && twoIn then s!"fun _ g => {Tn}.emb_wf g.1.2" else hw2T
  let intro := if small then "obtain ⟨g, hg⟩ := g; dsimp only; " else ""
  let finish := if rkS == ".t" then "rfl" else match rSc with
    | some .bool => "exact Proven.Frontx.Ind.outBool _"
    | _ => "exact Proven.Frontx.Ind.outNat _"
  let houtT := s!"fun g => by
      {intro}{unfoldEntry}have h := {P}.sem {semArgs}
      simp only [{Tn}.emb] at h
      simp only [Proven.Mach.Ind.Kd.out, Proven.Mach.Ind.BIn.val]
      rw [h]; {finish}"
  let rl := if rkS == ".t" then "true" else "false"
  runCmd s!"theorem _root_.{fS}.implements1 : Proven.Implements1With {encA'} {encB} {fS}.code {fApp'}
    (Proven.Frontx.Ind.space {P}.pg.M) (2 ^ 20) {rl} := by
  have := Proven.Frontx.Ind.implements1_ind {Tn}.sh {P}.pg {bi} (BitVec.ofNat 64 {a0}) {nb} {encA'} {encB} {fApp'} {v1} {v2}
    ({hencT}) (fun g => {Tn}.emb_wf _) ({hw2T})
    ({houtT})
    (by decide) (by decide) (by decide) (by unfold Proven.Mach.Ind.Pg.lin; decide) (by intro t h; cases h <;> decide)
    (by decide) (by decide) {P}.wf
  exact this"
  let t1 ← IO.monoMsNow
  logInfo m!"frontx_ind: {fN}{if isEntry then m!" (entry of {gN})" else m!""} on {Tn}: {arms.size} arms, result {rkS}; {t1 - t0} ms"

end Proven.Frontx.IndCmd
