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
  deriving Inhabited

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

/-- a type declared with `frontx_ind_type` (its name `T`, the analysis) -/
structure RTy where
  tn : Name
  ti : TyInfo
  deriving Inhabited

/-- a function of the program: its structural argument (of type `ty`), word and tree parameters, result kind -/
structure FnI where
  name : Name
  ty : RTy
  sIdx : Nat
  aIdx : Option Nat
  bIdx : Option Nat
  aSc : Option Sc
  nargs : Nat
  rk : String
  rSc : Option Sc
  rTy : Option RTy
  deriving Inhabited

structure Ctx where
  g : Name
  nargs : Nat
  ti : TyInfo
  tys : Array RTy
  /-- expressions with a fixed translation (fields of the node, of matched values, the node itself, `let`s); the
  text from the number of enclosing `bind`s -/
  als : Array (Expr × (Nat → String))
  /-- the children of the current node (`false` = `l`) -/
  kids : Array (Expr × Bool)
  /-- the number of enclosing `bind`s -/
  depth : Nat
  sIdx : Nat
  aIdx : Option Nat
  bIdx : Option Nat
  params : Array Expr
  /-- set when a comparison of `Nat`s is translated (the theorem then needs the range hypothesis `T.small`) -/
  small : IO.Ref Bool
  fns : Array FnI
  cur : Nat
  /-- functions called that are not (yet) in `fns` -/
  found : IO.Ref (Array Name)

/-- `Nat` or a fixed-width scalar type whose comparisons are translated (`Nat` sets `small`) -/
def cmpTy (c : Ctx) (t : Expr) : MetaM Unit := do
  match ← scOf? t with
  | some .nat => c.small.set true
  | some _ => pure ()
  | none => throwError "frontx_ind: comparison of an unsupported type{indentExpr t}"

def findTy (tys : Array RTy) (t : Expr) : MetaM (Option RTy) := do
  for r in tys do
    if ← isDefEq t r.ti.ty then return some r
  return none

def findCtor (tys : Array RTy) (cn : Name) : Option (RTy × Nat) := Id.run do
  for r in tys do
    if let some i := r.ti.ctors.findIdx? (· == cn) then return some (r, i)
  return none

/-- the kind of a value of type `t` -/
def kindOf (c : Ctx) (t : Expr) : MetaM String := do
  if (← findTy c.tys t).isSome then return ".t"
  if (← scOf? t).isSome then return ".w"
  throwError "frontx_ind: a value of unsupported type{indentExpr t}"

/-- the aliases of the fields of constructor `i` of `r` (pattern variables `fs`) read from the value `d` -/
def fieldAliases (r : RTy) (i : Nat) (fs : Array Expr) (d : Nat → String) : Array (Expr × (Nat → String)) := Id.run do
  let rs := r.ti.roles[i]!
  let mut out := #[]
  for j in [0:rs.size] do
    match rs[j]! with
    | .l => out := out.push (fs[j]!, fun (D : Nat) => s!"(.ft false {d D})")
    | .r => out := out.push (fs[j]!, fun (D : Nat) => s!"(.ft true {d D})")
    | .x _ => out := out.push (fs[j]!, fun (D : Nat) => s!"(.fw true {d D})")
    | .drop => pure ()
  return out

/-- the explicit arguments of a call of `fi`: tree, word, tree -/
def callArgs (fi : FnI) (args : Array Expr) : Expr × Option Expr × Option Expr :=
  (args[fi.sIdx]!, fi.aIdx.map (args[·]!), fi.bIdx.map (args[·]!))

/-- a constructor application of a closed value of a declared type -/
partial def closedCtor (tys : Array RTy) (e : Expr) : Option (RTy × Nat × Array Expr) :=
  match e.getAppFn with
  | .const cn _ => match findCtor tys cn with
    | some (r, i) => some (r, i, e.getAppArgs.extract r.ti.params.size e.getAppNumArgs)
    | none => none
  | _ => none

/-- the other explicit arguments: one scalar, one more value of a declared type -/
def extraArgs (tys : Array RTy) (args : Array Expr) (sIdx : Nat) :
    MetaM (Option Nat × Option Nat × Option Sc) := do
  let mut aIdx := none; let mut bIdx := none; let mut aSc := none
  for j in [0:args.size] do
    if j == sIdx then continue
    let t ← inferType args[j]!
    if (← isProp t) || (← isType args[j]!) || t.isSort then continue
    if !(args[j]!.isMVar || args[j]!.isFVar) then continue
    if (← findTy tys t).isSome then
      if bIdx.isSome then throwError "frontx_ind: more than one extra parameter of a declared type"
      bIdx := some j
    else match ← scOf? t with
      | some s =>
        if aIdx.isSome then throwError "frontx_ind: more than one scalar parameter"
        aIdx := some j; aSc := some s
      | none =>
        if (← isClass? t).isSome then continue
        if (← whnfR t).isConstOf ``Unit || (← whnfR t).isConstOf ``PUnit then continue
        throwError "frontx_ind: unsupported parameter type{indentExpr t}"
  return (aIdx, bIdx, aSc)

def resKind (tys : Array RTy) (r : Expr) : MetaM (String × Option Sc × Option RTy) := do
  if let some rt ← findTy tys r then return (".t", none, some rt)
  match ← scOf? r with
  | some s => return (".w", some s, none)
  | none => throwError "frontx_ind: unsupported result type{indentExpr r}"

/-- the structural argument (of a declared type), the result kind, the arity of `g` -/
def fnInfo (tys : Array RTy) (g : Name) : MetaM FnI := do
  let (xs, _, res) ← forallMetaTelescope (← typeOfM g)
  -- the structural argument: the first explicit argument of a declared type that the equations match on
  let some eqns ← getEqnsFor? g | throwError "frontx_ind: no equations for {g}"
  let mut sIdx? := none
  let mut rty? := none
  for eqn in eqns do
    let (_, _, ty) ← forallMetaTelescope (← typeOfM eqn)
    let some (_, lhs, _) := ty.eq? | continue
    let args := lhs.getAppArgs
    for j in [0:args.size] do
      if sIdx?.isNone then
        if let .const cn _ := args[j]!.getAppFn then
          if let some (r, _) := findCtor tys cn then sIdx? := some j; rty? := some r
  if sIdx?.isNone then
    -- no constructor pattern in the equations (a `match` in the body): the first argument of a declared type
    for j in [0:xs.size] do
      if sIdx?.isNone then
        if let some r ← findTy tys (← inferType xs[j]!) then sIdx? := some j; rty? := some r
  let some sIdx := sIdx? | throwError "frontx_ind: {g} has no argument of a declared type"
  let some rty := rty? | throwError "frontx_ind: {g} has no argument of a declared type"
  unless ← isDefEq (← inferType xs[sIdx]!) rty.ti.ty do throwError "frontx_ind: {g}: type mismatch"
  let (aIdx, bIdx, aSc) ← extraArgs tys xs sIdx
  let (rk, rSc, rTy) ← resKind tys (← instantiateMVars res)
  return { name := g, ty := rty, sIdx, aIdx, bIdx, aSc, nargs := xs.size, rk, rSc, rTy }

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
  | some ``Eq, 3 =>
    if (← findTy c.tys args[0]!).isSome then return ← treeEq c args[1]! args[2]!
    cmpTy c args[0]!; return s!"(.bin .eq {← reify c args[1]!} {← reify c args[2]!})"
  | some ``Ne, 3 =>
    if (← findTy c.tys args[0]!).isSome then return s!"(.bin .xor {← treeEq c args[1]! args[2]!} (.k 1))"
    cmpTy c args[0]!; return s!"(.bin .xor (.bin .eq {← reify c args[1]!} {← reify c args[2]!}) (.k 1))"
  | some ``Not, 1 => return s!"(.bin .xor {← reifyP c args[0]!} (.k 1))"
  | some ``And, 2 => return s!"(.bin .and {← reifyP c args[0]!} {← reifyP c args[1]!})"
  | some ``Or, 2 => return s!"(.bin .or {← reifyP c args[0]!} {← reifyP c args[1]!})"
  | _, _ => throwError "frontx_ind: unsupported condition{indentExpr p}"

/-- `d = k` for a closed constructor term `k` (either side): the tags and the fields, recursively -/
partial def treeEq (c : Ctx) (a b : Expr) : MetaM String := do
  let (d, k) ← match closedCtor c.tys b, closedCtor c.tys a with
    | some _, _ => pure (a, b)
    | none, some _ => pure (b, a)
    | none, none => throwError "frontx_ind: `=` of two values of the type that are not constants{indentExpr a}"
  let dS ← reify c d
  treeEqS c dS k

partial def treeEqS (c : Ctx) (dS : String) (k : Expr) : MetaM String := do
  let some (r, i, fs) := closedCtor c.tys k | throwError "frontx_ind: not a constant{indentExpr k}"
  let rs := r.ti.roles[i]!
  let mut acc := s!"(.bin .eq (.fw false {dS}) (.k (BitVec.ofNat 64 {i})))"
  for j in [0:rs.size] do
    match rs[j]! with
    | .l => acc := s!"(.bin .and {acc} {← treeEqS c s!"(.ft false {dS})" fs[j]!})"
    | .r => acc := s!"(.bin .and {acc} {← treeEqS c s!"(.ft true {dS})" fs[j]!})"
    | .x _ => acc := s!"(.bin .and {acc} (.bin .eq (.fw true {dS}) {← reify c fs[j]!}))"
    | .drop => throwError "frontx_ind: `=` on a constructor with a field not in the byte format{indentExpr k}"
  return acc

/-- a `match`: split on the first discriminant that is not a constructor application (a value of a declared
type: on its tag, the pattern variables read from it; a `Bool` or an enumeration: on its value) -/
partial def reifyMatch (c : Ctx) (e : Expr) : MetaM (Option String) := do
  let some m ← matchMatcherApp? e | return none
  for i in [0:m.discrs.size] do
    let d := m.discrs[i]!.consumeMData
    let dt ← whnfR (← inferType d)
    let .const tn us := dt.getAppFn | continue
    let some (.inductInfo iv) := (← getEnv).find? tn | continue
    if let .const dn _ := d.getAppFn then if iv.ctors.contains dn then continue
    let rebuild (ce : Expr) : Expr :=
      mkAppN (mkConst m.matcherName m.matcherLevels.toList)
        (m.params ++ #[m.motive] ++ m.discrs.set! i ce ++ m.alts ++ m.remaining)
    let branch (c' : Ctx) (app : Expr) : MetaM String := do
      match ← reduceMatcher? app with
      | .reduced e' => reify c' e'.headBeta
      | _ => reify c' app
    let rt? ← findTy c.tys dt
    if let some rt := rt? then
      -- the matched value: an als (a field, a parameter, a `let`), or bound here
      let (c1, dT, wrap) ← do
        if let some (_, t) := c.als.find? (·.1 == d) then pure (c, t, fun (s : String) => s)
        else if (c.bIdx.map (c.params[·]! == d)).getD false then pure (c, fun (_ : Nat) => ".b", fun (s : String) => s)
        else
          let dS ← reify c d
          let p := c.depth
          pure ({ c with als := c.als.push (d, fun (D : Nat) => s!"(.var {D - 1 - p} .t)"), depth := c.depth + 1 },
            fun (D : Nat) => s!"(.var {D - 1 - p} .t)", fun (s : String) => s!"(.bind {dS} {s})")
      let mut bs := #[]
      for j in [0:rt.ti.ctors.size] do
        let cn := rt.ti.ctors[j]!
        let cty ← inferType (mkAppN (mkConst cn us) dt.getAppArgs)
        let s ← forallTelescope cty fun fs _ => do
          let ce := mkAppN (mkConst cn us) (dt.getAppArgs ++ fs)
          let c' := { c1 with als := (c1.als ++ fieldAliases rt j fs dT).push (ce, dT) }
          branch c' (rebuild ce)
        bs := bs.push s
      let mut acc := bs[bs.size - 1]!
      for j' in [0:bs.size - 1] do
        let j := bs.size - 2 - j'
        -- the same branch as the rest: no test
        unless bs[j]! == acc do
          acc := s!"(.ite (.bin .eq (.fw false {dT c1.depth}) (.k (BitVec.ofNat 64 {j}))) {bs[j]!} {acc})"
      return some (wrap acc)
    -- an enumeration (`Bool`: `true` is constructor 1)
    let mut enum := true
    for cn in iv.ctors do
      let some (.ctorInfo ci) := (← getEnv).find? cn | enum := false
      unless ci.numFields == 0 do enum := false
    unless enum do continue
    let dS ← reify c d
    let mut bs := #[]
    for cn in iv.ctors do
      bs := bs.push (← branch c (rebuild (mkAppN (mkConst cn us) dt.getAppArgs)))
    let mut acc := bs[bs.size - 1]!
    for j' in [0:bs.size - 1] do
      let j := bs.size - 2 - j'
      unless bs[j]! == acc do
        acc := s!"(.ite (.bin .eq {dS} (.k (BitVec.ofNat 64 {j}))) {bs[j]!} {acc})"
    return some acc
  return none

partial def reify (c : Ctx) (e : Expr) : MetaM String := do
  let e := e.consumeMData
  if let some (_, s) := c.als.find? (·.1 == e) then return s c.depth
  if e.isFVar || e.isMVar then
    if let some i := c.aIdx then if c.params[i]! == e then return ".a"
    if let some i := c.bIdx then if c.params[i]! == e then return ".b"
    throwError "frontx_ind: unsupported variable (a dropped field?){indentExpr e}"
  if let some n := e.rawNatLit? then return s!"(.k (BitVec.ofNat 64 {n}))"
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (e.getArg! 1).rawNatLit? then return s!"(.k (BitVec.ofNat 64 {n}))"
  if e.isConstOf ``Nat.zero || e.isConstOf ``Bool.false then return "(.k 0)"
  if e.isConstOf ``Bool.true then return "(.k 1)"
  if e.isAppOfArity ``Nat.succ 1 then return s!"(.bin .add {← reify c e.appArg!} (.k 1))"
  -- `let`
  if let .letE _ ty v b _ := e then
    let vS ← reify c v
    let k ← kindOf c ty
    return ← withLetDecl `x ty v fun x => do
      let p := c.depth
      let c' := { c with als := c.als.push (x, fun (D : Nat) => s!"(.var {D - 1 - p} {k})"), depth := c.depth + 1 }
      return s!"(.bind {vS} {← reify c' (b.instantiate1 x)})"
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let t ← whnfR (e.getArg! 0)
    if t.isConstOf ``Nat || t.isConstOf ``UInt64 then
      return s!"(.bin .add {← reify c (e.getArg! 4)} {← reify c (e.getArg! 5)})"
  -- `UInt64` arithmetic wraps like the words
  for (op, o) in [(``HSub.hSub, ".sub"), (``HAnd.hAnd, ".and"), (``HOr.hOr, ".or"), (``HXor.hXor, ".xor")] do
    if e.isAppOfArity op 6 then
      if (← whnfR (e.getArg! 0)).isConstOf ``UInt64 then
        return s!"(.bin {o} {← reify c (e.getArg! 4)} {← reify c (e.getArg! 5)})"
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
    let ch ← match c.kids.find? (fun (x, _) => s == x) with
      | some (_, false) => pure "false"
      | some (_, true) => pure "true"
      | none => throwError "frontx_ind: a recursive call not on a child{indentExpr e}"
    let a ← match c.aIdx with | some i => reify c args[i]! | none => pure "(.k 0)"
    let b ← match c.bIdx with | some i => reify c args[i]! | none => pure ".nul"
    return s!"(.call {ch} {a} {b})"
  -- a call of another function of the program
  if let .const fnN _ := fn then
    if let some p := c.fns.findIdx? (·.name == fnN) then
      let fi := c.fns[p]!
      if e.getAppNumArgs == fi.nargs then
        unless p > c.cur do throwError "frontx_ind: {fnN} is called from a function after it (recursion between functions)"
        let (t, a, b) := callArgs fi e.getAppArgs
        let tS ← reify c t
        let aS ← match a with | some x => reify c x | none => pure "(.k 0)"
        let bS ← match b with | some x => reify c x | none => pure ".nul"
        return s!"(.ext {p - c.cur - 1} {fi.rk} {tS} {aS} {bS})"
  if let .const cn _ := fn then
    if let some (rt, i) := findCtor c.tys cn then
      let args := e.getAppArgs
      let fs := args.extract rt.ti.params.size args.size
      let rs := rt.ti.roles[i]!
      unless fs.size == rs.size do throwError "frontx_ind: partial constructor application{indentExpr e}"
      let mut x := "(.k 0)"; let mut l := ".nul"; let mut r := ".nul"
      for j in [0:rs.size] do
        match rs[j]! with
        | .l => l ← reify c fs[j]!
        | .r => r ← reify c fs[j]!
        | .x _ => x ← reify c fs[j]!
        | .drop => pure ()  -- not in the byte format (`T.emb` ignores it)
      return s!"(.mk {i} {x} {l} {r})"
  -- instances (`+` on `Pos`, `++` on lists): unfold to the function
  let e' ← withTransparency .instances (whnf e)
  if e' != e then return ← reify c e'
  -- a function of a declared type not in the program yet: recorded, translated in the next round
  if let .const fnN _ := fn then
    if (← getEqnsFor? fnN).isSome && !(c.fns.any (·.name == fnN)) then
      if (← (do let _ ← fnInfo c.tys fnN; pure true) <|> pure false) then
        c.found.modify fun a => if a.contains fnN then a else a.push fnN
        return "(.ext 0 .w .nul (.k 0) .nul)"
  throwError "frontx_ind: unsupported term{indentExpr e}"
end

/-- the aliases and children of the node's pattern variables (constructor `i` of `r`) -/
def nodeAliases (r : RTy) (i : Nat) (fs : Array Expr) : Array (Expr × (Nat → String)) × Array (Expr × Bool) := Id.run do
  let rs := r.ti.roles[i]!
  let mut al := #[]; let mut kids := #[]
  for j in [0:fs.size] do
    match rs[j]! with
    | .l => al := al.push (fs[j]!, fun (_ : Nat) => ".l"); kids := kids.push (fs[j]!, false)
    | .r => al := al.push (fs[j]!, fun (_ : Nat) => ".r"); kids := kids.push (fs[j]!, true)
    | .x _ => al := al.push (fs[j]!, fun (_ : Nat) => ".x")
    | .drop => pure ()
  return (al, kids)

structure Arms where
  sIdx : Nat
  aIdx : Option Nat
  bIdx : Option Nat
  aSc : Option Sc
  arms : Array String
  small : Bool
  deriving Inhabited

/-- the arms of `g` (structural over `r`), one per constructor, from its equations -/
def armsOfEqns (g : Name) (r : RTy) (tys : Array RTy) (fns : Array FnI) (cur : Nat) (found : IO.Ref (Array Name)) :
    MetaM Arms := do
  let ti := r.ti
  let some eqns ← getEqnsFor? g | throwError "frontx_ind: no equations for {g}"
  let small ← IO.mkRef false
  let mut arms : Array (Option String) := ti.ctors.map fun _ => none
  let mut info : Option (Nat × Option Nat × Option Nat × Option Sc) := none
  for eqn in eqns do
    let r ← do
      let (hs, _, ty) ← forallMetaTelescope (← typeOfM eqn)
      let some (_, lhs, _) := ty.eq? | throwError "frontx_ind: bad equation {eqn}"
      let args := lhs.getAppArgs
      let mut sIdx? := none
      let mut ctorI := 0
      for j in [0:args.size] do
        if let .const cn _ := args[j]!.getAppFn then
          if let some i := ti.ctors.findIdx? (· == cn) then
            if sIdx?.isNone then sIdx? := some j; ctorI := i
      let some sIdx := sIdx? | throwError "frontx_ind: equation {eqn} has no constructor pattern"
      unless (← isDefEq (← inferType args[sIdx]!) ti.ty) do throwError "frontx_ind: {g} is not over the type"
      let ty ← instantiateMVars ty
      let some (_, lhs, rhs) := ty.eq? | throwError "frontx_ind: bad equation {eqn}"
      let args := lhs.getAppArgs
      for h in hs do
        if (← inferType h).isProp then throwError "frontx_ind: overlapping patterns ({eqn} has hypotheses)"
      -- other arguments must be variables (no patterns on them)
      for j in [0:args.size] do
        if j != sIdx then
          if let .const cn _ := args[j]!.getAppFn then
            if (findCtor tys cn).isSome then throwError "frontx_ind: a pattern on another argument ({eqn})"
      let sa := args[sIdx]!.getAppArgs
      let fs := sa.extract ti.params.size sa.size
      for j in [0:fs.size] do
        unless fs[j]!.isMVar do throwError "frontx_ind: nested patterns are not supported ({eqn})"
      let (al, kids) := nodeAliases r ctorI fs
      let (aIdx, bIdx, aSc) ← extraArgs tys args sIdx
      let c : Ctx := {
        g, nargs := args.size, ti, tys, als := al.push (args[sIdx]!, fun (_ : Nat) => ".me"), kids := kids,
        depth := 0, sIdx, aIdx, bIdx, params := args, small, fns, cur, found }
      pure (ctorI, (sIdx, aIdx, bIdx, aSc), ← reify c rhs)
    let (i, inf, s) := r
    arms := arms.set! i (some s)
    info := some inf
  let some (sIdx, aIdx, bIdx, aSc) := info | throwError "frontx_ind: no equations"
  let arms' ← arms.mapIdxM fun i a => match a with
    | some s => pure s
    | none => throwError "frontx_ind: no equation for constructor {ti.ctors[i]!}"
  return { sIdx, aIdx, bIdx, aSc, arms := arms', small := ← small.get }

/-- the arms of a `g` whose equations overlap (wildcard patterns, a match on several values): its body with the
structural argument replaced by each constructor -/
def armsOfCases (g : Name) (r : RTy) (tys : Array RTy) (fns : Array FnI) (cur : Nat) (found : IO.Ref (Array Name)) :
    MetaM Arms := do
  let ti := r.ti
  let ueq ← match ← getUnfoldEqnFor? g (nonRec := true) with
    | some u => pure u
    | none => throwError "frontx_ind: no unfolding equation for {g}"
  let small ← IO.mkRef false
  let mut arms := #[]
  let mut info := none
  for i in [0:ti.ctors.size] do
    let us := ti.ty.getAppFn.constLevels!
    let cty ← inferType (mkAppN (mkConst ti.ctors[i]! us) ti.params)
    let res ← forallTelescope cty fun fs _ => do
      let (_, _, ty) ← forallMetaTelescope (← typeOfM ueq)
      let some (_, lhs, _) := ty.eq? | throwError "frontx_ind: bad equation {ueq}"
      let args := lhs.getAppArgs
      let mut sIdx? := none
      for j in [0:args.size] do
        if sIdx?.isNone && args[j]!.isMVar then
          if (← whnfR (← inferType args[j]!)).getAppFn.isConstOf ti.ind then
            if ← isDefEq (← inferType args[j]!) ti.ty then sIdx? := some j
      let some sIdx := sIdx? | throwError "frontx_ind: {g} has no argument of the type"
      let ce := mkAppN (mkConst ti.ctors[i]! us) (ti.params ++ fs)
      unless ← isDefEq args[sIdx]! ce do throwError "frontx_ind: cannot instantiate {g}"
      let ty ← instantiateMVars ty
      let some (_, lhs, rhs) := ty.eq? | throwError "frontx_ind: bad equation {ueq}"
      let args := lhs.getAppArgs
      let rhs := rhs.headBeta
      let (al, kids) := nodeAliases r i fs
      let (aIdx, bIdx, aSc) ← extraArgs tys args sIdx
      let c : Ctx := {
        g, nargs := args.size, ti, tys, als := al.push (ce, fun (_ : Nat) => ".me"), kids := kids, depth := 0,
        sIdx, aIdx, bIdx, params := args, small, fns, cur, found }
      return ((sIdx, aIdx, bIdx, aSc), ← reify c rhs)
    arms := arms.push res.2
    info := some res.1
  let some (sIdx, aIdx, bIdx, aSc) := info | throwError "frontx_ind: a type without constructors"
  return { sIdx, aIdx, bIdx, aSc, arms, small := ← small.get }

def armsOf (g : Name) (r : RTy) (tys : Array RTy) (fns : Array FnI) (cur : Nat) (found : IO.Ref (Array Name)) :
    MetaM Arms := do
  try armsOfEqns g r tys fns cur found
  catch e =>
    try armsOfCases g r tys fns cur found catch e2 => throwError "{e.toMessageData}\n(by cases: {e2.toMessageData})"

def wfDefs : List String := ["Proven.Mach.Ind.indProg", "Proven.Mach.Ind.indProgM", "Proven.Mach.Ind.aC",
  "Proven.Mach.Ind.mainFn", "Proven.Mach.Ind.decFn",
  "Proven.Mach.Ind.encFn", "Proven.Mach.Ind.fFn", "Proven.Mach.Ind.fLoop", "Proven.Mach.Ind.disp",
  "Proven.Mach.Ind.arm", "Proven.Mach.Ind.armT", "Proven.Mach.Ind.E.ite?", "Proven.Mach.Ind.comp", "Proven.Mach.Ind.E.tail?", "Proven.Mach.Ind.loads",
  "Proven.Mach.Ind.dDisp", "Proven.Mach.Ind.dFlds", "Proven.Mach.Ind.dFld", "Proven.Mach.Ind.eDisp",
  "Proven.Mach.Ind.eFlds", "Proven.Mach.Ind.eFld", "Proven.Mach.Ind.rdB", "Proven.Mach.Ind.wrB",
  "Proven.Mach.Ind.alloc", "Proven.Mach.Ind.stW", "Proven.Mach.Ind.vE", "Proven.Mach.Ind.kE",
  "Proven.Mach.Ind.addE", "Proven.Mach.Ind.asg", "Proven.Mach.Ind.eqE", "List.mapIdx", "List.mapIdx.go",
  "List.getD"]

def rTyOfName (tn : Name) : TermElabM RTy := do
  let embTy ← inferType (← mkConstWithLevelParams (tn ++ `emb))
  return { tn, ti := ← analyze embTy.bindingDomain! }

def scTy : Option Sc → String
  | some .nat => "Nat" | some .u64 => "UInt64" | some .bool => "Bool" | none => "BitVec 64"


/-- one step of the `sem` proofs of functions that match on computed values: generalize a value `T.emb e`
(`e` a call, not a constructor application or a variable) and split it into its constructors -/
elab "frontx_emb_cases" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← instantiateMVars (← g.getType)
  let env ← getEnv
  let isCtor (e : Expr) : Bool := match e.getAppFn with
    | .const n _ => (env.find? n).any (·.isCtor)
    | _ => false
  let isEmb (s : Expr) : Bool := s.isApp && s.getAppNumArgs == 1 &&
      (match s.getAppFn with | .const n _ => n.componentsRev.head? == some `emb | _ => false)
  -- a call with variable arguments under `emb`
  let call? := t.find? fun s => isEmb s &&
      (let e := s.appArg!; !e.isFVar && !isCtor e && e.getAppFn.isConst && !e.hasLooseBVars &&
        e.getAppArgs.all fun a => a.isFVar || !(isCtor a || a.isApp))
  if let some s := call? then
    let stx ← Lean.Elab.Term.exprToSyntax s.appArg!
    Lean.Elab.Tactic.evalTactic (← `(tactic| generalize $stx = x at *))
    Lean.Elab.Tactic.evalTactic (← `(tactic| cases x))
    return
  -- a variable under `emb` matched on (a tag read)
  let var? := t.find? fun s => s.isApp &&
      (match s.getAppFn with
       | .const n _ => (match n.componentsRev.head? with
           | some (.str _ str) => str.startsWith "match_" | _ => false)
       | _ => false) &&
      s.getAppArgs.any fun a => isEmb a && a.appArg!.isFVar
  if let some s := var? then
    if let some a := s.getAppArgs.find? fun a => isEmb a && a.appArg!.isFVar then
      Lean.Elab.Tactic.evalTactic (← `(tactic| cases $(← Lean.Elab.Term.exprToSyntax a.appArg!):term))
      return
  throwError "frontx_emb_cases: nothing to split"

/-- the functions a function calls (other than itself), in order of appearance -/
def callees (tys : Array RTy) (fi : FnI) : MetaM (Array Name) := do
  let found ← IO.mkRef #[]
  discard <| armsOf fi.name fi.ty tys #[] 0 found
  return ← found.get

/-- the program: the function `g` first, then the functions it calls, each before the ones it calls -/
def programOf (tys : Array RTy) (g : Name) : MetaM (Array FnI) := do
  let mut infos : Array FnI := #[← fnInfo tys g]
  let mut edges : Array (Name × Array Name) := #[]
  let mut todo := #[g]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if edges.any (·.1 == n) then continue
    let fi := (infos.find? (·.name == n)).get!
    let cs ← callees tys fi
    edges := edges.push (n, cs)
    for m in cs do
      unless infos.any (·.name == m) do
        infos := infos.push (← fnInfo tys m)
        todo := todo.push m
  -- order: reverse post-order of a depth-first search from `g` (callers before callees)
  let mut order : Array Name := #[]
  let mut state : Array (Name × Nat) := #[]  -- 1 = on the stack, 2 = done
  let rec visit (fuel : Nat) (n : Name) (order : Array Name) (state : Array (Name × Nat)) :
      MetaM (Array Name × Array (Name × Nat)) := do
    match fuel with
    | 0 => throwError "frontx_ind: call graph too deep"
    | fuel + 1 =>
      match state.find? (·.1 == n) with
      | some (_, 1) => throwError "frontx_ind: recursion between functions ({n})"
      | some _ => return (order, state)
      | none =>
        let mut st := state.push (n, 1)
        let mut ord := order
        for m in ((edges.find? (·.1 == n)).map (·.2)).getD #[] do
          let (o, s) ← visit fuel m ord st
          ord := o; st := s
        st := st.map fun (k, v) => if k == n then (k, 2) else (k, v)
        return (ord.push n, st)
  let (o, _) ← visit 1000 g order state
  order := o.reverse
  return order.map fun n => (infos.find? (·.name == n)).get!

syntax "frontx_ind " ident " on " ident (" using " ident+)? : command
elab_rules : command
  | `(frontx_ind $f:ident on $T:ident $[using $Us*]?) => do
  let t0 ← IO.monoMsNow
  let embN ← liftCoreM (realizeGlobalConstNoOverloadWithInfo (mkIdentFrom T (T.getId ++ `emb)))
  let Tn := embN.getPrefix
  let mut uNs : Array Name := #[]
  for U in Us.getD #[] do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo (mkIdentFrom U (U.getId ++ `emb)))
    uNs := uNs.push n.getPrefix
  let fN ← liftCoreM (realizeGlobalConstNoOverloadWithInfo f)
  let fS := toString fN
  let r ← liftTermElabM do
    let tys ← (#[Tn] ++ uNs).mapM rTyOfName
    let rT := tys[0]!
    let ti := rT.ti
    let tyS ← ppFull ti.ty
    let finfo ← getConstInfo fN
    -- `f` recursive (it has equations matching a constructor), or an entry `f xs = g c₁ …`
    let recur ← match ← getEqnsFor? fN with
      | none => pure false
      | some eqns => eqns.anyM fun eqn => do
        let (_, _, ty) ← forallMetaTelescope (← typeOfM eqn)
        let some (_, lhs, _) := ty.eq? | pure false
        return lhs.getAppArgs.any fun a => a.getAppFn.isConst && (findCtor tys a.getAppFn.constName!).isSome
    let recur := recur || (← (do let _ ← fnInfo tys fN; pure (← getEqnsFor? fN).isSome) <|> pure false) &&
      (finfo.value?.map (fun v => v.find? (fun e => e.isConstOf fN) |>.isSome)).getD false
    let (gN, entry) ← if recur then pure (fN, none) else
      forallTelescope finfo.type fun xs _ => do
        let some v := finfo.value? | throwError "frontx_ind: {fN} has no definition"
        let body := (← instantiateLambda v xs).consumeMData
        let .const gN _ := body.getAppFn | throwError "frontx_ind: {fN} is neither recursive nor `g c₁ …`"
        unless (← getEqnsFor? gN).isSome do throwError "frontx_ind: {gN} has no equations"
        -- the entry's explicit parameters: the input value(s), the input word
        let mut eps := #[]
        for x in xs do
          if (← x.fvarId!.getBinderInfo).isExplicit then eps := eps.push x
        return (gN, some (body.getAppArgs, eps))
    let fns ← programOf tys gN
    -- translate every function (positions final)
    let mut armsA := #[]
    for i in [0:fns.size] do
      let found ← IO.mkRef #[]
      armsA := armsA.push (← armsOf fns[i]!.name fns[i]!.ty tys fns i found)
    -- the entry: inputs, the constant arguments
    let fi0 := fns[0]!
    let (bi, a0, aConst, bConst, twoIn, ain) ← match entry with
      | none => pure ((if fi0.bIdx.isSome then "Proven.Mach.Ind.BIn.inp" else "Proven.Mach.Ind.BIn.none"), "0", none,
          none, fi0.bIdx.isSome, false)
      | some (eargs, eps) => do
        let mut aC := none; let mut bC := none; let mut bi := "Proven.Mach.Ind.BIn.none"; let mut ain := false
        let mut two := false
        if let some i := fi0.aIdx then
          if eps.contains eargs[i]! then ain := true
          else
            let some n := (← whnf eargs[i]!).rawNatLit? <|> (eargs[i]!.getArg! 1).rawNatLit?
              | throwError "frontx_ind: the scalar argument of the entry must be a literal or a parameter{indentExpr eargs[i]!}"
            aC := some n
        if let some i := fi0.bIdx then
          if eps.contains eargs[i]! then bi := "Proven.Mach.Ind.BIn.inp"; two := true
          else
            let .const cn _ := eargs[i]!.getAppFn | throwError "frontx_ind: the second argument must be a nullary constructor"
            let some (_, ci) := findCtor tys cn | throwError "frontx_ind: the second argument must be a constructor"
            unless eargs[i]!.getAppNumArgs == ti.params.size do throwError "frontx_ind: the second argument must be nullary"
            bi := s!"(Proven.Mach.Ind.BIn.ctor {ci})"; bC := some ci
        pure (bi, toString (aC.getD 0), aC, bC, two, ain)
    -- per function: explicit argument texts, `Unit` arguments
    let mut gArgsA := #[]
    for fi in fns do
      let gExpl ← forallTelescope (← getConstInfo fi.name).type fun xs _ => xs.mapM fun x => do
        return (← x.fvarId!.getBinderInfo).isExplicit
      let gUnit ← do
        let (xs, _, _) ← forallMetaTelescope (← typeOfM fi.name)
        discard <| isDefEq (← inferType xs[fi.sIdx]!) fi.ty.ti.ty
        xs.mapM fun x => do
          let t ← whnfR (← instantiateMVars (← inferType x))
          return t.isConstOf ``Unit || t.isConstOf ``PUnit
      let mut gArgs := #[]
      for j in [0:fi.nargs] do
        if !gExpl[j]! then continue
        if j == fi.sIdx then gArgs := gArgs.push "t"
        else if fi.aIdx == some j then gArgs := gArgs.push "a"
        else if fi.bIdx == some j then gArgs := gArgs.push "b"
        else if gUnit[j]! then gArgs := gArgs.push "()"
        else throwError "frontx_ind: unexpected explicit argument {j} of {fi.name}"
      gArgsA := gArgsA.push gArgs
    -- the type of each function's `b` parameter
    let mut bTys := #[]
    for fi in fns do
      match fi.bIdx with
      | none => bTys := bTys.push none
      | some j =>
        let (xs, _, _) ← forallMetaTelescope (← typeOfM fi.name)
        discard <| isDefEq (← inferType xs[fi.sIdx]!) fi.ty.ti.ty
        let some rb ← findTy tys (← instantiateMVars (← inferType xs[j]!)) | throwError "frontx_ind: b type"
        bTys := bTys.push (some rb)
    let mut tyStrs := #[]
    for r in tys do tyStrs := tyStrs.push (r.tn, ← ppFull r.ti.ty)
    return (tyS, tys, fns, armsA, entry.isSome, bi, a0, aConst, bConst, twoIn, ain, gArgsA, bTys, tyStrs)
  let (tyS, tys, fns, armsA, isEntry, bi, a0, aConst, bConst, twoIn, ain, gArgsA, bTys, tyStrs) := r
  let ti := tys[0]!.ti
  let tyOf (tn : Name) : String := ((tyStrs.find? (·.1 == tn)).map (·.2)).getD "?"
  let pre (i : Nat) : String := if i == 0 then s!"{fS}.ind" else s!"{fS}.ind.h{i}"
  let words := "Proven.Frontx.Ind.bw_or, Proven.Frontx.Ind.bw_and, Proven.Frontx.Ind.bw_not, " ++
    "Proven.Frontx.Ind.bw_true, Proven.Frontx.Ind.bw_false, Proven.Frontx.Ind.nat_add"
  let words0 := words
  let cmpW := "Proven.Frontx.Ind.nat_ult, Proven.Frontx.Ind.nat_eq, Proven.Frontx.Ind.bw_eq0, Proven.Frontx.Ind.bw_eq0', " ++
    "Proven.Frontx.Ind.u64_ult, Proven.Frontx.Ind.u64_eq, Proven.Frontx.Ind.bool_eq, Proven.Frontx.Ind.u64_ops, " ++
    "Proven.Frontx.Ind.beq_dec"
  let allFolds := ", ".intercalate (tys.toList.flatMap fun r => (List.range r.ti.ctors.size).filter
    (fun k => !r.ti.roles[k]!.contains .drop) |>.map fun k => s!"{r.tn}.fold{k}")
  let embs := ", ".intercalate (tys.toList.map fun r => s!"{r.tn}.emb")
  let smalls := ", ".intercalate (tys.toList.map fun r => s!"{r.tn}.small")
  let cells := "Proven.Mach.Ind.C.tag, Proven.Mach.Ind.C.xv, Proven.Mach.Ind.C.lv, Proven.Mach.Ind.C.rv, " ++
    "Proven.Mach.Ind.Kd.pick, Proven.Mach.Ind.Kd.pair, Proven.Mach.Ind.semX, List.getD_cons_zero, List.getD_cons_succ"
  let multi := fns.size > 1
  let fnsS := ", ".intercalate (fns.toList.map fun f => toString f.name)
  let mut anySmall := false
  -- per function, last first: the program, its meaning
  for i' in [0:fns.size] do
    let i := fns.size - 1 - i'
    let fi := fns[i]!
    let A := armsA[i]!
    let P := pre i
    let later := ", ".intercalate ((List.range (fns.size - i - 1)).map fun j =>
      s!"⟨{fns[i + 1 + j]!.rk}, {pre (i + 1 + j)}.pg⟩")
    let xf := if i + 1 < fns.size then
      s!", X := Proven.Mach.Ind.semX [{later}], XA := Proven.Mach.Ind.alX [{later}]" else ""
    runCmd s!"def _root_.{P}.pg : Proven.Mach.Ind.Pg {fi.rk} := \{ arms := [{", ".intercalate A.arms.toList}]{xf} }"
    runCmd s!"theorem _root_.{P}.arms : {P}.pg.arms = [{", ".intercalate A.arms.toList}] := rfl"
    if i + 1 < fns.size then
      runCmd s!"theorem _root_.{P}.X : {P}.pg.X = Proven.Mach.Ind.semX [{later}] := rfl"
    let laterSems := ", ".intercalate ((List.range (fns.size - i - 1)).map fun j => s!"{pre (i + 1 + j)}.sem")
    let extra := (if i + 1 < fns.size then s!", {P}.X, {laterSems}" else "") ++ s!", {cells}"
    let small := A.small
    if small then anySmall := true
    if small && multi then throwError "frontx_ind: comparisons of `Nat`s in a program of several functions"
    let gS := toString fi.name
    let Ttn := fi.ty.tn
    let aTy := scTy fi.aSc
    let aRep := match fi.aSc with | some s => s.rep "a" | none => "a"
    let (bTy, bRep) := match bTys[i]! with
      | some rb => (tyOf rb.tn, s!"({rb.tn}.emb b)")
      | none => ("Proven.Mach.Ind.C", "b")
    let gApp := s!"({gS} {" ".intercalate gArgsA[i]!.toList})"
    let resRep := if fi.rk == ".t" then s!"({fi.rTy.get!.tn}.emb {gApp})" else fi.rSc.get!.rep gApp
    let folds := ", ".intercalate ((List.range fi.ty.ti.ctors.size).filter (fun k => !fi.ty.ti.roles[k]!.contains .drop) |>.map
      fun k => s!"{Ttn}.fold{k}")
    let hyps := if !small then "" else
      s!"{Ttn}.small t → " ++ (if fi.aSc == some .nat then "a < 2 ^ 64 → " else "") ++
        (match bTys[i]! with | some rb => s!"{rb.tn}.small b → " | none => "")
    let words := (if small then words ++ s!", {smalls}, {cmpW}" else words ++ s!", {cmpW}") ++ extra
    let caseB := if bTys[i]!.isSome then "cases b <;> " else ""
    runCmd s!"theorem _root_.{P}.sem : ∀ (t : {tyOf Ttn}) (a : {aTy}) (b : {bTy}), {hyps}{P}.pg.sem ({Ttn}.emb t) {aRep} {bRep} = {resRep} := by
  intro t; induction t <;> intro a b <;> intros <;>
  first
  | (simp_all [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {embs}, {words}]; done)
  | (simp_all [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {embs}, {words}] <;> rfl)
  | (simp only [{embs}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Bool.false_eq_true, if_true, if_false]
     simp only [{gS}]
     split <;> simp_all [{embs}, {words}]; done)
  | (simp only [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {embs}, {smalls},
      List.getElem?_cons_succ, List.getElem?_cons_zero] at *
     try simp (disch := omega) only [{cmpW}, decide_eq_false_iff_not, {words0}]
     repeat' split
     all_goals simp_all [{embs}, {words}]
     all_goals omega)
  | (simp only [{embs}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Bool.false_eq_true, if_true, if_false, {words}]
     try simp only [{folds}, Proven.Frontx.Ind.nat_add]
     try simp only [*]
     simp [{gS}, {embs}, {words}]; done)
  | ({caseB}simp_all [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {embs}, {words}]; done)
  | (simp only [{Ttn}.emb, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Bool.false_eq_true, if_true, if_false, {words}] at *
     try simp only [{allFolds}] at *
     try simp only [*{if i + 1 < fns.size then ", " ++ laterSems else ""}]
     first | rfl | (simp [{gS}, {embs}, {words}]; done) | (simp [{gS}, {embs}, {words}] <;> rfl))
  | ({caseB}(simp only [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {embs}, List.getElem?_cons_succ, List.getElem?_cons_zero] at *; repeat' split; all_goals simp_all [{embs}, {words}]); done)
  | (simp only [{Ttn}.emb, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Bool.false_eq_true, if_true, if_false, {words}] at *
     try simp only [*{if i + 1 < fns.size then ", " ++ laterSems else ""}]
     simp only [{gS}]
     repeat' (first | (simp_all [{fnsS}, {embs}, {words}, Proven.Op.eval]; done) |
       (simp_all [{fnsS}, {embs}, {words}, Proven.Op.eval] <;> rfl) |
       simp_all [{fnsS}, {embs}, {words}, Proven.Op.eval] | frontx_emb_cases)
     done)"
  -- the machine program
  let fi0 := fns[0]!
  let gN := fi0.name
  let gS := toString gN
  let rkS := fi0.rk
  let rSc := fi0.rSc
  let P := pre 0
  let small := anySmall
  let shO := match fi0.rTy with | some rt => s!"{rt.tn}.sh" | none => s!"{Tn}.sh"
  let oldForm := !multi && !ain && (fi0.rTy.map (·.tn == Tn)).getD true && fi0.ty.tn == Tn
  let nb := match rSc with | some .bool => 1 | _ => 8
  let res := if rkS == ".t" then 1 else 7
  let hsList := "[" ++ ", ".intercalate ((List.range (fns.size - 1)).map fun j => s!"⟨{fns[1 + j]!.rk}, {pre (1 + j)}.pg⟩") ++ "]"
  -- locals: the temporaries of the largest arm (`E.tmp`), at least 16
  let nl ← liftTermElabM do
    let mut m := 0
    for i in [0:fns.size] do
      let e ← Term.elabTerm (← `(List.foldr max 0 (List.map Proven.Mach.Ind.E.tmp $(mkIdent (if i == 0 then fN ++ `ind ++ `pg else fN ++ `ind ++ Name.mkSimple s!"h{i}" ++ `pg)).arms))) (some (mkConst ``Nat))
      let e ← instantiateMVars e
      let v ← withTransparency .all <| Meta.reduce e
      match v.rawNatLit? <|> v.nat? with
      | some n => m := max m n
      | none => throwError "frontx_ind: cannot compute the temporaries {v}"
    return max 16 (m + 9)
  let progS := if oldForm then s!"(Proven.Mach.Ind.indProg {Tn}.sh {P}.pg {bi} (BitVec.ofNat 64 {a0}) {nb})" else
    s!"(Proven.Mach.Ind.indProgM {Tn}.sh {shO} {P}.pg {hsList} {bi} {if ain then "true" else "false"} (BitVec.ofNat 64 {a0}) {nb} {nl})"
  let pgDefs := ", ".intercalate ((List.range fns.size).map fun i => s!"{pre i}.pg")
  let shDefs := ", ".intercalate (tys.toList.map fun r => s!"{r.tn}.sh")
  let wfT := s!"wf_calls [{", ".intercalate (wfDefs ++ [shDefs, pgDefs])}]"
  let nP := 4 + fns.size - 1
  let fsDisj := " ∨ ".intercalate ((List.range nP).map fun k => s!"f = {k}")
  let rfls := " | ".intercalate ((List.range nP).map fun _ => "rfl")
  runCmd s!"set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem _root_.{P}.wf : Proven.Mach.Riscv.WfProg1W {progS} (if {rkS} = Proven.Mach.Ind.Kd.t then 1 else 7) 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : {fsDisj} := by simp [Proven.Mach.Ind.indProg, Proven.Mach.Ind.indProgM] at hf; omega
    rcases this with {rfls} <;> {wfT}
  · {wfT}"
  runCmd s!"def _root_.{fS}.code : List (BitVec 32) := Proven.Mach.Riscv.callsCode1W {progS} {res} 0"
  -- the machine theorem: input type, encodings
  let bTn := match fi0.bIdx with | some _ => (bTys[0]!.map (·.tn)).getD Tn | none => Tn
  let inTyB := if twoIn then s!"{tyS} × {tyOf bTn}" else tyS
  let inTy := if ain then s!"{inTyB} × {scTy fi0.aSc}" else inTyB
  let pT := if ain then (if twoIn then "p.1.1" else "p.1") else (if twoIn then "p.1" else "p")
  let pB := if ain then "p.1.2" else "p.2"
  let pA := "p.2"
  let encIn := if twoIn then s!"{Tn}.enc {pT} ++ {bTn}.enc {pB}" else s!"{Tn}.enc {pT}"
  let encA := if ain then s!"(fun p : {inTy} => {encIn} ++ leN 8 {if fi0.aSc == some .nat then pA else s!"{pA}.toNat"})"
    else if twoIn then s!"{Tn}.enc2" else s!"{Tn}.enc"
  let gArgs := gArgsA[0]!
  let gP := gArgs.toList.map fun s => if s == "t" then pT else if s == "b" then pB else if s == "a" then
    (if ain then pA else toString (aConst.getD 0)) else s
  let fApp := if isEntry then
      (if ain || twoIn then s!"(fun p : {inTy} => {fS} {" ".intercalate (gP.filter (· != "()"))})" else s!"(fun t : {tyS} => {fS} t)")
    else if twoIn || ain then s!"(fun p : {inTy} => {gS} {" ".intercalate gP})"
    else s!"(fun t : {tyS} => {gS} {" ".intercalate gArgs.toList})"
  let encB := if rkS == ".t" then s!"{fi0.rTy.get!.tn}.enc" else match rSc with
    | some .bool => "(fun b : Bool => [if b then (1 : UInt8) else 0])"
    | _ => "(fun n : Nat => leN 8 n)"
  let v1 := if twoIn || ain then s!"(fun p : {inTy} => {Tn}.emb {pT})" else s!"{Tn}.emb"
  let v2 := if twoIn then s!"(fun p : {inTy} => {bTn}.emb {pB})" else s!"(fun _ : {inTy} => Proven.Mach.Ind.C.z)"
  let avS := if ain then s!"(fun p : {inTy} => {(fi0.aSc.getD .nat).rep pA})" else s!"(fun _ : {inTy} => (0 : BitVec 64))"
  let hencT := "fun g => rfl"
  let hencN := s!"fun g => by simp [Proven.Mach.Ind.inBytesA, Proven.Mach.Ind.inBytes, {Tn}.enc, {Tn}.enc2, {bTn}.enc, Proven.Frontx.Ind.leN8_ofNat, Proven.Frontx.Ind.leN8_mod]"
  let hw2T := if twoIn then s!"fun _ g => {bTn}.emb_wf g.{if ain then "1.2" else "2"}" else "fun h => nomatch h"
  let unfoldEntry := if isEntry then s!"show {encB} ({gS} {" ".intercalate (gArgs.toList.map fun s =>
    if s == "t" then (if ain || twoIn then pT.replace "p" "g" else "g") else if s == "a" then (if ain then "g.2" else toString (aConst.getD 0))
    else if s == "b" then (if twoIn then pB.replace "p" "g" else "_") else "_")}) = _; " else ""
  if fi0.aIdx.isSome && aConst.isNone && !ain then throwError "frontx_ind: a scalar parameter needs an entry `f xs = {gN} n xs`"
  let aS := if ain then "g.2" else match aConst with | some n => toString n | none => "(BitVec.ofNat 64 0)"
  let bS := if twoIn then pB.replace "p" "g" else match bConst with
    | some ci => s!"(@{ti.ctors[ci]!} {" ".intercalate (List.replicate ti.params.size "_")})"
    | none => "Proven.Mach.Ind.C.z"
  let tS := if ain || twoIn then pT.replace "p" "g" else "g"
  let semArgs := s!"{tS} {aS} {bS}"
  -- with the range hypothesis: the input is the subtype `{g // T.small g}`
  let smallP := s!"{Tn}.small {tS}" ++ (if ain && fi0.aSc == some .nat then " ∧ g.2 < 2 ^ 64" else "") ++
    (if twoIn then s!" ∧ {bTn}.small {bS}" else "")
  let semArgs := if !small then semArgs else
    semArgs ++ " hg.1" ++ (if fi0.aSc == some .nat then (if ain then (if twoIn then " hg.2.1" else " hg.2") else " (by decide)") else "") ++
      (if fi0.bIdx.isSome then (if twoIn then (if ain then " hg.2.2" else " hg.2") else s!" (by simp [{Tn}.small])") else "")
  let semArgs := if small && !ain && !twoIn then semArgs.replace " hg.1" " hg" else semArgs
  let smallP := if small then smallP else smallP
  let sub (fn : String) : String := if small then s!"(fun g : \{g : {inTy} // {smallP}} => {fn} g.1)" else fn
  let encA' := sub encA
  let fApp' := sub fApp
  let v1' := sub v1
  let v2' := sub v2
  let av' := sub avS
  let hw2T := if small && twoIn then s!"fun _ g => {bTn}.emb_wf g.1.{if ain then "1.2" else "2"}" else hw2T
  let hencN := if small then
      s!"fun g => by obtain ⟨g, hg⟩ := g; simp [Proven.Mach.Ind.inBytesA, Proven.Mach.Ind.inBytes, {Tn}.enc, {Tn}.enc2, {bTn}.enc, Proven.Frontx.Ind.leN8_ofNat, Proven.Frontx.Ind.leN8_mod]"
    else hencN
  let intro := if small then "obtain ⟨g, hg⟩ := g; dsimp only; " else ""
  let finish := if rkS == ".t" then "rfl" else match rSc with
    | some .bool => "exact Proven.Frontx.Ind.outBool _"
    | _ => "exact Proven.Frontx.Ind.outNat _"
  let hasA := if ain then "simp only [if_true]; " else "simp only [Bool.false_eq_true, if_false]; "
  let houtT := s!"fun g => by
      {intro}{unfoldEntry}have h := {P}.sem {semArgs}
      simp only [Proven.Mach.Ind.Kd.out, Proven.Mach.Ind.BIn.val]
      {if oldForm then "" else hasA}first
      | (simp only [{embs}] at h; rw [h]; {finish})
      | (rw [h]; {finish})"
  let rl := if rkS == ".t" then "true" else "false"
  let tryOld : CommandElabM Unit := runCmd s!"theorem _root_.{fS}.implements1 : Proven.Implements1With {encA'} {encB} {fS}.code {fApp'}
    (Proven.Frontx.Ind.space {P}.pg.M) (2 ^ 20) {rl} := by
  have := Proven.Frontx.Ind.implements1_ind {Tn}.sh {P}.pg {bi} (BitVec.ofNat 64 {a0}) {nb} {encA'} {encB} {fApp'} {v1'} {v2'}
    ({hencT}) (fun g => {Tn}.emb_wf _) ({hw2T})
    ({houtT})
    (by decide) (by decide) (by decide) (by unfold Proven.Mach.Ind.Pg.lin; decide) (by intro t h; cases h <;> decide)
    (by decide) (by decide) {P}.wf
  exact this"
  let ainS := if ain then "true" else "false"
  let tryL : CommandElabM Unit := runCmd s!"theorem _root_.{fS}.implements1 : Proven.Implements1With {encA'} {encB} {fS}.code {fApp'}
    (Proven.Frontx.Ind.spaceA 1 16 (fun n => {P}.pg.M * n)) (2 ^ 20) {rl} :=
  Proven.Frontx.Ind.implements1_indL {Tn}.sh {shO} {P}.pg {bi} {ainS} (BitVec.ofNat 64 {a0}) {nb} {encA'} {encB} {fApp'} {v1'} {v2'} {av'}
    ({hencN}) (fun g => {Tn}.emb_wf _) ({hw2T})
    ({houtT})
    (by decide) (by decide) (by decide) (by decide) (by unfold Proven.Mach.Ind.Pg.lin; decide) (by intro t h; cases h <;> decide)
    (by decide) {P}.wf"
  let chain := "⟨fun j hj => ⟨rfl, rfl⟩, " ++ String.join ((List.range (fns.size - 1)).map fun _ => "⟨fun j hj => ⟨rfl, rfl⟩, ") ++
    "trivial" ++ String.join ((List.range fns.size).map fun _ => "⟩")
  let chain := if fns.size == 1 then "⟨fun j hj => absurd hj (by simp), trivial⟩" else chain
  let tryS : CommandElabM Unit := runCmd s!"theorem _root_.{fS}.implements1 : Proven.Implements1With {encA'} {encB} {fS}.code {fApp'}
    (Proven.Frontx.Ind.spaceA {fns.size} {nl} (Proven.Mach.Ind.cellsSup {Tn}.sh {P}.pg {bi} {ainS} (BitVec.ofNat 64 {a0}))) (2 ^ 20) {rl} :=
  Proven.Frontx.Ind.implements1_indS {Tn}.sh {shO} {P}.pg {hsList} {bi} {ainS} (BitVec.ofNat 64 {a0}) {nb} {nl} {encA'} {encB} {fApp'} {v1'} {v2'} {av'}
    ({hencN}) (fun g => {Tn}.emb_wf _) ({hw2T})
    ({houtT})
    (by decide) (by decide) (by decide) (by first | exact {chain} | (simp only [Proven.Mach.Ind.Chain]; decide))
    (by decide) (by intro t h; cases h <;> decide) (by decide) {P}.wf"
  if oldForm && nl == 16 then
    try tryOld catch _ => tryS
  else if !multi && nl == 16 then
    try tryL catch _ => tryS
  else tryS
  let t1 ← IO.monoMsNow
  logInfo m!"frontx_ind: {fN}{if isEntry then m!" (entry of {gN})" else m!""} on {Tn}: {fns.size} function(s) {fns.map (·.name)}, {armsA[0]!.arms.size} arms, result {rkS}, {nl} locals; {t1 - t0} ms"

end Proven.Frontx.IndCmd
