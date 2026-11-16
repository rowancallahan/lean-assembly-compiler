/- `frontx_ind_type T := ty` and `frontx_ind f on T`: user inductives compiled as cells (`Riscv/Frontx/Ind.lean`).

`frontx_ind_type T := ty` (`ty` an inductive type, e.g. `BinTree Nat`): per constructor (tag = its index) the fields
in declaration order; a field of type `ty` is a child (`l`, then `r`; at most two), a `Nat` / `UInt64` / `Bool`
field the scalar `x` (at most one), any other field is DROPPED (not in the byte format; a function reading it is
rejected).  Generated: `T.sh` (the shape), `T.emb : ty → C`, `T.emb_wf`, `T.enc` (the input format: `C.enc T.sh ∘
T.emb`: tag byte, then the fields, `x` 8 bytes little-endian mod `2^64`), `T.enc2` (two values one after another).
A `UInt8` field is one byte (`Fld.b`); a `String` field, and with `nesting U, …` a field of type `U`, is a child of
another type of the same shape (`String`: `Bytes8`, its UTF-8 bytes, `Riscv/Frontx/IndStr.lean`), whose constructor
tags follow `ty`'s (`T.N1`, `T.N2`, … with `off`; NOTES section 23).

`frontx_ind f on T`: `f` is either structurally recursive over `ty` (one equation per constructor, from the
equation compiler), with at most one scalar parameter (`a`) and one more `ty` parameter (`b`, the second input), or
non-recursive with body `g c₁ …` for such a `g` (the scalar argument a literal, the `ty` argument a nullary
constructor).  The arms are read off `g`'s equations (`E` terms: fields, parameters, literals, `+`, `||`, `&&`, `!`,
constructors of `ty`, recursive calls on the children; calls in tail position become loops).  Generated, all proved
automatically: `f.pg`, `f.sem` (the program's meaning is `g`'s), `f.wf`, `f.code` and `f.implements1`. -/
import Riscv.Frontx.IndStr
import Riscv.Back.Calls

namespace Proven.Frontx.IndCmd
open Lean Meta Elab Command Term

def runCmd (s : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command ("set_option linter.unusedSimpArgs false in\n" ++ s) with
  | .ok stx => elabCommand stx
  | .error e => throwError "frontx_ind: generated text does not parse ({e}):\n{s}"

inductive Sc where | nat | u64 | bool | u8
  deriving BEq, Inhabited

def scOf? (t : Expr) : MetaM (Option Sc) := do
  let t ← whnfR t
  if t.isConstOf ``Nat then return some .nat
  if t.isConstOf ``UInt64 then return some .u64
  if t.isConstOf ``Bool then return some .bool
  if t.isConstOf ``UInt8 then return some .u8
  return none

/-- the word of a scalar `v` -/
def Sc.rep : Sc → String → String
  | .nat, v => s!"(BitVec.ofNat 64 {v})"
  | .u64, v => s!"({v}).toBitVec"
  | .bool, v => s!"(Proven.Frontx.Ind.bw {v})"
  | .u8, v => s!"(BitVec.ofNat 64 ({v}).toNat)"

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
  /-- per constructor and field: for a child of another type of the shape, that type (and whether the field is a
  `String`, embedded as `Bytes8.ofString`) -/
  kty : Array (Array (Option (Expr × Bool))) := #[]
  /-- per constructor and field: the extension cells to pass (through `r`) to reach the field's cell (NOTES
  section 25: a constructor with more than two children or one scalar continues in extension cells) -/
  hops : Array (Array Nat) := #[]
  /-- per constructor: its number of extension cells (their tags follow the type's constructors) -/
  next : Array Nat := #[]
  deriving Inhabited

/-- the cells of a constructor: per field its role in its cell (`l`, `r`, `x`) and the number of extension
cells before it.  If the fields fit one cell (at most two children, one scalar) they are as before; otherwise the
cell takes the longest prefix with at most one child and one scalar, and `r` points to an extension cell holding
the rest (the same rule again).  The byte order stays the declaration order. -/
def layout (rs0 : Array Role) : Array Role × Array Nat × Nat := Id.run do
  let mut rs := rs0
  let mut hs : Array Nat := rs0.map fun _ => 0
  let mut rest : List Nat := (List.range rs0.size).filter fun j => !(rs0[j]! matches .drop)
  let mut hop := 0
  let mut fuel := rs0.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    let isK (j : Nat) : Bool := rs0[j]! matches .l | .r
    let nk := (rest.filter isK).length
    let ns := (rest.filter (!isK ·)).length
    if nk ≤ 2 && ns ≤ 1 then
      let mut k := 0
      for j in rest do
        if isK j then
          rs := rs.set! j (if k == 0 then Role.l else Role.r); k := k + 1
        hs := hs.set! j hop
      return (rs, hs, hop)
    -- the longest prefix with at most one child and one scalar
    let mut k := 0; let mut sc := 0; let mut taken := 0
    for j in rest do
      if taken == 0 || (if isK j then k == 0 else sc == 0) then
        if (if isK j then k == 0 else sc == 0) then
          if isK j then k := k + 1 else sc := sc + 1
          taken := taken + 1
        else break
      else break
    for j in rest.take taken do
      if isK j then rs := rs.set! j Role.l
      hs := hs.set! j hop
    rest := rest.drop taken
    hop := hop + 1
  return (rs, hs, hop)

/-- `analyze ty nest`: the fields of `ty`'s constructors; a field of a type in `nest`, or a `String`, is a child of
that type (`String`: `Bytes8`) -/
def analyze (ty : Expr) (nest : Array Expr := #[]) : MetaM TyInfo := do
  let ty ← whnfR ty
  let .const ind _ := ty.getAppFn | throwError "frontx_ind_type: not an inductive type{indentExpr ty}"
  let some (.inductInfo iv) := (← getEnv).find? ind | throwError "frontx_ind_type: not an inductive type{indentExpr ty}"
  let params := ty.getAppArgs
  unless params.size == iv.numParams && iv.numIndices == 0 do throwError "frontx_ind_type: indexed families are not supported"
  let mut roles := #[]
  let mut hopsA := #[]
  let mut nextA := #[]
  let mut ftys := #[]
  let mut ktys := #[]
  let us := ty.getAppFn.constLevels!
  for c in iv.ctors do
    let cty ← inferType (mkAppN (mkConst c us) params)
    let (rs, fts, ks) ← forallTelescope cty fun xs _ => do
      let mut rs := #[]
      let mut fts := #[]
      let mut ks := #[]
      let mut kids := 0
      for x in xs do
        let ft ← inferType x
        fts := fts.push (toString (← withOptions (fun o => o.setBool `pp.fullNames true) (ppExpr ft)))
        let other ← do
          if (← whnfR ft).isConstOf ``String then pure (some (Lean.mkConst ``Proven.Frontx.Ind.Bytes8, true))
          else
            let mut o := none
            for n in nest do
              if o.isNone then if ← isDefEq ft n then o := some (n, false)
            pure o
        if (← isDefEq ft ty) || other.isSome then
          rs := rs.push (if kids == 0 then Role.l else Role.r)
          ks := ks.push other
          kids := kids + 1
        else match ← scOf? ft with
          | some s =>
            rs := rs.push (Role.x s); ks := ks.push none
          | none => rs := rs.push Role.drop; ks := ks.push none
      return (rs, fts, ks)
    let (rs', hs, ne) := layout rs
    roles := roles.push rs'
    hopsA := hopsA.push hs
    nextA := nextA.push ne
    ftys := ftys.push fts
    ktys := ktys.push ks
  return { ty, ind, params, ctors := iv.ctors.toArray, roles, ftys, kty := ktys, hops := hopsA, next := nextA }

/-- the number of tags of a type: its constructors, then their extension cells -/
def TyInfo.ntags (ti : TyInfo) : Nat := ti.ctors.size + ti.next.foldl (· + ·) 0

/-- the tag (relative to the type's first) of the `k`-th cell (`0` = the constructor's own) of constructor `i` -/
def TyInfo.cellTag (ti : TyInfo) (i k : Nat) : Nat :=
  if k == 0 then i else ti.ctors.size + ((ti.next.toList.take i).foldl (· + ·) 0) + (k - 1)

/-- the field's place read from a value `d` (a text): `hops` extension cells through `ft true`, then the slot -/
def TyInfo.fieldAt (ti : TyInfo) (i j : Nat) (d : String) : String := Id.run do
  let mut b := d
  for _ in [0:(ti.hops[i]?.bind (·[j]?)).getD 0] do b := s!"(.ft true {b})"
  match ti.roles[i]![j]! with
  | .l => return s!"(.ft false {b})"
  | .r => return s!"(.ft true {b})"
  | .x _ => return s!"(.fw true {b})"
  | .drop => return "?"

def TyInfo.hop (ti : TyInfo) (i j : Nat) : Nat := (ti.hops[i]?.bind (·[j]?)).getD 0

def roleFld : Role → Option String
  | .l => some ".l" | .r => some ".r" | .x .u8 => some ".b" | .x _ => some ".x" | .drop => none

/-- the type of a constant, its universe parameters fresh metavariables -/
def typeOfM (n : Name) : MetaM Expr := do
  let ci ← getConstInfo n
  let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
  return ci.instantiateTypeLevelParams us

def ppFull (e : Expr) : MetaM String := do
  return toString (← withOptions (fun o => o.setBool `pp.fullNames true)
    (ppExpr e))

/-- `wf_calls` (`Riscv/Back/Calls.lean`) for the larger programs of nested types: a length comparison whose
`decide` instance is too large is evaluated by `simp` -/
syntax "wf_calls_ind" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| wf_calls_ind [$ls,*]) => `(tactic|
    (simp [$ls,*, Proven.Mach.MachineC.wfF, Proven.Mach.MachineC.wfC, Proven.Mach.MachineF.wfB, Proven.Mach.BExp.depth,
      Proven.Mach.BExp.vlt, Proven.Mach.nlOf, Proven.Mach.MachineC.progOff, Proven.Mach.MachineC.offs,
      Proven.Mach.MachineC.lenF, Proven.Mach.MachineC.lenC, Proven.Mach.MachineC.lenStub, Proven.Mach.MachineC.posS,
      Proven.Mach.MachineC.lenArgs, Proven.Mach.MachineC.lenLi, Proven.Mach.argsC, Proven.Mach.padArgs, Proven.Mach.mgenB,
      Proven.Mach.setV, Proven.Mach.MachineF.compB, Proven.Mach.MachineF.codeF, Proven.Mach.MachineC.codeC,
      Proven.Mach.MachineC.encY, Proven.Mach.MachineF.encF, Proven.Mach.Riscv.rvC, Proven.Mach.Riscv.rvF,
      Proven.Mach.Riscv.rv, Proven.Mach.Riscv.core, Proven.Mach.Riscv.base, Proven.Mach.Riscv.enc,
      Proven.Mach.Riscv.encX, Proven.Mach.Riscv.encC, Proven.prologue, Proven.opCode,
      Proven.selCode, Proven.Mach.addrB, Proven.Mach.addrW, Proven.Mach.rk, Proven.Mach.avar,
      List.replicate, Proven.Mach.Riscv.gcLen, Proven.NS] <;>
      first | decide | simp [Proven.Mach.Riscv.glF]))

/-- the cell of constructor `i` (tag `off + i`) with field texts `fs`; `emb j v` embeds child field `j` -/
def cellS (ti : TyInfo) (i : Nat) (fs : Array String) (emb : Nat → String → String) (off : Nat := 0) : String := Id.run do
  let rs := ti.roles[i]!
  let ne := ti.next[i]?.getD 0
  let mut acc := ""
  for k' in [0:ne + 1] do
    let k := ne - k'
    let mut x := "0"; let mut l := "Proven.Mach.Ind.C.z"; let mut r := if k < ne then acc else "Proven.Mach.Ind.C.z"
    for j in [0:rs.size] do
      if ti.hop i j == k then
        match rs[j]! with
        | .l => l := emb j fs[j]!
        | .r => r := emb j fs[j]!
        | .x s => x := s.rep fs[j]!
        | .drop => pure ()
    acc := s!"(Proven.Mach.Ind.C.c {off + ti.cellTag i k} {x} {l} {r})"
  return acc

/-- the shape of a type: per constructor the fields of its cell (in declaration order, the extension last), then
the extension cells -/
def shapeOf (ti : TyInfo) : Array String := Id.run do
  let cellF (i k : Nat) : String := Id.run do
    let rs := ti.roles[i]!
    let mut fs : Array String := #[]
    for j in [0:rs.size] do
      if ti.hop i j == k then if let some f := roleFld rs[j]! then
        -- a `String` field: its length, then its bytes (`Fld.sl` / `Fld.sr`)
        let str := match (ti.kty[i]?.bind (·[j]?)).getD none with | some (_, true) => true | _ => false
        fs := fs.push (if str then (if f == ".l" then ".sl" else ".sr") else f)
    if k < ti.next[i]?.getD 0 then fs := fs.push ".r"
    return "[" ++ ", ".intercalate fs.toList ++ "]"
  let mut out := #[]
  for i in [0:ti.ctors.size] do out := out.push (cellF i 0)
  for i in [0:ti.ctors.size] do
    for k in [1:(ti.next[i]?.getD 0) + 1] do out := out.push (cellF i k)
  return out

/-- the name of the `k`-th type of the shape of `T` (`T` itself, then `T.N1`, `T.N2`, …) -/
def unionName (Tn : Name) (k : Nat) : Name := if k == 0 then Tn else Tn ++ Name.mkSimple s!"N{k}"

syntax "frontx_ind_type " ident " := " term (" nesting " term,+)? : command
elab_rules : command
  | `(frontx_ind_type $T:ident := $ty:term $[nesting $ns,*]?) => do
  let Tn := T.getId
  -- the types of the shape: `ty`, then (depth first) the types of its fields given in `nesting` and `Bytes8`
  -- for `String` fields; constructor tags are numbered through all of them
  let r : String × Array (String × TyInfo) ← liftTermElabM do
    let tyE ← elabType ty
    let mut nest0 : Array Expr := #[]
    for n in ns.map (·.getElems) |>.getD #[] do
      let e ← elabType n
      nest0 := nest0.push (← instantiateMVars e)
    synthesizeSyntheticMVarsNoPostponing
    let tyE ← instantiateMVars tyE
    let nest := nest0.push (Lean.mkConst ``Proven.Frontx.Ind.Bytes8)
    let mut U : Array (Expr × TyInfo) := #[(tyE, ← analyze tyE nest)]
    let mut k := 0
    while h : k < U.size do
      let ti := U[k].2
      for ks in ti.kty do
        for o in ks do
          if let some (t, _) := o then
            let mut known := false
            for (u, _) in U do if ← isDefEq u t then known := true
            unless known do U := U.push (t, ← analyze t nest)
      k := k + 1
    -- the types given in `nesting` are in the shape even when no field has them (a result type, e.g. `Option T`)
    for n in nest0 do
      let mut known := false
      for (u, _) in U do if ← isDefEq u n then known := true
      unless known do U := U.push (n, ← analyze n nest)
      -- and the types of their fields
      let mut k2 := U.size - 1
      while h : k2 < U.size do
        let ti := U[k2].2
        for ks in ti.kty do
          for o in ks do
            if let some (t, _) := o then
              let mut known2 := false
              for (u, _) in U do if ← isDefEq u t then known2 := true
              unless known2 do U := U.push (t, ← analyze t nest)
        k2 := k2 + 1
    -- the cells of strings (`Bytes8`) are the shape's last two tags (`Compiler/Ind.lean`, `sTag`)
    U := U.filter (fun (_, ti) => ti.ind != ``Proven.Frontx.Ind.Bytes8) ++ U.filter (fun (_, ti) => ti.ind == ``Proven.Frontx.Ind.Bytes8)
    let mut out : Array (String × TyInfo) := #[]
    for (t, ti) in U do out := out.push (← ppFull t, ti)
    return (← ppFull tyE, out)
  let us := r.2
  -- union indices of the children
  let idxOf (t : Expr) : CommandElabM Nat := liftTermElabM do
    for k in [0:us.size] do
      if ← isDefEq us[k]!.2.ty t then return k
    throwError "frontx_ind_type: a child type not in the shape"
  let mut offs := #[]
  let mut o := 0
  for (_, ti) in us do offs := offs.push o; o := o + ti.ntags
  -- per type, per constructor, per field: the embedding of a child (`Tk.emb`, a `String` through `Bytes8.ofString`)
  let mut kemb : Array (Array (Array (Option (String × Bool)))) := #[]
  for k in [0:us.size] do
    let ti := us[k]!.2
    let mut a := #[]
    for i in [0:ti.ctors.size] do
      let mut b := #[]
      for j in [0:ti.roles[i]!.size] do
        match ti.kty[i]![j]! with
        | some (t, str) =>
          let kk ← idxOf t
          b := b.push (some (s!"{unionName Tn kk}.emb", str))
        | none => b := b.push (if ti.roles[i]![j]! matches .l | .r then some (s!"{unionName Tn k}.emb", false) else none)
      a := a.push b
    kemb := kemb.push a
  let embF (k i : Nat) (j : Nat) (v : String) : String :=
    match kemb[k]![i]![j]! with
    | some (e, true) => s!"({e} (Proven.Frontx.Ind.Bytes8.ofString {v}))"
    | some (e, false) => s!"({e} {v})"
    | none => "?"
  let mut shParts := #[]
  for (_, ti) in us do
    shParts := shParts ++ shapeOf ti
  let shS := ", ".intercalate shParts.toList
  runCmd s!"def {Tn}.sh : Proven.Mach.Ind.Shape := [{shS}]"
  -- definitions per type, the types used by a type first
  -- (a topological order of the child-type relation: `List Level` after `Level`, whatever their positions)
  let mut deps : Array (Array Nat) := #[]
  for k in [0:us.size] do
    let mut d := #[]
    for ks in us[k]!.2.kty do
      for o2 in ks do
        if let some (t, _) := o2 then
          let kk ← idxOf t
          if kk != k && !d.contains kk then d := d.push kk
    deps := deps.push d
  let mut order : List Nat := []
  let mut fuel := us.size * us.size + 1
  while order.length < us.size && fuel > 0 do
    fuel := fuel - 1
    for k in [0:us.size] do
      if !order.contains k && deps[k]!.all (order.contains ·) then order := order ++ [k]
  if order.length < us.size then throwError "frontx_ind_type: the nested types depend on each other"
  for k in order do
    let (tS, ti) := us[k]!
    let Kn := unionName Tn k
    if k > 0 then
      runCmd s!"@[reducible] def {Kn}.sh : Proven.Mach.Ind.Shape := {Tn}.sh"
      runCmd s!"@[reducible] def {Kn}.off : Nat := {offs[k]!}"
    let mut alts := ""
    for i in [0:ti.ctors.size] do
      let fs := (List.range ti.roles[i]!.size).toArray.map fun j => s!"f{j}"
      let pat := s!"@{ti.ctors[i]!} " ++ " ".intercalate ((List.replicate ti.params.size "_") ++ fs.toList)
      alts := alts ++ s!"\n  | {pat} => {cellS ti i fs (embF k i) offs[k]!}"
    runCmd s!"def {Kn}.emb : {tS} → Proven.Mach.Ind.C{alts}"
    let mut salts := ""
    for i in [0:ti.ctors.size] do
      let rs := ti.roles[i]!
      let fs := (List.range rs.size).toArray.map fun j => s!"f{j}"
      let pat := s!"@{ti.ctors[i]!} " ++ " ".intercalate ((List.replicate ti.params.size "_") ++ fs.toList)
      let mut cs : Array String := #[]
      for j in [0:rs.size] do
        match rs[j]!, ti.kty[i]![j]! with
        | .l, none | .r, none => cs := cs.push s!"{Kn}.small {fs[j]!}"
        | .l, some (t, str) | .r, some (t, str) =>
          let kk ← idxOf t
          cs := cs.push s!"{unionName Tn kk}.small {if str then s!"(Proven.Frontx.Ind.Bytes8.ofString {fs[j]!})" else fs[j]!}"
        | .x .nat, _ => cs := cs.push s!"{fs[j]!} < 2 ^ 64"
        | _, _ => pure ()
      salts := salts ++ s!"\n  | {pat} => {if cs.isEmpty then "True" else " ∧ ".intercalate cs.toList}"
    runCmd s!"/-- every `Nat` field of the value is below `2^64` -/
def {Kn}.small : {tS} → Prop{salts}"
    for i in [0:ti.ctors.size] do
      if ti.roles[i]!.contains .drop then continue
      let fs := (List.range ti.roles[i]!.size).toArray.map fun j => s!"f{j}"
      let bs := " ".intercalate ((List.range fs.size).map fun j => s!"({fs[j]!} : {ti.ftys[i]![j]!})")
      let app := s!"(@{ti.ctors[i]!} " ++ " ".intercalate ((List.replicate ti.params.size "_") ++ fs.toList) ++ ")"
      runCmd s!"theorem {Kn}.fold{i} : {if fs.isEmpty then "" else "∀ " ++ bs ++ ","} {cellS ti i fs (embF k i) offs[k]!} = {Kn}.emb {app} := {if fs.isEmpty then "rfl" else "fun " ++ " ".intercalate fs.toList ++ " => rfl"}"
    let isB (kk : Nat) : Bool := us[kk]!.2.ind == ``Proven.Frontx.Ind.Bytes8
    if isB k then
      runCmd s!"theorem {Kn}.emb_str : ∀ t : {tS}, ({Kn}.emb t).IsStr {offs[k]!} := by
  intro t; induction t with
  | nil => exact ⟨[], rfl⟩
  | cons b r ih => obtain ⟨L, h⟩ := ih; exact ⟨b :: L, by simp only [{Kn}.emb, h, Proven.Mach.Ind.C.str]⟩"
    let wfs := ", ".intercalate (deps[k]!.toList.map fun kk =>
      s!"{unionName Tn kk}.emb_wfL" ++ (if isB kk then s!", {unionName Tn kk}.emb_str" else ""))
    runCmd s!"theorem {Kn}.emb_wf : ∀ t : {tS}, ({Kn}.emb t).wf {Tn}.sh := by
  intro t; induction t <;> simp_all [{Kn}.emb, Proven.Mach.Ind.C.wf, Proven.Mach.Ind.sTag, {Tn}.sh, Proven.Frontx.Ind.u8_lt, Proven.Frontx.Ind.u8_lt'{if wfs.isEmpty then "" else ", " ++ wfs}]"
    if us.size > 1 then
      runCmd s!"theorem {Kn}.emb_wfL : ∀ t : {tS}, ({Kn}.emb t).wf [{shS}] := {Kn}.emb_wf"
    if k > 0 then
      runCmd s!"/-- the format of `{tS}` in the shape of `{Tn}` -/
def {Kn}.enc (t : {tS}) : List UInt8 := ({Kn}.emb t).enc {Tn}.sh"
  let tyS := us[0]!.1
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
  /-- the tag of the first constructor (a type nested in another type's shape, `T.Nk`) -/
  off : Nat := 0
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
  /-- the result is a `Decidable p` (a `Bool`: `isTrue` is `1`) -/
  isDec : Bool := false
  deriving Inhabited

structure Ctx where
  g : Name
  nargs : Nat
  ti : TyInfo
  tys : Array RTy
  /-- expressions with a fixed translation (fields of the node, of matched values, the node itself, `let`s); the
  text from the number of enclosing `bind`s -/
  als : Array (Expr × (Nat → String))
  /-- the children of the current node: the extension cells passed, `false` = `l` -/
  kids : Array (Expr × Nat × Bool)
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

/-- the constructor `cn` of the declared type of `t` (constructor names are shared, e.g. by `List Level` and
`List Expr`) -/
def findCtorT (tys : Array RTy) (cn : Name) (t : Expr) : MetaM (Option (RTy × Nat)) := do
  for r in tys do
    if let some i := r.ti.ctors.findIdx? (· == cn) then
      if ← isDefEq t r.ti.ty then return some (r, i)
  return none

def findCtor (tys : Array RTy) (cn : Name) : Option (RTy × Nat) := Id.run do
  for r in tys do
    if let some i := r.ti.ctors.findIdx? (· == cn) then return some (r, i)
  return none

/-- the kind of a value of type `t` -/
def kindOf (c : Ctx) (t : Expr) : MetaM String := do
  if (← findTy c.tys t).isSome then return ".t"
  if (← whnfR t).isConstOf ``String then return ".t"
  if (← scOf? t).isSome then return ".w"
  throwError "frontx_ind: a value of unsupported type{indentExpr t}"

/-- the aliases of the fields of constructor `i` of `r` (pattern variables `fs`) read from the value `d` -/
def fieldAliases (r : RTy) (i : Nat) (fs : Array Expr) (d : Nat → String) : Array (Expr × (Nat → String)) := Id.run do
  let rs := r.ti.roles[i]!
  let mut out := #[]
  for j in [0:rs.size] do
    unless rs[j]! matches .drop do
      out := out.push (fs[j]!, fun (D : Nat) => r.ti.fieldAt i j (d D))
    -- a `String` field is its chain of bytes
    if let some (some (_, true)) := r.ti.kty[i]?.bind (·[j]?) then
      out := out.push (mkApp (mkConst ``Proven.Frontx.Ind.Bytes8.ofString) fs[j]!, fun (D : Nat) => r.ti.fieldAt i j (d D))
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
  if r.isAppOfArity ``Decidable 1 then return (".w", some .bool, none)
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
  -- the declared type of the argument itself (constructor names are shared between `List T`s)
  let rty := (← findTy tys (← instantiateMVars (← inferType xs[sIdx]!))).getD rty
  unless ← isDefEq (← inferType xs[sIdx]!) rty.ti.ty do throwError "frontx_ind: {g}: type mismatch"
  let (aIdx, bIdx, aSc) ← extraArgs tys xs sIdx
  let res ← instantiateMVars res
  let (rk, rSc, rTy) ← resKind tys res
  return { name := g, ty := rty, sIdx, aIdx, bIdx, aSc, nargs := xs.size, rk, rSc, rTy,
           isDec := res.isAppOfArity ``Decidable 1 }

/-- bytes per chunk function of a string literal -/
def strChunk : Nat := 6

/-- the function building bytes `[k * strChunk, (k + 1) * strChunk)` of the literal `str` in front of a chain -/
def strChunkName (g : Name) (str : String) (k : Nat) : Name :=
  g ++ `lit ++ Name.mkSimple s!"s{k}_{String.join (str.toUTF8.data.toList.map fun b => s!"{b.toNat}_")}"

partial def strLits : Expr → Array String
  | .lit (.strVal s) => #[s]
  | .app f a => strLits f ++ strLits a
  | .lam _ t b _ | .forallE _ t b _ => strLits t ++ strLits b
  | .letE _ t v b _ => strLits t ++ strLits v ++ strLits b
  | .mdata _ b | .proj _ _ b => strLits b
  | _ => #[]

/-- the free variables of `e`, outermost first, each once -/
partial def fvarsIn (e : Expr) : Array Expr :=
  let rec go (e : Expr) (acc : Array Expr) : Array Expr :=
    match e with
    | .fvar _ => if acc.contains e then acc else acc.push e
    | .app f a => go a (go f acc)
    | .mdata _ b => go b acc
    | _ => acc
  go e #[]

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
    if (← whnfR args[0]!).isConstOf ``String then return ← strEq c args[1]! args[2]!
    if (← findTy c.tys args[0]!).isSome then
      -- two values that are not constants: the program's function of the `DecidableEq` instance
      if (closedCtor c.tys args[1]!).isNone && (closedCtor c.tys args[2]!).isNone then
        let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
        return ← reify c (← withTransparency .instances (whnf inst)).headBeta
      return ← treeEq c args[1]! args[2]!
    cmpTy c args[0]!; return s!"(.bin .eq {← reify c args[1]!} {← reify c args[2]!})"
  | some ``Ne, 3 =>
    if (← whnfR args[0]!).isConstOf ``String then return s!"(.bin .xor {← strEq c args[1]! args[2]!} (.k 1))"
    if (← findTy c.tys args[0]!).isSome then return s!"(.bin .xor {← treeEq c args[1]! args[2]!} (.k 1))"
    cmpTy c args[0]!; return s!"(.bin .xor (.bin .eq {← reify c args[1]!} {← reify c args[2]!}) (.k 1))"
  | some ``Not, 1 => return s!"(.bin .xor {← reifyP c args[0]!} (.k 1))"
  | some ``And, 2 => return s!"(.bin .and {← reifyP c args[0]!} {← reifyP c args[1]!})"
  | some ``Or, 2 => return s!"(.bin .or {← reifyP c args[0]!} {← reifyP c args[1]!})"
  | _, _ => throwError "frontx_ind: unsupported condition{indentExpr p}"

/-- `a = b` on `String`s: `Bytes8.eqb` on their byte chains (a function of the program) -/
partial def strEq (c : Ctx) (a b : Expr) : MetaM String := do
  let oa := mkApp (mkConst ``Proven.Frontx.Ind.Bytes8.ofString) a
  let ob := mkApp (mkConst ``Proven.Frontx.Ind.Bytes8.ofString) b
  reify c (mkApp2 (mkConst ``Proven.Frontx.Ind.Bytes8.eqb) oa ob)

/-- `d = k` for a closed constructor term `k` (either side): the tags and the fields, recursively -/
partial def treeEq (c : Ctx) (a b : Expr) : MetaM String := do
  let (d, k) ← match closedCtor c.tys b, closedCtor c.tys a with
    | some _, _ => pure (a, b)
    | none, some _ => pure (b, a)
    | none, none => throwError "frontx_ind: `=` of two values of the type that are not constants{indentExpr a}"
  let dS ← reify c d
  treeEqS c dS k

partial def treeEqS (c : Ctx) (dS : String) (k : Expr) : MetaM String := do
  let some (r, i, fs) := closedCtor c.tys k | throwError "frontx_ind: not a constant{indentExpr k} (dS = {dS}) in {c.g}"
  let rs := r.ti.roles[i]!
  let mut acc := s!"(.bin .eq (.fw false {dS}) (.k (BitVec.ofNat 64 {r.off + i})))"
  for j in [0:rs.size] do
    match rs[j]! with
    | .l | .r => acc := s!"(.bin .and {acc} {← treeEqS c (r.ti.fieldAt i j dS) fs[j]!})"
    | .x _ => acc := s!"(.bin .and {acc} (.bin .eq {r.ti.fieldAt i j dS} {← reify c fs[j]!}))"
    | .drop => throwError "frontx_ind: `=` on a constructor with a field not in the byte format{indentExpr k}"
  return acc

/-- a `match`: split on the first discriminant that is not a constructor application (a value of a declared
type: on its tag, the pattern variables read from it; a `Bool` or an enumeration: on its value) -/
partial def reifyMatch (c : Ctx) (e : Expr) : MetaM (Option String) := do
  let some m ← matchMatcherApp? e | return none
  for pi in [0:2 * m.discrs.size] do
    let i := pi % m.discrs.size
    let pass := pi / m.discrs.size
    let d0 := m.discrs[i]!.consumeMData
    let mut d := d0
    let mut rebuild : Expr → Expr := fun ce =>
      mkAppN (mkConst m.matcherName m.matcherLevels.toList)
        (m.params ++ #[m.motive] ++ m.discrs.set! i ce ++ m.alts ++ m.remaining)
    -- a constructor application (a nested pattern `.const c []`): split on a variable field of it instead
    if let .const dn _ := d0.getAppFn then
      if let some (.ctorInfo _) := (← getEnv).find? dn then
        if pass == 0 then continue
        if let .reduced _ ← reduceMatcher? e then continue
        let mut found := false
        for a in fvarsIn d0 do
          if !found && a.isFVar then
            if let .const an _ := (← whnfR (← inferType a)).getAppFn then
              if let some (.inductInfo ai) := (← getEnv).find? an then
                -- the field the matcher is stuck on: every constructor of it reduces the matcher
                let aus := (← whnfR (← inferType a)).getAppFn.constLevels!
                let aargs := (← whnfR (← inferType a)).getAppArgs
                let mut all := true
                for cn in ai.ctors do
                  let ok ← forallTelescope (← inferType (mkAppN (mkConst cn aus) aargs)) fun fs _ => do
                    match ← reduceMatcher? (e.replaceFVar a (mkAppN (mkConst cn aus) (aargs ++ fs))) with
                    | .reduced _ => pure true
                    | _ => pure false
                  unless ok do all := false
                if all then
                  found := true; d := a
                  rebuild := fun ce => e.replaceFVar a ce
        -- no field on which every constructor reduces the matcher (a wildcard inside a nested pattern,
        -- `.lit (.natVal 0)` / `_`): the first field of a declared type or `Nat`, split on it
        if !found then
          for a in fvarsIn d0 do
            if !found then
              let at_ ← whnfR (← inferType a)
              if (← findTy c.tys at_).isSome || at_.isConstOf ``Nat then
                found := true; d := a
                rebuild := fun ce => e.replaceFVar a ce
        if !found then continue
    if pass == 1 && d == d0 then continue
    let dt ← whnfR (← inferType d)
    let .const tn us := dt.getAppFn | continue
    let some (.inductInfo iv) := (← getEnv).find? tn | continue
    if let .const dn _ := d.getAppFn then if iv.ctors.contains dn then continue
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
      -- in a shape of several types: the most frequent branch is the default, tests only for the others
      if c.tys.any (·.off > 0) then
        let cnt := fun (x : String) => (bs.filter (· == x)).size
        let dflt := bs.foldl (fun b x => if cnt x > cnt b then x else b) bs[bs.size - 1]!
        let mut acc := dflt
        for j' in [0:bs.size] do
          let j := bs.size - 1 - j'
          unless bs[j]! == dflt do
            acc := s!"(.ite (.bin .eq (.fw false {dT c1.depth}) (.k (BitVec.ofNat 64 {rt.off + j}))) {bs[j]!} {acc})"
        return some (wrap acc)
      let mut acc := bs[bs.size - 1]!
      for j' in [0:bs.size - 1] do
        let j := bs.size - 2 - j'
        -- the same branch as the rest: no test
        unless bs[j]! == acc do
          acc := s!"(.ite (.bin .eq (.fw false {dT c1.depth}) (.k (BitVec.ofNat 64 {rt.off + j}))) {bs[j]!} {acc})"
      return some (wrap acc)
    -- a `Nat` parameter or local (a match on a scalar together with a tree, `| 0, e => … | k + 1, .forallE _ b => …`):
    -- `0` or the successor of a new local `d - 1`
    if dt.isConstOf ``Nat && (d.isMVar || d.isFVar) then
      let dS ← reify c d
      c.small.set true
      let z ← branch c (rebuild (mkNatLit 0))
      let p := c.depth
      let sc ← withLocalDeclD `n (mkConst ``Nat) fun n => do
        let c' := { c with als := c.als.push (n, fun (D : Nat) => s!"(.var {D - 1 - p} .w)"), depth := c.depth + 1 }
        branch c' (rebuild (mkNatSucc n))
      return some s!"(.ite (.bin .eq {dS} (.k 0)) {z} (.bind (Proven.Frontx.Ind.natSub {dS} (.k (BitVec.ofNat 64 1))) {sc}))"
    -- an enumeration (`Bool`: `true` is constructor 1)
    -- (constructors whose fields are proofs count: `Decidable`, `isFalse` is constructor 0)
    let mut enum := true
    for cn in iv.ctors do
      let some (.ctorInfo _) := (← getEnv).find? cn | enum := false
      let cty ← inferType (mkAppN (mkConst cn us) dt.getAppArgs)
      let allProofs ← forallTelescope cty fun fs _ => fs.allM fun f => do isProp (← inferType f)
      unless allProofs do enum := false
    unless enum do continue
    let dS ← reify c d
    let mut bs := #[]
    for cn in iv.ctors do
      let cty ← inferType (mkAppN (mkConst cn us) dt.getAppArgs)
      bs := bs.push (← forallTelescope cty fun fs _ =>
        branch c (rebuild (mkAppN (mkConst cn us) (dt.getAppArgs ++ fs))))
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
  -- a string literal: the constant chain of its UTF-8 bytes (`Bytes8`, the type of a `String` field in memory), built
  -- `let x := nil; let x := f_k t x; …` by the chunk functions `strChunkName` (generated by `frontx_ind` for a
  -- constant; one function body cannot hold more than a few cells: conditional branches reach 4 KiB)
  if let .lit (.strVal str) := e then
    let b8 := Lean.mkConst ``Proven.Frontx.Ind.Bytes8
    let t ← instantiateMVars c.params[c.sIdx]!
    let mut v : Expr := .bvar 0
    for k in [0:(str.toUTF8.size + strChunk - 1) / strChunk] do
      v := .letE `x b8 (mkApp2 (Lean.mkConst (strChunkName c.tys[0]!.tn str k)) t (.bvar 0)) v false
    v := .letE `x b8 (Lean.mkConst ``Proven.Frontx.Ind.Bytes8.nil) v false
    return ← reify c v
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
  -- `Nat` subtraction: truncated at `0` (`natSub`; the values below `2^64`)
  if e.isAppOfArity ``HSub.hSub 6 then
    if (← whnfR (e.getArg! 0)).isConstOf ``Nat then
      c.small.set true
      return s!"(Proven.Frontx.Ind.natSub {← reify c (e.getArg! 4)} {← reify c (e.getArg! 5)})"
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
  if e.isAppOfArity ``Decidable.decide 2 then
    -- `a = b` of two values of a declared type: the program's function deciding it (`DecidableEq` instance)
    let p := e.getArg! 0
    if p.isAppOfArity ``Eq 3 then
      if (← findTy c.tys (p.getArg! 0)).isSome && (closedCtor c.tys (p.getArg! 1)).isNone &&
          (closedCtor c.tys (p.getArg! 2)).isNone then
        let inst ← withTransparency .instances (whnf (e.getArg! 1))
        return ← reify c inst.headBeta
    return ← reifyP c p
  if e.isAppOfArity ``Decidable.isTrue 2 then return "(.k 1)"
  if e.isAppOfArity ``Decidable.isFalse 2 then return "(.k 0)"
  if e.isAppOfArity ``dite 5 then
    let cnd := e.getArg! 1
    let cS ← reifyP c cnd
    let t ← withLocalDeclD `h cnd fun h => reify c (mkApp (e.getArg! 3) h).headBeta
    let f ← withLocalDeclD `h (mkNot cnd) fun h => reify c (mkApp (e.getArg! 4) h).headBeta
    return s!"(.ite {cS} {t} {f})"
  if e.isAppOfArity ``BEq.beq 4 then
    if (← whnfR (e.getArg! 0)).isConstOf ``String then return ← strEq c (e.getArg! 2) (e.getArg! 3)
    -- `a == b` on a declared type: its instance's function (`decide (a = b)`)
    if (← findTy c.tys (e.getArg! 0)).isSome then
      let mut e' := (← withTransparency .instances (whnf e)).headBeta
      -- `Name.beq a b := decide (a = b)`: unfold to the `decide`
      if let some (.defnInfo dv) := (← getEnv).find? (e'.getAppFn.constName?.getD Name.anonymous) then
        if (← lambdaTelescope dv.value fun _ b => pure b).isAppOfArity ``Decidable.decide 2 then
          if let some u ← unfoldDefinition? e' then e' := u.headBeta
      if e' != e then return ← reify c e'
    cmpTy c (e.getArg! 0); return s!"(.bin .eq {← reify c (e.getArg! 2)} {← reify c (e.getArg! 3)})"
  if e.isAppOfArity ``bne 4 then
    cmpTy c (e.getArg! 0); return s!"(.bin .xor (.bin .eq {← reify c (e.getArg! 2)} {← reify c (e.getArg! 3)}) (.k 1))"
  if let some s ← reifyMatch c e then return s
  let fn := e.getAppFn
  if fn.isConstOf c.g && e.getAppNumArgs == c.nargs then
    let args := e.getAppArgs
    let s := args[c.sIdx]!.consumeMData
    let (hop, ch) ← match c.kids.find? (fun (x, _) => s == x) with
      | some (_, h, ch) => pure (h, ch)
      | none => throwError "frontx_ind: a recursive call not on a child{indentExpr e}"
    let a ← match c.aIdx with | some i => reify c args[i]! | none => pure "(.k 0)"
    let b ← match c.bIdx with | some i => reify c args[i]! | none => pure ".nul"
    if hop == 0 then return s!"(.call {ch} {a} {b})"
    if hop == 1 then return s!"(.call2 true {ch} {a} {b})"
    throwError "frontx_ind: a recursive call on a field in a second extension cell{indentExpr e}"
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
    if let some (rt, i) ← findCtorT c.tys cn (← inferType e) then
      let args := e.getAppArgs
      let fs := args.extract rt.ti.params.size args.size
      let rs := rt.ti.roles[i]!
      unless fs.size == rs.size do throwError "frontx_ind: partial constructor application{indentExpr e}"
      let ne := rt.ti.next[i]?.getD 0
      let mut acc := ""
      for k' in [0:ne + 1] do
        let k := ne - k'
        let mut x := "(.k 0)"; let mut l := ".nul"; let mut r := if k < ne then acc else ".nul"
        for j in [0:rs.size] do
          if rt.ti.hop i j == k then
            match rs[j]! with
            | .l => l ← reify c fs[j]!
            | .r => r ← reify c fs[j]!
            | .x _ => x ← reify c fs[j]!
            | .drop => pure ()  -- not in the byte format (`T.emb` ignores it)
        acc := s!"(.mk {rt.off + rt.ti.cellTag i k} {x} {l} {r})"
      return acc
  -- instances (`+` on `Pos`, `++` on lists): unfold to the function
  let e' ← withTransparency .instances (whnf e)
  if e' != e then return ← reify c e'
  -- a constant (a definition without arguments) of a declared type: its value
  if let .const cn _ := e then
    if let some (.defnInfo dv) := (← getEnv).find? cn then
      if !dv.type.isForall && (← findTy c.tys dv.type).isSome then return ← reify c dv.value
  -- a function of a declared type not in the program yet: recorded, translated in the next round
  if let .const fnN _ := fn then
    if (← getEqnsFor? fnN).isSome && !(c.fns.any (·.name == fnN)) then
      if (← (do let _ ← fnInfo c.tys fnN; pure true) <|> pure false) then
        c.found.modify fun a => if a.contains fnN then a else a.push fnN
        -- the arguments of declared types may call functions too (string literals: their chunk functions)
        for a in e.getAppArgs do
          if (← findTy c.tys (← inferType a)).isSome && !(a.isFVar || a.isMVar) then
            discard <| (reify c a <|> pure "")
        return "(.ext 0 .w .nul (.k 0) .nul)"
  throwError "frontx_ind: unsupported term{indentExpr e}"
end

/-- the aliases and children of the node's pattern variables (constructor `i` of `r`) -/
def nodeAliases (r : RTy) (i : Nat) (fs : Array Expr) : Array (Expr × (Nat → String)) × Array (Expr × Nat × Bool) := Id.run do
  let rs := r.ti.roles[i]!
  let mut al := #[]; let mut kids := #[]
  for j in [0:fs.size] do
    let h := r.ti.hop i j
    -- in the node's own cell: the fields `.l`, `.r`, `.x`; in an extension cell: read from `r`
    let at_ : String := if h == 0 then
        (match rs[j]! with | .l => ".l" | .r => ".r" | .x _ => ".x" | .drop => "?")
      else Id.run do
        let mut b := ".r"
        for _ in [1:h] do b := s!"(.ft true {b})"
        return match rs[j]! with
          | .l => s!"(.ft false {b})" | .r => s!"(.ft true {b})" | .x _ => s!"(.fw true {b})" | .drop => "?"
    match rs[j]! with
    | .l => al := al.push (fs[j]!, fun (_ : Nat) => at_); kids := kids.push (fs[j]!, h, false)
    | .r => al := al.push (fs[j]!, fun (_ : Nat) => at_); kids := kids.push (fs[j]!, h, true)
    | .x _ => al := al.push (fs[j]!, fun (_ : Nat) => at_)
    | .drop => pure ()
    if let some (some (_, true)) := r.ti.kty[i]?.bind (·[j]?) then
      al := al.push (mkApp (mkConst ``Proven.Frontx.Ind.Bytes8.ofString) fs[j]!, fun (_ : Nat) => at_)
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
  "Proven.Frontx.Ind.natSub", "Proven.Mach.Ind.fLoopX", "Proven.Mach.Ind.fLoopS", "Proven.Mach.Ind.dispS",
  "Proven.Mach.Ind.armN", "Proven.Mach.Ind.dStr", "Proven.Mach.Ind.allocK", "Proven.Mach.Ind.eStr",
  "Proven.Mach.Ind.eCnt", "Proven.Mach.Ind.eBytes", "Proven.Mach.Ind.sTag",
  "List.getD"]

/-- the types of the shape of `T` after `T` itself (`T.N1`, `T.N2`, …) -/
def nestedNames (env : Environment) (tn : Name) : Array Name := Id.run do
  let mut out := #[]
  let mut k := 1
  while env.contains (unionName tn k ++ `emb) && k < 64 do
    out := out.push (unionName tn k); k := k + 1
  return out

def rTyOfName (tn : Name) : TermElabM RTy := do
  let env ← getEnv
  -- the root of a nested type `T.Nk` is `T`
  let root := if (env.contains (tn ++ `off)) then tn.getPrefix else tn
  let mut nest := #[]
  for n in nestedNames env root do
    nest := nest.push (← inferType (← mkConstWithLevelParams (n ++ `emb))).bindingDomain!
  let embTy ← inferType (← mkConstWithLevelParams (tn ++ `emb))
  let off ← if env.contains (tn ++ `off) then do
      let v ← whnf (← mkConstWithLevelParams (tn ++ `off))
      pure ((v.rawNatLit? <|> v.nat?).getD 0)
    else pure 0
  return { tn, ti := ← analyze embTy.bindingDomain! nest, off }

/-- an arm with a recursive call whose word argument grows (a sum, `d + 1` under a binder) -/
def armShifts (arm : String) : Bool := Id.run do
  let parts := (arm.splitOn "(.call ").drop 1 ++ (arm.splitOn "(.call2 ").drop 1
  for p in parts do
    let mut q := p
    for _ in [0:2] do
      if q.startsWith "true " then q := q.drop 5 |>.toString
      else if q.startsWith "false " then q := q.drop 6 |>.toString
    -- the word argument: up to the tree argument (a growing one is a sum, `d + 1`)
    if q.startsWith "(.bin .add" then return true
  return false

def scTy : Option Sc → String
  | some .nat => "Nat" | some .u64 => "UInt64" | some .bool => "Bool" | some .u8 => "UInt8" | none => "BitVec 64"


/-- the `sem` step for calls whose arguments are built terms (NOTES section 25, F3): for each call `f t a b` of a
function of the program in the goal (`fs`), the meaning theorem of `f` (`sems`, or an induction hypothesis) is
instantiated at those arguments (`b` a constructor term), its cells written out (`embs`), and used to rewrite -/
syntax "frontx_calls_sem" "[" ident,* "]" "[" ident,* "]" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
elab_rules : tactic
  | `(tactic| frontx_calls_sem [$fs,*] [$sems,*] [$ls,*]) => Lean.Elab.Tactic.withMainContext do
  let fNs ← fs.getElems.mapM fun f => Lean.Elab.realizeGlobalConstNoOverloadWithInfo f
  let semEs ← sems.getElems.mapM fun s => do mkConstWithLevelParams (← Lean.Elab.realizeGlobalConstNoOverloadWithInfo s)
  let g ← Lean.Elab.Tactic.getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (_, _, rhs) := t.eq? | return
  -- the calls in the expected value
  let calls := (Id.run do
      let mut out : Array Expr := #[]
      let mut todo : Array Expr := #[rhs]
      while h : todo.size > 0 do
        let e := todo[todo.size - 1]
        todo := todo.pop
        if let .const n _ := e.getAppFn then
          if fNs.contains n && !e.hasLooseBVars then out := out.push e
        for a in e.getAppArgs do todo := todo.push a
        if let .app f x := e then if !e.getAppFn.isConst then todo := todo.push f |>.push x
      return out)
  -- the lemmas: the meaning theorems and the local hypotheses (induction hypotheses)
  let mut lems : Array Expr := semEs
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isForall then lems := lems.push d.toExpr
  let mut k := 0
  if (← IO.getEnv "FRONTX_DEBUG").isSome then logInfo m!"calls {calls} lems {lems.size}"
  for c in calls do
    if (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty then return
    for L in lems do
      let ok ← withNewMCtxDepth (allowLevelAssignments := true) <| (do
        let (_, _, eq) ← forallMetaTelescope (← inferType L)
        let some (_, _, r) := eq.eq? | return false
        let mut found := false
        let mut todo : Array Expr := #[r]
        while h : todo.size > 0 do
          let e := todo[todo.size - 1]
          todo := todo.pop
          if !found && e.getAppFn == c.getAppFn && e.getAppNumArgs == c.getAppNumArgs then
            if ← isDefEq e c then found := true
          for a in e.getAppArgs do todo := todo.push a
        return found)
      if ok then
        -- instantiate for real, generalize what is left (the word argument, hypotheses)
        let (ms, _, eq) ← forallMetaTelescope (← inferType L)
        let some (_, _, r) := eq.eq? | continue
        let mut todo : Array Expr := #[r]
        let mut done := false
        while h : todo.size > 0 do
          let e := todo[todo.size - 1]
          todo := todo.pop
          if !done && e.getAppFn == c.getAppFn && e.getAppNumArgs == c.getAppNumArgs then
            if ← isDefEq e c then done := true
          for a in e.getAppArgs do todo := todo.push a
        let pf ← instantiateMVars (mkAppN L ms)
        let res ← abstractMVars pf
        let ty ← inferType res.expr
        let nm := Name.mkSimple s!"hcall{k}"
        k := k + 1
        let g ← Lean.Elab.Tactic.getMainGoal
        let g' ← g.assert nm ty res.expr
        let (_, g'') ← g'.intro1P
        Lean.Elab.Tactic.replaceMainGoal [g'']
        let hid := mkIdent nm
        try Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [$ls,*, UInt64.toBitVec_ofNat] at $hid:ident)) catch _ => pure ()
        try Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [$hid:ident])) catch _ => pure ()
        break

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

/-- `g`'s binders from `j` on, the fixed ones instantiated with their literals: the type and value of the
specialisation -/
partial def specOpen (g : Name) (n : Nat) (gc : Expr) (fixed : Array (Nat × Expr)) (j : Nat) (t : Expr)
    (ys args : Array Expr) : MetaM (Expr × Expr) := do
  if j ≥ n then return (← mkForallFVars ys t, ← mkLambdaFVars ys (mkAppN gc args))
  let .forallE nm d b bi := t | throwError "frontx_ind: {g}: arity"
  match (fixed.find? (·.1 == j)).map (·.2) with
  | some v => specOpen g n gc fixed (j + 1) (b.instantiate1 v) ys (args.push v)
  | none => withLocalDecl nm bi d fun y => specOpen g n gc fixed (j + 1) (b.instantiate1 y) (ys.push y) (args.push y)

/-- Specialisation of a function `g` at constant scalar arguments (NOTES section 36): the entry passes literals
`fixed` (argument index ↦ literal) to parameters that every recursive call of `g` passes unchanged.  Generates
`sN := fun rest => g (rest with the literals)` and its equations `sN.eq_k`, one per equation `g.eq_k` of `g`, with
`g lit…` replaced by `sN` (each proved by `g.eq_k` itself: `sN` unfolds to `g lit…`, kernel-checked by
definitional unfolding).  Lean takes `sN.eq_1 …` as `sN`'s equations (`getEqnsFor?`: already generated), so the
front end translates `sN` like a recursive function of one scalar parameter. -/
def specialise (g : Name) (fixed : Array (Nat × Expr)) (sN : Name) : MetaM Unit := do
  let some (.defnInfo gi) := (← getEnv).find? g | throwError "frontx_ind: {g} is not a definition"
  let lvls := gi.levelParams.map mkLevelParam
  let gc := Lean.mkConst g lvls
  let isFixed (j : Nat) : Option Expr := (fixed.find? (·.1 == j)).map (·.2)
  let some eqns ← getEqnsFor? g | throwError "frontx_ind: no equations for {g}"
  -- every recursive call passes the fixed parameters unchanged
  for eqn in eqns do
    forallTelescope (← inferType (mkConst eqn lvls)) fun _ ty => do
      let some (_, lhs, rhs) := ty.eq? | throwError "frontx_ind: bad equation {eqn}"
      let la := lhs.getAppArgs
      for (j, _) in fixed do
        unless la[j]!.isFVar do throwError "frontx_ind: {g}: a pattern on the parameter to specialise ({eqn})"
      let bad := rhs.find? fun e => e.isAppOfArity g la.size && fixed.any fun (j, _) => e.getArg! j != la[j]!
      if let some b := bad then throwError "frontx_ind: {g}: a recursive call changes the parameter to specialise{indentExpr b}"
  let n := gi.type.getForallArity
  let rw (e : Expr) : Expr := e.replace fun x =>
    if x.isAppOfArity g n && fixed.all (fun (j, v) => x.getArg! j == v) then
      some (mkAppN (mkConst sN lvls) ((List.range n).filter (fun j => (isFixed j).isNone) |>.toArray.map (x.getArg! ·)))
    else none
  let (ty, val) ← specOpen g n gc fixed 0 gi.type #[] #[]
  addDecl (.defnDecl { name := sN, levelParams := gi.levelParams, type := ty, value := val, hints := .regular 0, safety := .safe })
  -- the equations
  let mut k := 1
  for eqn in eqns do
    let (ety, pf) ← forallTelescope (← inferType (mkConst eqn lvls)) fun hs ty => do
      let some (_, lhs, _) := ty.eq? | throwError "frontx_ind: bad equation {eqn}"
      let la := lhs.getAppArgs
      let fv := fixed.map (la[·.1]!)
      let lits := fixed.map (·.2)
      let hs' := hs.filter fun h => !fv.contains h
      let ty' := rw (ty.replaceFVars fv lits)
      let hsArgs := hs.map fun h => match fv.idxOf? h with | some i => lits[i]! | none => h
      return (← mkForallFVars hs' ty', ← mkLambdaFVars hs' (mkAppN (mkConst eqn lvls) hsArgs))
    let eqN := sN ++ Name.mkSimple s!"eq_{k}"
    addDecl (.thmDecl { name := eqN, levelParams := gi.levelParams, type := ety, value := pf })
    k := k + 1

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
  -- the string literals of `f`, of the constants it unfolds to and of the functions of declared types it uses:
  -- chunk functions (`strChunkName`, once per literal and shape)
  let rootS ← liftTermElabM (do ppFull (← rTyOfName Tn).ti.ty)
  let lits ← liftTermElabM do
    let tys ← (#[Tn] ++ nestedNames (← getEnv) Tn).mapM rTyOfName
    let mut seen : Array Name := #[]; let mut todo := #[fN]; let mut ls : Array String := #[]
    while h : todo.size > 0 do
      let n := todo[todo.size - 1]; todo := todo.pop
      if seen.contains n then continue
      seen := seen.push n
      let some (.defnInfo dv) := (← getEnv).find? n | continue
      let ok ← forallTelescope dv.type fun xs r => do
        let mut ok := (← findTy tys r).isSome || n == fN
        for x in xs do if (← findTy tys (← inferType x)).isSome then ok := true
        return ok
      unless ok do continue
      ls := ls ++ strLits dv.value
      todo := todo ++ dv.value.getUsedConstants
    return ls
  for str in lits.toList.eraseDups do
    let bs := str.toUTF8.data.toList
    for k in [0:(bs.length + strChunk - 1) / strChunk] do
      let nm := strChunkName Tn str k
      unless (← getEnv).contains nm do
        let chunk := (bs.drop (k * strChunk)).take strChunk
        let body := chunk.foldr (fun b acc => s!"(Proven.Frontx.Ind.Bytes8.cons ({b.toNat} : UInt8) {acc})") "r"
        runCmd s!"def _root_.{nm} (t : {rootS}) (r : Proven.Frontx.Ind.Bytes8) : Proven.Frontx.Ind.Bytes8 := {body}"
  -- a constant (no arguments) of a declared type: the function `f.cst t := f` of an input tree `t` that it ignores
  let cstTy ← liftTermElabM do
    let ty ← whnfR (← getConstInfo fN).type
    if ty.isForall then return none
    let tys ← (#[Tn] ++ nestedNames (← getEnv) Tn).mapM rTyOfName
    return ← (do if (← findTy tys ty).isSome then pure (some (← ppFull ty)) else pure none)
  if let some tyS := cstTy then
    let cN := fN ++ `cst
    runCmd s!"def _root_.{cN} (t : {rootS}) : {tyS} := {fN}"
    let c := mkIdentFrom f cN
    elabCommand (← `(frontx_ind $c:ident on $T:ident $[using $Us*]?))
    return
  let r ← liftTermElabM do
    let env ← getEnv
    let tys ← (#[Tn] ++ nestedNames env Tn ++ uNs.flatMap (fun u => #[u] ++ nestedNames env u)).mapM rTyOfName
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
        -- `decide (a = b)`: the `DecidableEq` instance's function, its `Decidable` result as a `Bool`
        -- `a == b` (a `BEq` instance) and a definition `f a b := decide (a = b)` are unfolded to it
        let mut body := body
        for _ in [0:4] do
          if body.isAppOfArity ``Decidable.decide 2 then
            body := (← withTransparency .instances (whnf (body.getArg! 1))).headBeta
          else if body.isAppOfArity ``BEq.beq 4 then
            body := (← withTransparency .instances (whnf body)).headBeta
          else if let some b' ← unfoldDefinition? body then
            let b' := b'.headBeta
            if b'.isAppOfArity ``Decidable.decide 2 || b'.isAppOfArity ``BEq.beq 4 then body := b'
        -- a body that is not a call (a `match`, e.g. with default patterns): `f` itself is the function (by cases)
        let gN := match body.getAppFn with | .const g _ => (if body.getAppNumArgs == 0 then fN else g) | _ => fN
        let gN ← if (← getEqnsFor? gN).isSome then pure gN else pure fN
        if gN == fN then return (fN, none)
        -- two scalar parameters, one a literal that every recursive call passes unchanged: specialise `g` at it
        let gFail ← try (do let _ ← fnInfo tys gN; pure false)
          catch e => pure (((← e.toMessageData.toString).splitOn "more than one scalar").length > 1)
        let body0 := body
        let (gN, body1) ← if !gFail then pure (gN, body0) else do
          let sN := fN ++ `spec
          let bargs := body0.getAppArgs
          let mut cands := #[]
          for j in [0:bargs.size] do
            if (← scOf? (← inferType bargs[j]!)).isSome then
              let v ← instantiateMVars bargs[j]!
              if (v.rawNatLit? <|> (if v.isAppOfArity ``OfNat.ofNat 3 then (v.getArg! 1).rawNatLit? else none)).isSome then
                cands := cands.push (j, v)
          let mut done := false
          for (j, v) in cands do
            unless done do
              try
                if !(← getEnv).contains sN then specialise gN #[(j, v)] sN
                done := true
              catch _ => pure ()
          unless done do throwError "frontx_ind: {gN} has two scalar parameters and none is a literal it passes unchanged"
          let lv := (← getConstInfo gN).levelParams.map mkLevelParam
          let some (.defnInfo si) := (← getEnv).find? sN | throwError "frontx_ind: {sN}"
          -- the arguments of `g` but the fixed one (the one `sN`'s value applies to a literal)
          let fixedIdx ← lambdaTelescope si.value fun ys b => do
            let ba := b.getAppArgs
            return (List.range ba.size).filter (fun j => !(ys.contains ba[j]!))
          pure (sN, mkAppN (mkConst sN body0.getAppFn.constLevels!) ((List.range bargs.size).filter (fun j => !fixedIdx.contains j) |>.toArray.map (bargs[·]!)))
        -- the entry's explicit parameters: the input value(s), the input word
        let mut eps := #[]
        for x in xs do
          if (← x.fvarId!.getBinderInfo).isExplicit then eps := eps.push x
        return (gN, some (body1.getAppArgs, eps))
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
            let byType ← try findCtorT tys cn (← inferType eargs[i]!) catch _ => pure none
            let some (rb, ci) := byType <|> findCtor tys cn | throwError "frontx_ind: the second argument must be a constructor"
            unless eargs[i]!.getAppNumArgs == rb.ti.params.size do throwError "frontx_ind: the second argument must be nullary"
            bi := s!"(Proven.Mach.Ind.BIn.ctor {rb.off + ci})"; bC := some ci
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
    -- the entry's explicit parameters in order: which argument of `g` each one is (`t`, `a`, `b`)
    let entryRoles : Array String := match entry with
      | none => #[]
      | some (eargs, eps) => eps.map fun x =>
        if eargs[fi0.sIdx]? == some x then "t"
        else if (fi0.aIdx.bind (eargs[·]?)) == some x then "a"
        else if (fi0.bIdx.bind (eargs[·]?)) == some x then "b" else "?"
    return (tyS, tys, fns, armsA, entry.isSome, bi, a0, aConst, bConst, twoIn, ain, gArgsA, bTys, tyStrs, entryRoles)
  let (tyS, tys, fns, armsA, isEntry, bi, a0, aConst, bConst, twoIn, ain, gArgsA, bTys, tyStrs, entryRoles) := r
  let ti := tys[0]!.ti
  let tyOf (tn : Name) : String := ((tyStrs.find? (·.1 == tn)).map (·.2)).getD "?"
  let pre (i : Nat) : String := if i == 0 then s!"{fS}.ind" else s!"{fS}.ind.h{i}"
  let words := "Proven.Frontx.Ind.bw_or, Proven.Frontx.Ind.bw_and, Proven.Frontx.Ind.bw_not, " ++
    "Proven.Frontx.Ind.bw_true, Proven.Frontx.Ind.bw_false, Proven.Frontx.Ind.nat_add"
  let words0 := words
  let cmpW := "Proven.Frontx.Ind.nat_ult, Proven.Frontx.Ind.nat_eq, Proven.Frontx.Ind.bw_eq0, Proven.Frontx.Ind.bw_eq0', " ++
    "Proven.Frontx.Ind.u64_ult, Proven.Frontx.Ind.u64_eq, Proven.Frontx.Ind.bool_eq, Proven.Frontx.Ind.u64_ops, " ++
    "Proven.Frontx.Ind.beq_dec, Proven.Frontx.Ind.u8_eq, Proven.Frontx.Ind.Bytes8.eqb_ofString, " ++
    "Proven.Frontx.Ind.ev_natSub, Proven.Frontx.Ind.natSubW_ofNat"
  let allFolds := ", ".intercalate (tys.toList.flatMap fun r => (List.range r.ti.ctors.size).filter
    (fun k => !r.ti.roles[k]!.contains .drop) |>.map fun k => s!"{r.tn}.fold{k}")
  let embs := ", ".intercalate (tys.toList.map fun r => s!"{r.tn}.emb")
  let smalls := ", ".intercalate (tys.toList.map fun r => s!"{r.tn}.small")
  let cells := "Proven.Mach.Ind.C.tag, Proven.Mach.Ind.C.xv, Proven.Mach.Ind.C.lv, Proven.Mach.Ind.C.rv, " ++
    "Proven.Mach.Ind.Kd.pick, Proven.Mach.Ind.Kd.pair, Proven.Mach.Ind.semX, List.getD_cons_zero, List.getD_cons_succ"
  let multi := fns.size > 1
  let fnsS := ", ".intercalate (fns.toList.map fun f => toString f.name)
  let mut anySmall := false
  let mut nodesHyp := false
  -- per function, last first: the program, its meaning
  -- the loop of a function must fit the reach of a branch (`bz` over the loop body, about 1000 words): a larger
  -- one is compiled straight-line (`Pg.st`, every call a real call, one test per tag in sequence)
  let stA : Array Bool ← liftTermElabM do
    let termOf (str : String) : TermElabM Expr := do
      match Parser.runParserCategory (← getEnv) `term str with
      | .ok stx => do
        let e ← Term.elabTerm stx (some (mkConst ``Nat))
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
      | .error err => throwError "frontx_ind: {err}"
    let armsOfI (i : Nat) : String :=
      let fi := fns[i]!
      "[" ++ ", ".intercalate (List.replicate fi.ty.off (if fi.rk == ".t" then ".nul" else "(.k 0)") ++ armsA[i]!.arms.toList) ++ "]"
    let mut m := 0
    for i in [0:fns.size] do
      let e ← termOf s!"List.foldr max 0 (List.map Proven.Mach.Ind.E.tmp ({armsOfI i} : List (Proven.Mach.Ind.E {fns[i]!.rk} {fns[i]!.rk})))"
      let v ← withTransparency .all <| Meta.reduce e
      match v.rawNatLit? <|> v.nat? with
      | some n => m := max m n
      | none => throwError "frontx_ind: cannot compute the temporaries {v}"
    let nl0 := max 16 (m + 9)
    let mut out : Array Bool := #[]
    for i in [0:fns.size] do
      let e ← termOf s!"Proven.Mach.Riscv.rvC.lenC (List.replicate {4 + fns.size} (⟨3, {nl0}, .base (.assign 0 (.var 0)), .var 0⟩ : Proven.Mach.Fn)) [0, 3] [2] (Proven.Mach.Ind.fLoop {3 + i} (\{ arms := {armsOfI i} } : Proven.Mach.Ind.Pg {fns[i]!.rk}))"
      let n ← unsafe Meta.evalExpr Nat (mkConst ``Nat) e
      out := out.push (decide (n > 1000))
    return out
  for i' in [0:fns.size] do
    let i := fns.size - 1 - i'
    let fi := fns[i]!
    let A := armsA[i]!
    let P := pre i
    let later := ", ".intercalate ((List.range (fns.size - i - 1)).map fun j =>
      s!"⟨{fns[i + 1 + j]!.rk}, {pre (i + 1 + j)}.pg⟩")
    let xf := if i + 1 < fns.size then
      s!", X := Proven.Mach.Ind.semX [{later}], XA := Proven.Mach.Ind.alX [{later}]" else ""
    -- a function over a type nested in the shape: its tags start at the type's offset (no arms below)
    let armsL := List.replicate fi.ty.off (if fi.rk == ".t" then ".nul" else "(.k 0)") ++ A.arms.toList
    runCmd s!"def _root_.{P}.pg : Proven.Mach.Ind.Pg {fi.rk} := \{ arms := [{", ".intercalate armsL}]{xf}{if stA[i]! then ", st := true" else ""} }"
    runCmd s!"theorem _root_.{P}.arms : {P}.pg.arms = [{", ".intercalate armsL}] := rfl"
    if i + 1 < fns.size then
      runCmd s!"theorem _root_.{P}.X : {P}.pg.X = Proven.Mach.Ind.semX [{later}] := rfl"
    let laterSems := ", ".intercalate ((List.range (fns.size - i - 1)).map fun j => s!"{pre (i + 1 + j)}.sem")
    let extra := (if i + 1 < fns.size then s!", {P}.X, {laterSems}" else "") ++ s!", {cells}"
    -- a function calling a function that needs the range hypotheses needs them too
    let small := (List.range (fns.size - i)).any fun j => armsA[i + j]!.small
    if small then anySmall := true
    -- (`Nat` comparisons with several functions: each function's meaning carries its own range hypotheses)
    let gS := toString fi.name
    let Ttn := fi.ty.tn
    let aTy := scTy fi.aSc
    let aRep := match fi.aSc with | some s => s.rep "a" | none => "a"
    let (bTy, bRep) := match bTys[i]! with
      | some rb => (tyOf rb.tn, s!"({rb.tn}.emb b)")
      | none => ("Proven.Mach.Ind.C", "b")
    let gApp := s!"({gS} {" ".intercalate gArgsA[i]!.toList})"
    let resRep := if fi.rk == ".t" then s!"({fi.rTy.get!.tn}.emb {gApp})"
      else if fi.isDec then s!"(Proven.Frontx.Ind.bw (@decide _ {gApp}))" else fi.rSc.get!.rep gApp
    -- a specialisation `g.spec` (its value `fun … => g lit …`): `simp` unfolds it, so the original's equations too
    let gS ← liftTermElabM do
      if fi.name.getString! != "spec" then return gS
      let some (.defnInfo si) := (← getEnv).find? fi.name | return gS
      let some gO := (← lambdaTelescope si.value fun _ b => pure b.getAppFn.constName?) | return gS
      return s!"{gS}, {gO}"
    let folds := ", ".intercalate ((List.range fi.ty.ti.ctors.size).filter (fun k => !fi.ty.ti.roles[k]!.contains .drop) |>.map
      fun k => s!"{Ttn}.fold{k}")
    -- a recursive call with a word argument other than `a` (`d + 1` under a binder): the range hypothesis covers
    -- the growth along a path (`a + nodes < 2^64`)
    let shift := fns.size == 1 && fi.aSc == some .nat && A.arms.any armShifts
    if shift then nodesHyp := true
    let hyps := if !small then "" else
      s!"{Ttn}.small t → " ++ (if fi.aSc == some .nat then (if shift then s!"a + ({Ttn}.emb t).nodes < 2 ^ 64 → " else "a < 2 ^ 64 → ") else "") ++
        (match bTys[i]! with | some rb => s!"{rb.tn}.small b → " | none => "")
    let words := (if small then words ++ s!", {smalls}, {cmpW}" else words ++ s!", {cmpW}") ++ extra
    let caseB := if bTys[i]!.isSome then "cases b <;> " else ""
    runCmd s!"set_option maxHeartbeats 16000000 in
theorem _root_.{P}.sem : ∀ (t : {tyOf Ttn}) (a : {aTy}) (b : {bTy}), {hyps}{P}.pg.sem ({Ttn}.emb t) {aRep} {bRep} = {resRep} := by
  intro t; induction t <;> intro a b <;> intros <;>
  first
  | (simp_all [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {embs}, {words}]; done)
  | (simp_all [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {embs}, {words}] <;> rfl)
  | (simp only [{embs}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Bool.false_eq_true, if_true, if_false]
     simp only [{gS}]
     split <;> simp_all [{embs}, {words}]; done)
  | (simp only [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {embs}, {smalls},
      List.getElem?_cons_succ, List.getElem?_cons_zero, Proven.Mach.Ind.C.nodes] at *
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
     done)
  | ({caseB}simp_all [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {embs}, {smalls}, {words}, {cmpW}, Proven.Frontx.Ind.bw_eqz{extra}] <;>
     (repeat' split) <;> simp_all [Proven.Frontx.Ind.bw]; done)
  | (simp only [{gS}, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, {embs}, {smalls}, List.getElem?_cons_succ,
      List.getElem?_cons_zero, List.getElem?_nil, Bool.false_eq_true, if_false, if_true] at *
     try simp only [Proven.Mach.Ind.C.nodes] at *
     simp (disch := first | omega | (simp_all; done)) only [*, {cmpW}, {words0}, ↓reduceIte, ite_true, ite_false{extra}]
     all_goals (try simp (disch := first | omega | (simp_all; done)) only [Proven.Mach.Ind.ev, Proven.Frontx.Ind.natSubW_ofNat,
       Proven.Frontx.Ind.nat_add, Proven.Frontx.Ind.bw_eq0, Proven.Frontx.Ind.bw_eq0', decide_eq_false_iff_not,
       decide_eq_true_eq] at *)
     all_goals (repeat' split)
     all_goals (simp_all [{embs}, Proven.Frontx.Ind.bw]; try omega)
     done)
  | (simp only [{Ttn}.emb, {P}.arms, Proven.Mach.Ind.Pg.sem, Proven.Mach.Ind.ev, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Bool.false_eq_true, if_true, if_false, {words}] at *
     all_goals try simp only [*{if i + 1 < fns.size then ", " ++ laterSems else ""}]
     all_goals try simp only [{gS}]
     all_goals frontx_calls_sem [{fnsS}] [{laterSems}] [{embs}]
     all_goals first | rfl | (simp_all [{fnsS}, {embs}, {words}]; done))"
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
  let progS := if oldForm && nl == 16 then s!"(Proven.Mach.Ind.indProg {Tn}.sh {P}.pg {bi} (BitVec.ofNat 64 {a0}) {nb})" else
    s!"(Proven.Mach.Ind.indProgM {Tn}.sh {shO} {P}.pg {hsList} {bi} {if ain then "true" else "false"} (BitVec.ofNat 64 {a0}) {nb} {nl})"
  let pgDefs := ", ".intercalate ((List.range fns.size).map fun i => s!"{pre i}.pg")
  let shDefs := ", ".intercalate (tys.toList.map fun r => s!"{r.tn}.sh")
  let wfT := s!"{if tys.any (·.off > 0) then "wf_calls_ind" else "wf_calls"} [{", ".intercalate (wfDefs ++ [shDefs, pgDefs])}]"
  let nP := 4 + fns.size - 1
  let fsDisj := " ∨ ".intercalate ((List.range nP).map fun k => s!"f = {k}")
  let rfls := " | ".intercalate ((List.range nP).map fun _ => "rfl")
  runCmd s!"set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 4000000 in
theorem _root_.{P}.wf : Proven.Mach.Riscv.WfProg1W {progS} (if {rkS} = Proven.Mach.Ind.Kd.t then 1 else 7) 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : {fsDisj} := by simp [Proven.Mach.Ind.indProg, Proven.Mach.Ind.indProgM] at hf; omega
    rcases this with {rfls} <;> first | ({wfT}; done) | (simp [Proven.Mach.Ind.indProg, Proven.Mach.Ind.indProgM] at hf; done) | ({wfT})
  · {wfT}"
  runCmd s!"def _root_.{fS}.code : List (BitVec 32) := Proven.Mach.Riscv.callsCode1W {progS} {res} 0"
  -- the machine theorem: input type, encodings
  -- the type of the structural argument (the root of the shape, or a type nested in it)
  let T0 := fi0.ty.tn
  let tyS0 := tyOf T0
  let bTn := match fi0.bIdx with | some _ => (bTys[0]!.map (·.tn)).getD Tn | none => Tn
  let inTyB := if twoIn then s!"{tyS0} × {tyOf bTn}" else tyS0
  let inTy := if ain then s!"{inTyB} × {scTy fi0.aSc}" else inTyB
  let pT := if ain then (if twoIn then "p.1.1" else "p.1") else (if twoIn then "p.1" else "p")
  let pB := if ain then "p.1.2" else "p.2"
  let pA := "p.2"
  let encIn := if twoIn then s!"{T0}.enc {pT} ++ {bTn}.enc {pB}" else s!"{T0}.enc {pT}"
  let encA := if ain then s!"(fun p : {inTy} => {encIn} ++ leN 8 {if fi0.aSc == some .nat then pA else s!"{pA}.toNat"})"
    else if twoIn then (if T0 == Tn && bTn == Tn then s!"{Tn}.enc2" else s!"(fun p : {inTy} => {encIn})") else s!"{T0}.enc"
  let gArgs := gArgsA[0]!
  let gP := gArgs.toList.map fun s => if s == "t" then pT else if s == "b" then pB else if s == "a" then
    (if ain then pA else toString (aConst.getD 0)) else s
  let eP := entryRoles.toList.map fun s => if s == "t" then pT else if s == "b" then pB else if s == "a" then pA else s
  let fApp := if isEntry then
      (if ain || twoIn then s!"(fun p : {inTy} => {fS} {" ".intercalate eP})" else s!"(fun t : {tyS0} => {fS} t)")
    else if twoIn || ain then s!"(fun p : {inTy} => {gS} {" ".intercalate gP})"
    else s!"(fun t : {tyS0} => {gS} {" ".intercalate gArgs.toList})"
  let encB := if rkS == ".t" then s!"{fi0.rTy.get!.tn}.enc" else match rSc with
    | some .bool => "(fun b : Bool => [if b then (1 : UInt8) else 0])"
    | _ => "(fun n : Nat => leN 8 n)"
  let v1 := if twoIn || ain then s!"(fun p : {inTy} => {T0}.emb {pT})" else s!"{T0}.emb"
  let v2 := if twoIn then s!"(fun p : {inTy} => {bTn}.emb {pB})" else s!"(fun _ : {inTy} => Proven.Mach.Ind.C.z)"
  let avS := if ain then s!"(fun p : {inTy} => {(fi0.aSc.getD .nat).rep pA})" else s!"(fun _ : {inTy} => (0 : BitVec 64))"
  let hencT := "fun g => rfl"
  let hencN := s!"fun g => by simp [Proven.Mach.Ind.inBytesA, Proven.Mach.Ind.inBytes, {Tn}.enc, {Tn}.enc2, {T0}.enc, {bTn}.enc, Proven.Frontx.Ind.leN8_ofNat, Proven.Frontx.Ind.leN8_mod]"
  let hw2T := if twoIn then s!"fun _ g => {bTn}.emb_wf g.{if ain then "1.2" else "2"}" else "fun h => nomatch h"
  let unfoldEntry := if isEntry then s!"show {encB} ({if fi0.isDec then "@decide _ (" else ""}{gS} {" ".intercalate (gArgs.toList.map fun s =>
    if s == "t" then (if ain || twoIn then pT.replace "p" "g" else "g") else if s == "a" then (if ain then "g.2" else toString (aConst.getD 0))
    else if s == "b" then (if twoIn then pB.replace "p" "g" else "_") else "_")}){if fi0.isDec then ")" else ""} = _; " else ""
  if fi0.aIdx.isSome && aConst.isNone && !ain then throwError "frontx_ind: a scalar parameter needs an entry `f xs = {gN} n xs`"
  let aS := if ain then "g.2" else match aConst with | some n => toString n | none => "(BitVec.ofNat 64 0)"
  let bTi : TyInfo := match fi0.bIdx with | some _ => ((bTys[0]!.map (fun (r : RTy) => r.ti)).getD ti) | none => ti
  let bS := if twoIn then pB.replace "p" "g" else match bConst with
    | some ci => s!"(@{bTi.ctors[ci]!} {" ".intercalate (List.replicate bTi.params.size "_")})"
    | none => "Proven.Mach.Ind.C.z"
  let tS := if ain || twoIn then pT.replace "p" "g" else "g"
  let semArgs := s!"{tS} {aS} {bS}"
  -- with the range hypothesis: the input is the subtype `{g // T.small g}`
  let smallP := s!"{T0}.small {tS}" ++ (if ain && fi0.aSc == some .nat then " ∧ g.2 < 2 ^ 64" else "") ++
    (if twoIn then s!" ∧ {bTn}.small {bS}" else "")
  let semArgs := if !small then semArgs else
    semArgs ++ " hg.1" ++ (if fi0.aSc == some .nat then (if ain then (if twoIn then " hg.2.1" else " hg.2") else " (by decide)") else "") ++
      (if fi0.bIdx.isSome then (if twoIn then (if ain then " hg.2.2" else " hg.2") else s!" (by simp [{Tn}.small])") else "")
  let semArgs := if small && !ain && !twoIn then semArgs.replace " hg.1" " hg" else semArgs
  -- the range hypothesis `a + nodes < 2^64` (a word argument that grows along a path)
  let nodesS := s!"({T0}.emb {tS}).nodes"
  let (smallP, semArgs) := if !(small && nodesHyp) then (smallP, semArgs) else
    let bS' := if fi0.bIdx.isSome then (if twoIn then (if ain then " hg.2.2" else " hg.2.1") else s!" (by simp [{Tn}.small])") else ""
    if ain then
      (s!"{T0}.small {tS} ∧ g.2 + {nodesS} < 2 ^ 64" ++ (if twoIn then s!" ∧ {bTn}.small {bS}" else ""),
        s!"{tS} {aS} {bS} hg.1" ++ (if twoIn then " hg.2.1" else " hg.2") ++ bS')
    else
      (s!"{T0}.small {tS}" ++ (if twoIn then s!" ∧ {bTn}.small {bS}" else "") ++ s!" ∧ {nodesS} < 2 ^ 64",
        s!"{tS} {aS} {bS} hg.1" ++ (if twoIn then " (by have := hg.2.2; omega)" else " (by have := hg.2; omega)") ++ bS')
  let smallP := if small then smallP else smallP
  let sub (fn : String) : String := if small then s!"(fun g : \{g : {inTy} // {smallP}} => {fn} g.1)" else fn
  let encA' := sub encA
  let fApp' := sub fApp
  let v1' := sub v1
  let v2' := sub v2
  let av' := sub avS
  let hw2T := if small && twoIn then s!"fun _ g => {bTn}.emb_wf g.1.{if ain then "1.2" else "2"}" else hw2T
  let hencN := if small then
      s!"fun g => by obtain ⟨g, hg⟩ := g; simp [Proven.Mach.Ind.inBytesA, Proven.Mach.Ind.inBytes, {Tn}.enc, {Tn}.enc2, {T0}.enc, {bTn}.enc, Proven.Frontx.Ind.leN8_ofNat, Proven.Frontx.Ind.leN8_mod]"
    else hencN
  let intro := if small then "obtain ⟨g, hg⟩ := g; dsimp only; " else ""
  let finish := if rkS == ".t" then "rfl" else match rSc with
    | some .bool => "exact Proven.Frontx.Ind.outBool _"
    | _ => "exact Proven.Frontx.Ind.outNat _"
  -- calls on grandchildren (extension cells) are outside the linear cell bound: `cellsSup`
  let lin := !(armsA.any (·.arms.any (·.contains ".call2")))
  let hasA := if ain then "try simp only [if_true]
      " else "try simp only [Bool.false_eq_true, if_false, ↓reduceIte]
      "
  let houtT := s!"fun g => by
      {intro}{unfoldEntry}have h := {P}.sem {semArgs}
      simp only [Proven.Mach.Ind.Kd.out, Proven.Mach.Ind.BIn.val]
      {if oldForm && lin then "" else hasA}first
      | (simp only [{embs}] at h; rw [h]; {finish})
      | (rw [h]; {finish})"
  let rl := if rkS == ".t" then "true" else "false"
  let tryOld : CommandElabM Unit := runCmd s!"theorem _root_.{fS}.implements1 : Proven.Implements1With {encA'} {encB} {fS}.code {fApp'}
    (Proven.Frontx.Ind.space {P}.pg.M) (2 ^ 20) {rl} := by
  have := Proven.Frontx.Ind.implements1_ind {Tn}.sh {P}.pg {bi} (BitVec.ofNat 64 {a0}) {nb} {encA'} {encB} {fApp'} {v1'} {v2'}
    ({hencT}) (fun g => {T0}.emb_wf _) ({hw2T})
    ({houtT})
    (by decide) (by decide) (by decide) (by unfold Proven.Mach.Ind.Pg.lin; decide) (by intro t h; cases h <;> decide)
    (by decide) (by decide) {P}.wf
  exact this"
  let ainS := if ain then "true" else "false"
  let tryL : CommandElabM Unit := runCmd s!"theorem _root_.{fS}.implements1 : Proven.Implements1With {encA'} {encB} {fS}.code {fApp'}
    (Proven.Frontx.Ind.spaceA 1 16 (fun n => {P}.pg.M * n)) (2 ^ 20) {rl} :=
  Proven.Frontx.Ind.implements1_indL {Tn}.sh {shO} {P}.pg {bi} {ainS} (BitVec.ofNat 64 {a0}) {nb} {encA'} {encB} {fApp'} {v1'} {v2'} {av'}
    ({hencN}) (fun g => {T0}.emb_wf _) ({hw2T})
    ({houtT})
    (by decide) (by decide) (by decide) (by decide) (by unfold Proven.Mach.Ind.Pg.lin; decide) (by intro t h; cases h <;> decide)
    (by decide) {P}.wf"
  let chain := "⟨fun j hj => ⟨rfl, rfl⟩, " ++ String.join ((List.range (fns.size - 1)).map fun _ => "⟨fun j hj => ⟨rfl, rfl⟩, ") ++
    "trivial" ++ String.join ((List.range fns.size).map fun _ => "⟩")
  let chain := if fns.size == 1 then "⟨fun j hj => absurd hj (by simp), trivial⟩" else chain
  let tryS : CommandElabM Unit := do
    let thS := s!"theorem _root_.{fS}.implements1 : Proven.Implements1With {encA'} {encB} {fS}.code {fApp'}
    (Proven.Frontx.Ind.spaceA {fns.size} {nl} (Proven.Mach.Ind.cellsSup {Tn}.sh {P}.pg {bi} {ainS} (BitVec.ofNat 64 {a0}))) (2 ^ 20) {rl} :=
  Proven.Frontx.Ind.implements1_indS {Tn}.sh {shO} {P}.pg {hsList} {bi} {ainS} (BitVec.ofNat 64 {a0}) {nb} {nl} {encA'} {encB} {fApp'} {v1'} {v2'} {av'}
    ({hencN}) (fun g => {T0}.emb_wf _) ({hw2T})
    ({houtT})
    (by decide) (by decide) (by decide) (by first | exact {chain} | (simp only [Proven.Mach.Ind.Chain]; decide))
    (by decide) (by intro t h; cases h <;> decide) (by decide) {P}.wf"
    if (← IO.getEnv "FRONTX_DEBUG").isSome then logInfo thS
    runCmd thS
  if oldForm && nl == 16 && lin then
    try tryOld catch _ => tryS
  else if !multi && nl == 16 && lin then
    try tryL catch _ => tryS
  else tryS
  let t1 ← IO.monoMsNow
  logInfo m!"frontx_ind: {fN}{if isEntry then m!" (entry of {gN})" else m!""} on {Tn}: {fns.size} function(s) {fns.map (·.name)}, {armsA[0]!.arms.size} arms, result {rkS}, {nl} locals; {t1 - t0} ms"

end Proven.Frontx.IndCmd
