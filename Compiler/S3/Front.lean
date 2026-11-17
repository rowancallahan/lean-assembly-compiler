/- **The S3 front end** (untrusted; `Testing/notes/IR_S3.md`): `s3_compile N := main` reads the kernel definitions
of `main` (a `List UInt8 → List UInt8` function) and of everything it calls, and generates
* `N.S`, `N.b<k>`, `N.P`: the S3 program (types as datatypes, one body per function, A-normal form);
* `N.φ`: the oracle (each function's Lean meaning on encoded values);
* `N.cert<k>`: the kernel-checked certificate `Good N.P N.φ k [enc x..]` for every function (by the function's own
  functional induction, `Compiler/S3/Cert.lean`), and `N.main_good` for `main`.
Nothing it produces is trusted: a wrong translation fails its certificate.

What it reads: the unfolding equation `f.eq_def` of each function (so the input is the kernel term, after
elaboration and match compilation), with
* monomorphisation and specialisation: a call's type, instance and function arguments are static (they become
  part of the function: `@List.filter UInt8 (· > 3)` is one S3 function);
* matchers unfolded to `casesOn`, `casesOn` to `match` (`cas`), constructors to `mk`, structure projections to a
  one-arm `match`, class projections of known instances unfolded (`++` to `List.append`);
* `UInt64`/`Int64` arithmetic, `UInt8`/`UInt64` comparisons, `Bool` connectives, `if`/`dite`/`cond`.
Not read (rejected with an error): `Nat`, `String`, arrays, function values that capture run-time variables,
mutual recursion between different functions. -/
import Lean
import Compiler.S3.Cert

namespace Proven.S3.Front
open Lean Meta Elab Command

/-- untyped S3 expressions, variables by de Bruijn level -/
inductive SE where
  | var (l : Nat)
  | lit (c : Nat)
  | blit (b : Bool)
  | bin (o : String) (a b : Nat)
  | cmp (c : String) (a b : Nat)
  | bnot (a : Nat)
  | let_ (t : Ty) (e₁ e₂ : SE)
  | ite (c : Nat) (e₁ e₂ : SE)
  | mk (i j : Nat) (xs : List Nat)
  /-- per arm: its number of fields and its body -/
  | cas (i x : Nat) (arms : List (Nat × SE))
  | call (f : Nat) (xs : List Nat)
  deriving Inhabited

instance : Inhabited Ty := ⟨.w⟩

structure FnInfo where
  key : Lean.Expr
  statics : Array Lean.Expr
  pTys : Array Lean.Expr
  retTy : Lean.Expr
  params : Array Ty := #[]
  ret : Ty := .w
  body : Option SE := none
  deriving Inhabited

structure St where
  tys : Array Lean.Expr := #[]
  dts : Array (Array (Array Ty)) := #[]
  /-- per datatype, per constructor, per Lean field: is it data (`false`: a proof, not stored) -/
  masks : Array (Array (Array Bool)) := #[]
  fns : Array FnInfo := #[]

abbrev M := StateRefT St MetaM

structure Ctx where
  vars : List (FVarId × Nat) := []
  depth : Nat := 0

def Ctx.push (c : Ctx) (x : Lean.Expr) : Ctx := ⟨(x.fvarId!, c.depth) :: c.vars, c.depth + 1⟩

def isRecursive (n : Name) : MetaM Bool := do
  if (← getEnv).contains (n ++ `_unary) || (← getEnv).contains (n.str "brecOn") then return true
  if let some ci := (← getEnv).find? n then
    if ci.all.length > 1 then return true
    -- structural recursion (compiled through `brecOn`): it has an unfolding equation as a recursive definition
    if ci.isDefinition && !(← isMatcher n) then
      if (← try getUnfoldEqnFor? n (nonRec := false) catch _ => pure none).isSome then return true
  return false

/-- a `Nat` literal (raw or `OfNat.ofNat Nat n _`) -/
def natLit? (e : Lean.Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e' => if e'.isAppOfArity ``OfNat.ofNat 3 && e'.appFn!.appFn!.appArg!.isConstOf ``Nat then
      match e'.appFn!.appArg!.consumeMData with
      | .lit (.natVal n) => some n
      | _ => none
    else none

def isWordTy (t : Lean.Expr) : Bool := t.isConstOf ``UInt64 || t.isConstOf ``Int64 || t.isConstOf ``UInt8 ||
  (t.isAppOfArity ``BitVec 1 && natLit? t.appArg! == some 64)

/-- the largest `Nat` literal (unary representation: a literal costs its value in constructor cells) -/
def natLitMax : Nat := 4096

/-- a `Nat` literal as constructors (datatype `i` is `Nat`) -/
def natChain (i : Nat) (d : Nat) : Nat → SE
  | 0 => .mk i 0 []
  | n + 1 => .let_ (.d i) (natChain i d n) (.mk i 1 [d])

partial def tyOf (t : Lean.Expr) : M Ty := do
  let t := (← instantiateMVars (← whnf t)).consumeMData
  if isWordTy t then return .w
  if t.isConstOf ``Bool then return .b
  let s ← get
  for i in [0:s.tys.size] do
    if (← withReducible (isDefEq s.tys[i]! t)) then return .d i
  let .const I us := t.getAppFn | throwError "S3: unsupported type {t}"
  let some (.inductInfo ii) := (← getEnv).find? I | throwError "S3: not an inductive type: {t}"
  unless ii.numIndices == 0 do throwError "S3: indexed families are not supported: {t}"
  let params := t.getAppArgs
  unless params.size == ii.numParams do throwError "S3: type not fully applied: {t}"
  if t.hasFVar || t.hasMVar then throwError "S3: type with variables: {t}"
  let i := s.tys.size
  modify fun s => { s with tys := s.tys.push t, dts := s.dts.push #[], masks := s.masks.push #[] }
  let mut cs : Array (Array Ty) := #[]
  let mut ms : Array (Array Bool) := #[]
  for c in ii.ctors do
    let cty ← inferType (mkAppN (mkConst c us) params)
    let (fs, mk) ← forallTelescopeReducing cty fun xs _ => do
      let mut r := #[]
      let mut mk := #[]
      for x in xs do
        let xt ← inferType x
        -- a proof field is not stored (it has no run-time content)
        if ← isProp xt then mk := mk.push false; continue
        if xt.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then throwError "S3: dependent field in {c}"
        r := r.push (← tyOf xt)
        mk := mk.push true
      return (r, mk)
    cs := cs.push fs
    ms := ms.push mk
  modify fun s => { s with dts := s.dts.set! i cs, masks := s.masks.set! i ms }
  return .d i

/-- the data mask of constructor `j` of datatype `i` -/
def maskOf (i j : Nat) : M (Array Bool) := do
  return (← get).masks[i]!.getD j #[]

/-- the data index of Lean field `k` (fields before it that are data) -/
def dataIdx (mask : Array Bool) (k : Nat) : Nat := ((mask.extract 0 k).filter id).size

def binOp? (n : Name) (t : Lean.Expr) : Option String :=
  if n == ``HAdd.hAdd then some "(.op .add)"
  else if n == ``HSub.hSub then some "(.op .sub)"
  else if n == ``HMul.hMul then some ".mul"
  else if n == ``HDiv.hDiv && t.isConstOf ``UInt64 then some ".udiv"
  else if n == ``HMod.hMod && t.isConstOf ``UInt64 then some ".urem"
  else if n == ``HAnd.hAnd then some "(.op .and)"
  else if n == ``HOr.hOr then some "(.op .or)"
  else if n == ``HXor.hXor then some "(.op .xor)"
  else if n == ``HShiftLeft.hShiftLeft then some "(.op .shl)"
  else if n == ``HShiftRight.hShiftRight then
    (if t.isConstOf ``Int64 then some "(.op .ashr)" else some "(.op .lshr)")
  else none

/-- is argument `i` of a call static (a type, an instance, a function, a proof)? -/
def staticArgs (f : Lean.Expr) (args : Array Lean.Expr) : MetaM Nat := do
  let fty ← inferType f
  forallBoundedTelescope fty args.size fun xs _ => do
    let mut n := 0
    let mut dyn := false
    for i in [0:xs.size] do
      let x := xs[i]!
      let d ← x.fvarId!.getDecl
      let xt ← whnfR d.type
      -- function-valued (also through definitions: `StateT σ m α` is `σ → m (α × σ)`)
      let isFn := (← whnf d.type).isForall
      let st := d.binderInfo.isInstImplicit || xt.isSort || (← isProp xt) || (isFn && !(← isProp xt)) ||
        (← isType xt) && !(← isProp xt) && (← whnfR xt).isSort
      if st then
        if dyn then throwError "S3: static argument after a run-time argument in {f}"
        n := n + 1
      else dyn := true
    return n

mutual

partial def fnIdx (key : Lean.Expr) : M Nat := do
  let key ← instantiateMVars key
  let s ← get
  for i in [0:s.fns.size] do
    if s.fns[i]!.key == key then return i
  let .const f us := key.getAppFn | throwError "S3: not a constant function: {key}"
  if key.hasFVar then throwError "S3: a function value captures run-time variables: {key}"
  let statics := key.getAppArgs
  let kty ← inferType key
  let (pTys, retTy) ← forallTelescopeReducing kty fun xs r => do
    if r.hasAnyFVar (fun v => xs.any (·.fvarId! == v)) then throwError "S3: dependent result type of {key}"
    return (← xs.mapM fun x => inferType x, r)
  let idx := s.fns.size
  modify fun s => { s with fns := s.fns.push { key, statics, pTys, retTy } }
  let params ← pTys.mapM tyOf
  let ret ← tyOf retTy
  modify fun s => { s with fns := s.fns.modify idx fun fi => { fi with params, ret } }
  let some eqn ← getUnfoldEqnFor? f (nonRec := true) | throwError "S3: no unfolding equation for {f}"
  let eqTy ← inferType (mkConst eqn us)
  let body ← forallTelescopeReducing kty fun xs _ => do
    -- the equation may have fewer binders than the (reduced) type: apply its right side to the rest
    let nEq ← forallTelescope eqTy fun ys _ => pure ys.size
    let all := statics ++ xs
    let inst ← instantiateForall eqTy (all.extract 0 nEq)
    let some (_, _, rhs0) := inst.eq? | throwError "S3: unexpected equation {inst}"
    let rhs := (mkAppN rhs0 (all.extract nEq all.size)).headBeta
    let mut c : Ctx := {}
    for x in xs.reverse do c := c.push x
    tr c rhs
  modify fun s => { s with fns := s.fns.modify idx fun fi => { fi with body := some body } }
  return idx

/-- an atom: the variable of `e` (let-bound if it is not one) -/
partial def atom (c : Ctx) (e : Lean.Expr) (k : Ctx → Nat → M SE) : M SE := do
  let e' := e.consumeMData.headBeta
  if let .fvar id := e' then
    if let some l := c.vars.lookup id then return ← k c l
  let s1 ← tr c e
  let ty ← tyOf (← inferType e)
  let s2 ← k { c with depth := c.depth + 1 } c.depth
  return .let_ ty s1 s2

partial def atoms (c : Ctx) : List Lean.Expr → (Ctx → List Nat → M SE) → M SE
  | [], k => k c []
  | e :: es, k => atom c e fun c' l => atoms c' es fun c'' ls => k c'' (l :: ls)

/-- a `Bool` value for a proposition -/
partial def condSE (c : Ctx) (p : Lean.Expr) : M SE := do
  let p := p.consumeMData
  let fn := p.getAppFn
  let args := p.getAppArgs
  let cmp2 (op : String) (a b : Lean.Expr) : M SE := atoms c [a, b] fun _ ls => return .cmp op ls[0]! ls[1]!
  let natCall (f : Name) (a b : Lean.Expr) : M SE := atoms c [a, b] fun _ ls => do
    let k ← fnIdx (mkConst f)
    return .call k ls
  match fn with
  | .const n _ =>
    let isNat := args.size > 0 && args[0]!.isConstOf ``Nat
    if isNat && n == ``Eq && args.size == 3 then return ← natCall ``Nat.beq args[1]! args[2]!
    if isNat && n == ``Ne && args.size == 3 then
      let s ← natCall ``Nat.beq args[1]! args[2]!
      return .let_ .b s (.bnot c.depth)
    if isNat && n == ``LT.lt && args.size == 4 then return ← natCall ``Nat.blt args[2]! args[3]!
    if isNat && n == ``LE.le && args.size == 4 then return ← natCall ``Nat.ble args[2]! args[3]!
    if isNat && n == ``GT.gt && args.size == 4 then return ← natCall ``Nat.blt args[3]! args[2]!
    if isNat && n == ``GE.ge && args.size == 4 then return ← natCall ``Nat.ble args[3]! args[2]!
    let signed := args.size > 0 && args[0]!.isConstOf ``Int64
    if n == ``LT.lt && args.size == 4 && isWordTy args[0]! then
      return ← cmp2 (if signed then ".slt" else ".ult") args[2]! args[3]!
    if n == ``LE.le && args.size == 4 && isWordTy args[0]! then
      return ← cmp2 (if signed then ".sle" else ".ule") args[2]! args[3]!
    if n == ``GT.gt && args.size == 4 && isWordTy args[0]! then
      return ← cmp2 (if signed then ".slt" else ".ult") args[3]! args[2]!
    if n == ``GE.ge && args.size == 4 && isWordTy args[0]! then
      return ← cmp2 (if signed then ".sle" else ".ule") args[3]! args[2]!
    if n == ``Eq && args.size == 3 && isWordTy args[0]! then return ← cmp2 ".eq" args[1]! args[2]!
    if n == ``Ne && args.size == 3 && isWordTy args[0]! then return ← cmp2 ".ne" args[1]! args[2]!
    if n == ``Eq && args.size == 3 && args[0]!.isConstOf ``Bool then
      if args[2]!.isConstOf ``Bool.true then return ← tr c args[1]!
      if args[2]!.isConstOf ``Bool.false then return ← atom c args[1]! fun _ l => return .bnot l
    if n == ``Not && args.size == 1 then
      let s ← condSE c args[0]!
      return .let_ .b s (.bnot c.depth)
    if n == ``And && args.size == 2 then
      let s ← condSE c args[0]!
      let c' := { c with depth := c.depth + 1 }
      return .let_ .b s (.ite c.depth (← condSE c' args[1]!) (.blit false))
    if n == ``Or && args.size == 2 then
      let s ← condSE c args[0]!
      let c' := { c with depth := c.depth + 1 }
      return .let_ .b s (.ite c.depth (.blit true) (← condSE c' args[1]!))
    throwError "S3: unsupported condition {p}"
  | _ => throwError "S3: unsupported condition {p}"

/-- the condition `p` as a `Bool` variable -/
partial def condAtom (c : Ctx) (p : Lean.Expr) (k : Ctx → Nat → M SE) : M SE := do
  let s ← condSE c p
  return .let_ .b s (← k { c with depth := c.depth + 1 } c.depth)

/-- the arm of a minor premise with `m` fields (the fields get the levels of variables `0 .. m - 1`) -/
partial def arm (c : Ctx) (minor : Lean.Expr) (m : Nat) (extra : Array Lean.Expr) (nih : Nat := 0)
    (mask : Array Bool := #[]) : M (Nat × SE) := do
  let mty ← inferType minor
  forallBoundedTelescope mty (m + nih) fun fs _ => do
    unless fs.size == m + nih do throwError "S3: arm with too few fields"
    let mut c' := c
    let mut nd := 0
    for k in [0:m] do
      if mask.getD k true then nd := nd + 1
    -- data fields only (proof fields stay local constants: they may occur only in proofs)
    for k in (List.range m).reverse do
      if mask.getD k true then c' := c'.push fs[k]!
    return (nd, ← tr c' (mkAppN (mkAppN minor fs) extra).headBeta)

partial def natLitSE (c : Ctx) (n : Nat) : M SE := do
  unless n ≤ natLitMax do throwError "S3: Nat literal {n} is too large for the unary representation"
  let .d i ← tyOf (mkConst ``Nat) | throwError "S3: Nat"
  return natChain i c.depth n

partial def tr (c : Ctx) (e : Lean.Expr) : M SE := do
  let e ← Core.betaReduce ((← instantiateMVars e).consumeMData)
  let e := e.consumeMData.headBeta
  match e with
  | .fvar id =>
    match c.vars.lookup id with
    | some l => return .var l
    | none => throwError "S3: unknown variable {e}"
  | .letE _ t v b _ =>
    -- a function value (a `do` join point): substitute it
    if (← whnf t).isForall || v.consumeMData.isLambda then
      return ← tr c (b.instantiate1 v).headBeta
    let s1 ← tr c v
    let ty ← tyOf t
    withLocalDeclD `x t fun x => do
      return .let_ ty s1 (← tr (c.push x) (b.instantiate1 x))
  | .proj S idx s =>
    let some (.ctorInfo ci) := (← getEnv).find? (getStructureCtor (← getEnv) S).name | throwError "S3: proj"
    atom c s fun c' lx => do
      let .d i ← tyOf (← inferType s) | throwError "S3: projection of a non-datatype"
      let mask ← maskOf i 0
      unless mask.getD idx true do throwError "S3: projection of a proof field {e}"
      let nd := (mask.filter id).size
      return .cas i lx [(nd, .var (c'.depth + nd - 1 - dataIdx mask idx))]
  | .const ``Bool.true _ => return .blit true
  | .const ``Bool.false _ => return .blit false
  | .lit (.natVal n) => natLitSE c n
  | _ => trApp c e

partial def trApp (c : Ctx) (e : Lean.Expr) : M SE := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let env ← getEnv
  -- `(let x := v; b) a…` (a `do` join point applied to the state): move the arguments under the `let`
  if let .letE nm t v b nd := fn.consumeMData then
    return ← tr c (.letE nm t v (mkAppN b (args.map (·.liftLooseBVars 0 1))) nd)
  let .const n _ := fn | throwError "S3: unsupported application {e}"
  -- literals
  if let some v := natLit? e then return ← natLitSE c v
  -- a `Fin n` literal: `⟨k % n, _⟩`
  if n == ``OfNat.ofNat && args.size == 3 && args[0]!.isAppOfArity ``Fin 1 then
    if let (some m, some k) := (natLit? args[0]!.appArg!, natLit? args[1]!) then
      if m > 0 then
        let .d i ← tyOf args[0]! | throwError "S3: Fin"
        let s1 ← natLitSE c (k % m)
        return .let_ (← tyOf (mkConst ``Nat)) s1 (.mk i 0 [c.depth])
  if n == ``OfNat.ofNat && args.size == 3 && isWordTy args[0]! then
    match args[1]!.consumeMData with
    | .lit (.natVal v) => return .lit (v % 2 ^ 64)
    | _ => throwError "S3: literal {e}"
  -- word operations
  if args.size == 6 && isWordTy args[0]! then
    if let some o := binOp? n args[0]! then
      if args[0]!.isConstOf ``UInt8 then throwError "S3: UInt8 arithmetic is not supported: {e}"
      return ← atoms c [args[4]!, args[5]!] fun _ ls => return .bin o ls[0]! ls[1]!
  if (n == ``BEq.beq || n == ``bne) && args.size == 4 && args[0]!.isConstOf ``Nat then
    return ← atoms c [args[2]!, args[3]!] fun c' ls => do
      let k ← fnIdx (mkConst ``Nat.beq)
      if n == ``BEq.beq then return .call k ls
      return .let_ .b (.call k ls) (.bnot c'.depth)
  if n == ``BEq.beq && args.size == 4 && isWordTy args[0]! then
    return ← atoms c [args[2]!, args[3]!] fun _ ls => return .cmp ".eq" ls[0]! ls[1]!
  if n == ``bne && args.size == 4 && isWordTy args[0]! then
    return ← atoms c [args[2]!, args[3]!] fun _ ls => return .cmp ".ne" ls[0]! ls[1]!
  if n == ``not && args.size == 1 then return ← atom c args[0]! fun _ l => return .bnot l
  if n == ``and && args.size == 2 then
    return ← atom c args[0]! fun c' l => do return .ite l (← tr c' args[1]!) (.blit false)
  if n == ``or && args.size == 2 then
    return ← atom c args[0]! fun c' l => do return .ite l (.blit true) (← tr c' args[1]!)
  if n == ``Decidable.decide && args.size == 2 then return ← condSE c args[0]!
  -- (extra arguments, e.g. a state, go into the branches)
  if n == ``ite && args.size ≥ 5 then
    let ex := args.extract 5 args.size
    return ← condAtom c args[1]! fun c' l => do
      return .ite l (← tr c' (mkAppN args[3]! ex)) (← tr c' (mkAppN args[4]! ex))
  if n == ``dite && args.size ≥ 5 then
    let ex := args.extract 5 args.size
    return ← condAtom c args[1]! fun c' l => do
      let t ← withLocalDeclD `h args[1]! fun h => tr c' (mkAppN (mkApp args[3]! h).headBeta ex)
      let f ← withLocalDeclD `h (mkNot args[1]!) fun h => tr c' (mkAppN (mkApp args[4]! h).headBeta ex)
      return .ite l t f
  if n == ``cond && args.size ≥ 4 then
    let ex := args.extract 4 args.size
    return ← atom c args[1]! fun c' l => do
      return .ite l (← tr c' (mkAppN args[2]! ex)) (← tr c' (mkAppN args[3]! ex))
  if (n == ``UInt64.ofBitVec || n == ``UInt64.toBitVec) && args.size == 1 then
    return ← atom c args[0]! fun _ l => return .var l
  if n == ``UInt8.toUInt64 && args.size == 1 then return ← atom c args[0]! fun _ l => return .var l
  if n == ``UInt64.toUInt8 && args.size == 1 then
    return ← atom c args[0]! fun c' l => return .let_ .w (.lit 255) (.bin "(.op .and)" l c'.depth)
  -- constructors
  if let some (.ctorInfo ci) := env.find? n then
    unless args.size == ci.numParams + ci.numFields do throwError "S3: partial constructor {e}"
    let .d i ← tyOf (← inferType e) | throwError "S3: constructor of a non-datatype {e}"
    let mask ← maskOf i ci.cidx
    let fs := (args.extract ci.numParams args.size).toList.zipIdx.filter (fun (_, k) => mask.getD k true)
    return ← atoms c (fs.map (·.1)) fun _ ls => return .mk i ci.cidx ls
  -- casesOn
  if isCasesOnRecursor env n then
    let I := n.getPrefix
    let some (.inductInfo ii) := env.find? I | throwError "S3: casesOn"
    let nmaj := ii.numParams + 1 + ii.numIndices
    let nmin := ii.ctors.length
    unless args.size ≥ nmaj + 1 + nmin do throwError "S3: partial casesOn {e}"
    let major := args[nmaj]!
    let minors := args.extract (nmaj + 1) (nmaj + 1 + nmin)
    let extra := args.extract (nmaj + 1 + nmin) args.size
    if I == ``Bool then
      return ← atom c major fun c' l => do
        return .ite l (← tr c' (mkAppN minors[1]! extra).headBeta) (← tr c' (mkAppN minors[0]! extra).headBeta)
    return ← atom c major fun c' l => do
      let .d i ← tyOf (← inferType major) | throwError "S3: match on a non-datatype {major}"
      let mut arms := #[]
      for j in [0:nmin] do
        let some (.ctorInfo cj) := env.find? ii.ctors[j]! | throwError "S3: ctor"
        arms := arms.push (← arm c' minors[j]! cj.numFields extra 0 (← maskOf i j))
      return .cas i l arms.toList
  -- recursors used as `casesOn` (the induction hypotheses unused)
  if let some (.recInfo ri) := env.find? n then
    let I := ri.getMajorInduct
    let some (.inductInfo ii) := env.find? I | throwError "S3: rec"
    let nmin := ii.ctors.length
    let nmaj := ii.numParams + 1 + nmin + ii.numIndices
    unless args.size ≥ nmaj + 1 && ri.numMotives == 1 do throwError "S3: partial recursor {e}"
    let major := args[nmaj]!
    let minors := args.extract (ii.numParams + 1) (ii.numParams + 1 + nmin)
    let extra := args.extract (nmaj + 1) args.size
    return ← atom c major fun c' l => do
      let .d i ← tyOf (← inferType major) | throwError "S3: match on a non-datatype {major}"
      let mut arms := #[]
      for j in [0:nmin] do
        let some (.ctorInfo cj) := env.find? ii.ctors[j]! | throwError "S3: ctor"
        let cty ← inferType (mkConst ii.ctors[j]! (ri.levelParams.drop 1 |>.map mkLevelParam))
        let nih ← forallTelescopeReducing cty fun xs _ => do
          let mut k := 0
          for x in xs.extract ii.numParams xs.size do
            if (← inferType x).getAppFn.isConstOf I then k := k + 1
          return k
        arms := arms.push (← arm c' minors[j]! cj.numFields extra nih (← maskOf i j))
      return .cas i l arms.toList
  -- matchers
  if (← isMatcher n) || (n.isInternal && (← getConstInfo n).isDefinition && !(← isRecursive n)) then
    let .const _ us := fn | throwError "S3"
    let info ← getConstInfo n
    let v ← instantiateValueLevelParams info us
    return ← tr c (mkAppN v args).headBeta
  -- projections: of a structure (a one-arm match), of a class instance (unfolded)
  if let some pi ← getProjectionFnInfo? n then
    if !pi.fromClass then
      unless args.size == pi.numParams + 1 do throwError "S3: projection with extra arguments {e}"
      let s := args[pi.numParams]!
      let some (.ctorInfo ci) := env.find? pi.ctorName | throwError "S3: proj"
      return ← atom c s fun c' lx => do
        let .d i ← tyOf (← inferType s) | throwError "S3: projection of a non-datatype"
        let mask ← maskOf i 0
        unless mask.getD pi.i true do throwError "S3: projection of a proof field {e}"
        let nd := (mask.filter id).size
        let _ := ci
        return .cas i lx [(nd, .var (c'.depth + nd - 1 - dataIdx mask pi.i))]
    if let some e' ← unfoldProjInst? e then return ← tr c e'.headBeta
    throwError "S3: unsupported class operation {e}"
  -- a non-recursive function applied beyond its declared arity (a monadic value applied to its state, e.g.
  -- `StateT.get s`): inlined
  if !(← isRecursive n) then
    let declArity ← forallTelescope (← inferType fn) fun ys _ => pure ys.size
    if args.size > declArity then
      let info ← getConstInfo n
      if info.isDefinition then
        let .const _ us := fn | throwError "S3"
        let v ← instantiateValueLevelParams info us
        return ← tr c (mkAppN v args).headBeta
  -- calls (a non-recursive function with a function argument after a run-time one is inlined)
  let ns ← try staticArgs fn args catch ex =>
    if (← isRecursive n) then throw ex
    let info ← getConstInfo n
    unless info.isDefinition do throw ex
    let .const _ us := fn | throw ex
    let v ← instantiateValueLevelParams info us
    return ← tr c (mkAppN v args).headBeta
  let key := mkAppN fn (args.extract 0 ns)
  if key.hasFVar && !(← isRecursive n) then
    -- a function argument captures run-time variables: inline the (non-recursive) callee
    let info ← getConstInfo n
    if info.isDefinition then
      let .const _ us := fn | throwError "S3"
      let v ← instantiateValueLevelParams info us
      return ← tr c (mkAppN v args).headBeta
  for a in args.extract ns args.size do
    if a.consumeMData.isLambda then throwError "S3: a function value as a run-time argument in {e}"
  let k ← fnIdx key
  atoms c (args.extract ns args.size).toList fun _ ls => return .call k ls

end

/-- `(k : Fin n).val` for a literal `k` is `k % n` (definitionally; simp does not index `Fin` literals by lemmas) -/
dsimproc [simp] s3FinValLit (Fin.val _) := fun e => do
  let_expr Fin.val n x ← e | return .continue
  let x := x.consumeMData
  unless x.isAppOfArity ``OfNat.ofNat 3 do return .continue
  let .lit (.natVal k) := x.appFn!.appArg!.consumeMData | return .continue
  unless x.appArg!.isAppOf ``Fin.instOfNat do return .continue
  return .visit (← mkAppM ``HMod.hMod #[mkNatLit k, n])

/-- `Enc.enc (k : Nat)` for a literal `k > 0` is `.c 1 [Enc.enc (k - 1)]` (definitionally: `natV`) -/
dsimproc [simp] s3EncNatLit (Proven.S3.Enc.enc _) := fun e => do
  unless e.isAppOfArity ``Proven.S3.Enc.enc 3 do return .continue
  unless e.appFn!.appFn!.appArg!.isConstOf ``Nat do return .continue
  let some k := natLit? e.appArg! | return .continue
  if k == 0 then return .continue
  let inner := mkApp3 (mkConst ``Proven.S3.Enc.enc) (mkConst ``Nat) e.appFn!.appArg! (mkNatLit (k - 1))
  let one := mkApp (mkConst ``Proven.S3.V.c) (mkNatLit 1)
  let l ← mkListLit (mkConst ``Proven.S3.V) [inner]
  return .visit (mkApp one l)

/-! ## certificate tactics -/

/-- split a variable `x` that the goal uses as `Enc.enc x` (a datatype value whose constructor is not known) -/
syntax (name := s3Split) "s3_split" : tactic

@[tactic s3Split] def evalS3Split : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let g ← Tactic.getMainGoal
  let t ← instantiateMVars (← g.getType)
  -- the datatype variables inside `Enc.enc _`, the latest declared first
  let mut inside : Array FVarId := #[]
  let r ← IO.mkRef (#[] : Array Lean.Expr)
  t.forEach fun e => do if e.isAppOfArity ``Proven.S3.Enc.enc 3 then r.modify (·.push e.appArg!)
  let encArgs ← r.get
  for e in encArgs do
    let fvs := (Lean.collectFVars {} e).fvarIds
    for v in fvs do
      unless inside.contains v do inside := inside.push v
  let lctx ← getLCtx
  let mut best : Option LocalDecl := none
  for v in inside do
    let some d := lctx.find? v | continue
    let ty ← whnf d.type
    if isWordTy ty || ty.isConstOf ``Bool then continue
    let .const I _ := ty.getAppFn | continue
    let some (.inductInfo ii) := (← getEnv).find? I | continue
    if ii.ctors.length < 2 then continue
    match best with
    | some b => if d.index < b.index then best := some d
    | none => best := some d
  -- first: the condition of an `if` (two goals, never a blow-up)
  let conds ← do
    let r ← IO.mkRef (#[] : Array Lean.Expr)
    t.forEach fun e => do
      if e.isAppOfArity ``ite 5 && !e.appFn!.appFn!.appFn!.appArg!.hasLooseBVars then
        r.modify (·.push e.appFn!.appFn!.appFn!.appArg!)
    r.get
  if h : 0 < conds.size then
    let (g1, g2) ← g.byCases conds[0]
    Tactic.replaceMainGoal [g1.mvarId, g2.mvarId]
    return
  -- second: a datatype value computed by a call (`Enc.enc (f args)`): generalize it, then split
  for e in encArgs do
    if e.isFVar || e.hasLooseBVars then continue
    let ty ← whnf (← inferType e)
    if isWordTy ty || ty.isConstOf ``Bool then continue
    let .const I _ := ty.getAppFn | continue
    let some (.inductInfo ii) := (← getEnv).find? I | continue
    if ii.ctors.length < 2 then continue
    if (← isConstructorApp e) then continue
    let .const h _ := e.getAppFn | continue
    if (← isMatcher h) || h == ``ite || h == ``dite || h == ``cond || isCasesOnRecursor (← getEnv) h then continue
    let (fvs, g') ← g.generalize #[{ expr := e, xName? := `t }]
    let gs ← g'.cases fvs[0]!
    Tactic.replaceMainGoal (gs.map (·.mvarId)).toList
    return
  if let some d := best then
    let gs ← g.cases d.fvarId
    Tactic.replaceMainGoal (gs.map (·.mvarId)).toList
    return
  throwError "s3_split: nothing to split in\n{MessageData.ofGoal g}"

/-- close a goal by a hypothesis `∀ xs, x = pattern → False` that now applies (a wildcard case of a match) -/
syntax (name := s3Contra) "s3_contra" : tactic

@[tactic s3Contra] def evalS3Contra : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let g ← Tactic.getMainGoal
  let g ← g.exfalso
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isForall do continue
    let s ← saveState
    try
      let gs ← g.apply d.toExpr
      for g' in gs do
        if !(← g'.isAssigned) then
          let gt ← whnfR (← g'.getType)
          if gt.isEq then g'.refl
          else if gt.isConstOf ``True then g'.assign (mkConst ``True.intro)
      if (← gs.allM fun g' => g'.isAssigned) then
        Tactic.replaceMainGoal []
        return
      s.restore
    catch _ => s.restore
  throwError "s3_contra: no contradiction"

/-- add the negated forms of `Nat` order hypotheses (`a < b` gives `¬ b ≤ a`, `¬ a < b` gives `b ≤ a`, and back) -/
syntax (name := s3Hyps) "s3_hyps" : tactic

@[tactic s3Hyps] def evalS3Hyps : Tactic.Tactic := fun _ => Tactic.withMainContext do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let add (pf : Lean.Expr) : Tactic.TacticM Unit := do
      let g ← Tactic.getMainGoal
      let t ← inferType pf
      let (_, g') ← (← g.assert `hS3 t pf).intro1P
      Tactic.replaceMainGoal [g']
    match ty.getAppFnArgs with
    | (``LT.lt, #[t, _, a, b]) => if t.isConstOf ``Nat then add (← mkAppM ``Nat.not_le_of_lt #[d.toExpr])
    | (``LE.le, #[t, _, a, b]) => if t.isConstOf ``Nat then add (← mkAppM ``Nat.not_lt_of_le #[d.toExpr])
    | (``Not, #[q]) =>
      match q.getAppFnArgs with
      | (``LT.lt, #[t, _, _, _]) => if t.isConstOf ``Nat then add (← mkAppM ``Nat.le_of_not_lt #[d.toExpr])
      | (``LE.le, #[t, _, _, _]) => if t.isConstOf ``Nat then add (← mkAppM ``Nat.lt_of_not_le #[d.toExpr])
      | _ => pure ()
    | _ => pure ()

/-- `s3_solve n [simp lemmas] with closer`: simplify; close what remains with `closer`; else split a variable and
retry (at most `n` times deep) -/
syntax (name := s3Solve) "s3_solve " num " [" Lean.Parser.Tactic.simpArg,* "]" " with " tactic : tactic

macro_rules (kind := s3Solve)
  | `(tactic| s3_solve $n [$ls,*] with $c) => do
    let k := n.getNat
    if k == 0 then
      `(tactic| ((try simp only [s3_norm, Nat.reduceMod, Nat.reducePow, beq_iff_eq, bne_iff_ne, Nat.blt_eq, Nat.ble_eq, UInt8.toNat_ofNat, decide_eq_true_eq] at *); (try s3_hyps); simp [s3_norm, $ls,*]; all_goals (repeat' apply And.intro) <;> $c))
    else
      let n' := Syntax.mkNumLit (toString (k - 1))
      `(tactic| first
        | s3_contra
        | ((try simp only [s3_norm, Nat.reduceMod, Nat.reducePow, beq_iff_eq, bne_iff_ne, Nat.blt_eq, Nat.ble_eq, UInt8.toNat_ofNat, decide_eq_true_eq] at *); (try s3_hyps); simp [s3_norm, $ls,*]; done)
        | ((try simp only [s3_norm, Nat.reduceMod, Nat.reducePow, beq_iff_eq, bne_iff_ne, Nat.blt_eq, Nat.ble_eq, UInt8.toNat_ofNat, decide_eq_true_eq] at *); (try s3_hyps); simp [s3_norm, $ls,*]; all_goals (repeat' apply And.intro) <;> $c; done)
        | (((try simp only [s3_norm, Nat.reduceMod, Nat.reducePow, beq_iff_eq, bne_iff_ne, Nat.blt_eq, Nat.ble_eq, UInt8.toNat_ofNat, decide_eq_true_eq] at *); (try s3_hyps); (try simp [s3_norm, $ls,*]);
            s3_split) <;> s3_solve $n' [$ls,*] with $c))

/-! ## text -/

def tyTxt : Ty → String
  | .w => ".w"
  | .b => ".b"
  | .d i => s!"(.d {i})"

def listTxt (l : List String) : String := "[" ++ ", ".intercalate l ++ "]"

def varTxt : Nat → String
  | 0 => ".z"
  | i + 1 => "(.s " ++ varTxt i ++ ")"

def varsTxt (depth : Nat) : List Nat → String
  | [] => ".nil"
  | l :: ls => s!"(.cons {varTxt (depth - 1 - l)} {varsTxt depth ls})"

partial def seTxt (depth : Nat) : SE → String
  | .var l => s!"(.var {varTxt (depth - 1 - l)})"
  | .lit c => s!"(.lit {c})"
  | .blit b => s!"(.blit {b})"
  | .bin o a b => s!"(.bin {o} {varTxt (depth - 1 - a)} {varTxt (depth - 1 - b)})"
  | .cmp o a b => s!"(.cmp {o} {varTxt (depth - 1 - a)} {varTxt (depth - 1 - b)})"
  | .bnot a => s!"(.bnot {varTxt (depth - 1 - a)})"
  | .let_ t e₁ e₂ => s!"(.let_ (σ := {tyTxt t}) {seTxt depth e₁} {seTxt (depth + 1) e₂})"
  | .ite c e₁ e₂ => s!"(.ite {varTxt (depth - 1 - c)} {seTxt depth e₁} {seTxt depth e₂})"
  | .mk i j xs => s!"(.mk {i} {j} {varsTxt depth xs})"
  | .cas i x arms =>
    let as := arms.foldr (fun (m, a) acc => s!"(.cons {seTxt (depth + m) a} {acc})") ".nil"
    s!"(.cas (i := {i}) {varTxt (depth - 1 - x)} (Alts.arms {as}))"
  | .call f xs => s!"(.call ⟨{f}, by decide⟩ {varsTxt depth xs} rfl)"

def exprTxt (e : Lean.Expr) : MetaM String := do
  let f ← withOptions (fun o => (((o.setBool `pp.explicit true).setBool `pp.fullNames true).setBool
    `pp.universes false).setBool `pp.funBinderTypes true |>.setBool `pp.deepTerms false
    |>.setBool `pp.proofs true) (ppExpr e)
  return "(" ++ f.pretty 100000 ++ ")"

/-- the functions a body calls -/
partial def SE.calls : SE → List Nat
  | .let_ _ a b => a.calls ++ b.calls
  | .ite _ a b => a.calls ++ b.calls
  | .cas _ _ arms => arms.flatMap (·.2.calls)
  | .call f _ => [f]
  | _ => []

def simpSet : String :=
  "Proven.S3.evalO, Proven.S3.CallsOk, Proven.S3.Var.idx, Proven.S3.Alts.arms, " ++
  "Proven.S3.Vars.get, Proven.S3.Vars.idxs, Proven.S3.Prim.eval, Proven.Op.eval, Proven.S3.Cmp.eval, " ++
  "Proven.S3.Sig.nc, Proven.S3.Sig.fld, Proven.S3.Sig.dt, Proven.S3.lget, -Fin.isValue"

/-- the certificate text of a mutual component `c` (S3 functions) of the Lean mutual block `blk`: ONE theorem by
the block's `mutual_induct` (Lean's own termination argument, structural or well-founded) for all members at once,
then one projection per member -/
def genMutual (st : St) (c : List Nat) (blk : List Name) (extraSimp : String) : MetaM String := do
  let fnameOf (j : Nat) : MetaM Name := do
    let .const f _ := st.fns[j]!.key.getAppFn | throwError "S3"
    return f
  let names ← c.mapM fnameOf
  unless names.Nodup do throwError "S3: a mutual block used at two specialisations: {names}"
  let k0 := c[0]!
  let fi0 := st.fns[k0]!
  let .const f0 us := fi0.key.getAppFn | throwError "S3"
  let indName ← realizeGlobalConstNoOverloadCore (f0 ++ `mutual_induct)
  let allNames ← forallTelescopeReducing (← getConstInfo f0).type fun ys _ => ys.mapM fun y => y.fvarId!.getUserName
  let indTy ← inferType (mkConst indName us)
  -- the parameters before the motives: the static arguments, by name
  let (preE, preTxt, motTys) ← forallTelescopeReducing indTy fun ys _ => do
    let mut pre : Array Lean.Expr := #[]
    let mut preT : Array String := #[]
    for y in ys do
      let nm ← y.fvarId!.getUserName
      if nm.toString.startsWith "motive" then break
      let some j := allNames.toList.idxOf? nm | throwError "S3: induction principle parameter {nm} not found"
      unless j < fi0.statics.size do throwError "S3: mutual induction keeps a run-time parameter {nm} fixed"
      pre := pre.push fi0.statics[j]!
      preT := preT.push (← exprTxt fi0.statics[j]!)
    return (pre, preT, (← ys.filterM fun y => do return (← y.fvarId!.getUserName).toString.startsWith "motive").size)
  unless motTys == blk.length do throwError "S3: {indName}: {motTys} motives for {blk.length} functions"
  let ty' ← instantiateForall indTy preE
  -- per block member: its motive (the certificate, or `True` for members the program does not use)
  let (motives, conjs) ← forallBoundedTelescope ty' blk.length fun ms _ => do
    let mut mo : Array String := #[]
    let mut cj : Array String := #[]
    for i in [0:blk.length] do
      let dom ← forallTelescopeReducing (← inferType ms[i]!) fun zs _ => zs.mapM fun z => do exprTxt (← inferType z)
      let ys := (List.range dom.size).map (s!"y{·}")
      let bnd := String.join ((List.range dom.size).map fun t => s!"({ys[t]!} : {dom[t]!}) ")
      let body ← match names.idxOf? blk[i]! with
        | some t =>
          let j := c[t]!
          unless st.fns[j]!.pTys.size == dom.size do throwError "S3: motive arity of {blk[i]!} (fixed parameters are not supported)"
          pure s!"Proven.S3.Good P φ ⟨{j}, by decide⟩ {listTxt (ys.map (s!"Proven.S3.Enc.enc {·}"))}"
        | none => pure "True"
      mo := mo.push (if dom.isEmpty then s!"({body})" else s!"(fun {bnd}=> {body})")
      cj := cj.push (if dom.isEmpty then s!"({body})" else s!"(∀ {bnd}, {body})")
    return (mo, cj)
  let mut out := ""
  for j in c do
    let fi := st.fns[j]!
    let xs := (List.range fi.pTys.size).map (s!"x{·}")
    let binders ← (List.range fi.pTys.size).mapM fun i => do return s!"({xs[i]!} : {← exprTxt fi.pTys[i]!})"
    let encs := listTxt (xs.map (s!"Proven.S3.Enc.enc {·}"))
    let fa := if binders.isEmpty then "" else s!"∀ {" ".intercalate binders}, "
    let fapp := (← exprTxt fi.key) ++ String.join (xs.map (" " ++ ·))
    out := out ++ s!"theorem body{j} : P.body ⟨{j}, by decide⟩ = b{j} := rfl\n"
    out := out ++ s!"theorem phi{j} : {fa}φ ⟨{j}, by decide⟩ {encs} = Proven.S3.Enc.enc ({fapp}) := by\n" ++
      (if xs.isEmpty then "" else s!"  intro {" ".intercalate xs}\n") ++ "  simp [φ]\n"
  -- callees outside the component close by their certificates
  let outside := (c.flatMap fun j => (st.fns[j]!.body.map SE.calls).getD []).eraseDups.filter (!c.contains ·)
  let closers := outside.map (fun j => s!"(apply cert{j}' <;> simp)")
  let closer := " | ".intercalate ("assumption" :: "(intros; assumption)" :: "(intros; apply_assumption; done)" :: "rfl" :: "omega" :: (closers ++ closers.map ("(intros; " ++ · ++ ")")))
  let mut unf := ""
  for j in outside do
    let fj := st.fns[j]!
    let .const gname _ := fj.key.getAppFn | continue
    if !(((fj.body.map SE.calls).getD []).contains j) && fj.pTys.size == 0 then unf := unf ++ s!", {gname}"
  let bs := String.join (c.map (s!", b{·}"))
  let chains ← c.mapM fun j => do
    let fn ← fnameOf j
    return s!"((apply Proven.S3.good_intro <;> rw [body{j}]) <;> (try rw [phi{j}]) <;> (try rw [{fn}.eq_def]))"
  let pre := String.join (preTxt.toList.map (" " ++ ·))
  let mo := String.join (motives.toList.map (" " ++ ·))
  out := out ++ s!"/-- **the component {names}**, by ONE induction: Lean's `{indName}` -/\n" ++
    s!"theorem certM{k0} : {" ∧ ".intercalate conjs.toList} := by\n" ++
    s!"  apply @{indName}{pre}{mo}\n" ++
    s!"  all_goals (intros; (try dsimp only at *); first | trivial | ((first | {" | ".intercalate chains}) <;>\n" ++
    s!"    s3_solve 12 [{simpSet}{bs}, φ{extraSimp}{unf}, *] with (first | {closer})))\n"
  for t in [0:c.length] do
    let j := c[t]!
    let i := blk.idxOf names[t]!
    let proj := (if i + 1 == blk.length then "" else ".1")
    let path := String.join ((List.range i).map fun _ => ".2") ++ proj
    let fi := st.fns[j]!
    let xs := (List.range fi.pTys.size).map (s!"x{·}")
    let binders ← (List.range fi.pTys.size).mapM fun i => do return s!"({xs[i]!} : {← exprTxt fi.pTys[i]!})"
    let encs := listTxt (xs.map (s!"Proven.S3.Enc.enc {·}"))
    let fa := if binders.isEmpty then "" else s!"∀ {" ".intercalate binders}, "
    out := out ++ s!"theorem cert{j} : {fa}Proven.S3.Good P φ ⟨{j}, by decide⟩ {encs} := certM{k0}{path}\n"
    let vs := (List.range fi.pTys.size).map (s!"v{·}")
    let hs := (List.range fi.pTys.size).map (s!"h{·}")
    let hyps ← (List.range fi.pTys.size).mapM fun i => do
      return s!"Proven.S3.Enc.enc (Proven.S3.Enc.dec {vs[i]!} : {← exprTxt fi.pTys[i]!}) = {vs[i]!} → "
    let vbind := if vs.isEmpty then "" else s!"∀ {" ".intercalate vs} : Proven.S3.V, "
    out := out ++ s!"theorem cert{j}' : {vbind}{String.join hyps}Proven.S3.Good P φ ⟨{j}, by decide⟩ {listTxt vs} := by\n" ++
      (if vs.isEmpty then s!"  exact cert{j}\n" else
        s!"  intro {" ".intercalate (vs ++ hs)}\n  have := cert{j} {" ".intercalate (vs.map (s!"(Proven.S3.Enc.dec {·})"))}\n" ++
        s!"  rw [{", ".intercalate hs}] at this\n  exact this\n")
  return out

/-- the commands for program `N` -/
def genText (N : Name) (st : St) (extraSimp : String) : MetaM String := do
  let p := N.toString
  let dts := st.dts.toList.map fun cs => listTxt (cs.toList.map fun fs => listTxt (fs.toList.map tyTxt))
  let fns := st.fns.toList.map fun fi => s!"({listTxt (fi.params.toList.map tyTxt)}, {tyTxt fi.ret})"
  let mut out := s!"namespace {p}\nopen Proven.S3\n"
  out := out ++ s!"abbrev S : Proven.S3.Sig := ⟨{listTxt dts}, {listTxt fns}⟩\n"
  for k in [0:st.fns.size] do
    let fi := st.fns[k]!
    let some b := fi.body | throwError "S3: missing body"
    out := out ++ s!"def b{k} : Proven.S3.Expr S {listTxt (fi.params.toList.map tyTxt)} {tyTxt fi.ret} :=\n  " ++
      seTxt fi.params.size b ++ "\n"
  let bodies := (List.range st.fns.size).foldr (fun k acc => s!"(.cons b{k} {acc})") ".nil"
  out := out ++ s!"abbrev P : Proven.S3.Prog := ⟨S, {bodies}, ⟨0, by decide⟩⟩\n"
  -- the oracle
  out := out ++ "noncomputable def φ : Fin P.S.fns.length → List Proven.S3.V → Proven.S3.V := fun f vs => match f.val with\n"
  for k in [0:st.fns.size] do
    let fi := st.fns[k]!
    let mut app := ← exprTxt fi.key
    for i in [0:fi.pTys.size] do
      app := app ++ s!" (Proven.S3.Enc.dec (vs.getD {i} default) : {← exprTxt fi.pTys[i]!})"
    out := out ++ s!"  | {k} => Proven.S3.Enc.enc ({app})\n"
  out := out ++ "  | _ => default\n"
  -- the certificates, components of the call graph callees first (a component: functions calling each other)
  let n := st.fns.size
  let callsOf (k : Nat) : List Nat := (st.fns[k]!.body.map SE.calls).getD []
  let mut reach : Array (Array Bool) := (List.range n).toArray.map fun k =>
    (List.range n).toArray.map fun j => (callsOf k).contains j
  for m in [0:n] do
    for i in [0:n] do
      for j in [0:n] do
        if reach[i]![m]! && reach[m]![j]! && !reach[i]![j]! then reach := reach.modify i (·.set! j true)
  let comp (k : Nat) : List Nat := (List.range n).filter fun j => j == k || (reach[k]![j]! && reach[j]![k]!)
  let mut done : Array Nat := #[]
  let mut comps : Array (List Nat) := #[]
  let mut changed := true
  while changed do
    changed := false
    for k in [0:n] do
      if done.contains k then continue
      let c := comp k
      if c.all (fun j => (callsOf j).all (fun i => c.contains i || done.contains i)) then
        done := done ++ c.toArray; comps := comps.push c; changed := true
  unless done.size == n do throwError "S3: call graph ordering failed"
  for c in comps do
    let k0 := c[0]!
    let .const f0 _ := st.fns[k0]!.key.getAppFn | throwError "S3"
    let blk := (← getConstInfo f0).all
    if blk.length > 1 then
      out := out ++ (← genMutual st c blk extraSimp)
      continue
    unless c.length == 1 do throwError "S3: functions {c} call each other but are not one Lean mutual block"
    let k := k0
    let fi := st.fns[k]!
    let xs := (List.range fi.pTys.size).map (s!"x{·}")
    let binders ← (List.range fi.pTys.size).mapM fun i => do return s!"({xs[i]!} : {← exprTxt fi.pTys[i]!})"
    let encs := listTxt (xs.map (s!"Proven.S3.Enc.enc {·}"))
    let .const fname _ := fi.key.getAppFn | throwError "S3"
    let recursive := ((fi.body.map SE.calls).getD []).contains k
    let callees := ((fi.body.map SE.calls).getD []).filter (· != k)
    let closers := callees.eraseDups.map (fun j => s!"(apply cert{j}' <;> simp)")
    let closer := " | ".intercalate ("assumption" :: "(intros; assumption)" :: "(intros; apply_assumption; done)" :: "rfl" :: "omega" :: (closers ++ closers.map ("(intros; " ++ · ++ ")")))
    -- non-recursive callees unfold in the certificate (their values are then computed)
    let mut unf := ""
    for j in callees.eraseDups do
      let fj := st.fns[j]!
      let .const gname _ := fj.key.getAppFn | continue
      let rec_ := ((fj.body.map SE.calls).getD []).contains j
      if !rec_ && fj.pTys.size == 0 then unf := unf ++ s!", {gname}"
    let introLine := if xs.isEmpty then "" else s!"  intro {" ".intercalate xs}\n"
    let introLine := if recursive then introLine else introLine ++ "  (\n"
    let mut statics := ""
    for a in fi.statics do statics := statics ++ " " ++ (← exprTxt a)
    let mut induct := ""
    if recursive then
      -- the parameters the induction principle keeps fixed (before `motive`) and the targets (the motive's arguments)
      let indName ← realizeGlobalConstNoOverloadCore (fname ++ `induct)
      let allNames ← forallTelescopeReducing (← getConstInfo fname).type fun ys _ => ys.mapM fun y => y.fvarId!.getUserName
      let argTxt ← do
        let mut r : Array String := #[]
        for a in fi.statics do r := r.push (← exprTxt a)
        pure (r ++ xs.toArray)
      let (preTxt, targetNames) ← forallTelescopeReducing (← getConstInfo indName).type fun ys _ => do
        let mut pre : Array String := #[]
        let mut m := 0
        let mut seenMotive := false
        for y in ys do
          let n ← y.fvarId!.getUserName
          if n == `motive then
            seenMotive := true
            m ← forallTelescopeReducing (← inferType y) fun zs _ => pure zs.size
          else if !seenMotive then
            match allNames.toList.idxOf? n with
            | some j => pre := pre.push (argTxt[j]!)
            | none => throwError "S3: induction principle parameter {n} not found"
        let mut r := #[]
        for y in ys.extract (ys.size - m) ys.size do r := r.push (← y.fvarId!.getUserName)
        return (pre, r)
      let dyn := (allNames.extract fi.statics.size allNames.size).toList
      let byName := targetNames.toList.map fun n => dyn.idxOf n
      let fixedTxt := String.join (preTxt.toList.map (" " ++ ·))
      let targets := if byName.Nodup && byName.all (· < xs.length) then byName
        else (List.range xs.length).filter (fun i => !preTxt.contains xs[i]!) |>.take targetNames.size
      let gen := (List.range xs.length).filter (fun i => !targets.contains i && !preTxt.contains xs[i]!)
      let genTxt := if gen.isEmpty then "" else s!" generalizing {" ".intercalate (gen.map (xs[·]!))}"
      induct := s!"  induction {", ".intercalate (targets.map (xs[·]!))} using @{fname}.induct{fixedTxt}{genTxt} <;> (\n"
    out := out ++ s!"theorem body{k} : P.body ⟨{k}, by decide⟩ = b{k} := rfl\n"
    let fapp := (← exprTxt fi.key) ++ String.join (xs.map (" " ++ ·))
    let fa := if binders.isEmpty then "" else s!"∀ {" ".intercalate binders}, "
    out := out ++ s!"theorem phi{k} : {fa}φ ⟨{k}, by decide⟩ {encs} = Proven.S3.Enc.enc ({fapp}) := by\n" ++
      (if xs.isEmpty then "" else s!"  intro {" ".intercalate xs}\n") ++ "  simp [φ]\n"
    out := out ++ s!"theorem cert{k} : {fa}Proven.S3.Good P φ ⟨{k}, by decide⟩ {encs} := by\n" ++
      introLine ++ induct ++
      s!"  (apply Proven.S3.good_intro <;> rw [body{k}]) <;> (try rw [phi{k}]) <;> (try rw [{fname}.eq_def]) <;>\n" ++
      s!"  s3_solve 12 [{simpSet}, b{k}, φ{extraSimp}{unf}, *] with (first | {closer}))\n"
    let vs := (List.range fi.pTys.size).map (s!"v{·}")
    let hs := (List.range fi.pTys.size).map (s!"h{·}")
    let hyps ← (List.range fi.pTys.size).mapM fun i => do
      return s!"Proven.S3.Enc.enc (Proven.S3.Enc.dec {vs[i]!} : {← exprTxt fi.pTys[i]!}) = {vs[i]!} → "
    let vbind := if vs.isEmpty then "" else s!"∀ {" ".intercalate vs} : Proven.S3.V, "
    out := out ++ s!"theorem cert{k}' : {vbind}{String.join hyps}Proven.S3.Good P φ ⟨{k}, by decide⟩ {listTxt vs} := by\n" ++
      (if vs.isEmpty then s!"  exact cert{k}\n" else
        s!"  intro {" ".intercalate (vs ++ hs)}\n  have := cert{k} {" ".intercalate (vs.map (s!"(Proven.S3.Enc.dec {·})"))}\n" ++
        s!"  rw [{", ".intercalate hs}] at this\n  exact this\n")
  out := out ++ s!"theorem main_good : ∀ bs : List UInt8, Proven.S3.Good P φ P.main [Proven.S3.Enc.enc bs] := cert0\n"
  out := out ++ "/-- **termination**: from `main` on every input, the call tree is well-founded (from the certificates, i.e. " ++
    "from Lean's own induction principles) -/\n" ++
    "theorem wf : Proven.S3.WfCert P (fun f vs => f = P.main ∧ ∃ bs : List UInt8, vs = [Proven.S3.Enc.enc bs]) :=\n" ++
    "  ⟨fun f vs ⟨hf, bs, hv⟩ => by subst hf hv; exact Proven.S3.acc_of_ev (main_good bs)⟩\n"
  let mainTxt ← exprTxt st.fns[0]!.key
  out := out ++ s!"/-- **the bridge**: the S3 program computes `main` on bytes -/\n" ++
    s!"theorem computes : Proven.Top.Computes P {mainTxt} id id :=\n" ++
    s!"  Proven.S3.computes_of_main {mainTxt} id id {mainTxt} (fun _ => rfl) (fun bs => phi0 bs) main_good\n"
  if (← getEnv).contains `Proven.S3.compile_correct then
    out := out ++ s!"/-- **the machine theorem**: the compiled code computes `main` (`Compiler/AllocSpec.lean`) -/\n" ++
      s!"theorem correct (compiled : Proven.Top.Alloc.CompiledA) (h : Proven.S3.compile P = some compiled) " ++
      s!"(input : List UInt8) (startState : Proven.Top.riscv.State) (call : Proven.Top.Call) " ++
      s!"(hs : Proven.Top.StartCorrect Proven.Top.riscv startState call compiled.code (id input)) " ++
      s!"(ho : (id ({mainTxt} input)).length ≤ call.outputLength) " ++
      s!"(hm : Proven.Top.Alloc.memoryNeeded compiled (id input) ≤ call.workLength) :\n" ++
      s!"    ∃ finishState, Proven.Top.Runs Proven.Top.riscv startState finishState ∧\n" ++
      s!"      (Proven.Top.riscv.observe finishState).programCounter = call.returnAddress ∧\n" ++
      s!"      (Proven.Top.riscv.observe finishState).register Proven.Top.riscv.mapping.status ≠ Proven.Top.Alloc.oomFlag ∧\n" ++
      s!"      Proven.Top.readMemory (Proven.Top.riscv.observe finishState) call.outputAddress (id ({mainTxt} input)).length\n" ++
      s!"        = some (id ({mainTxt} input)) :=\n" ++
      s!"  Proven.S3.compile_correct P compiled {mainTxt} id id input startState call h computes hs ho hm\n"
  out := out ++ s!"end {p}\n"
  return out

/-- the monad operations of concrete `StateT σ (Except ε)` / `ExceptT` code, unfolded in the certificates -/
def monadSimp : String :=
  ", bind, StateT.bind, StateT.pure, pure, Except.bind, Except.pure, get, getThe, MonadStateOf.get, StateT.get, " ++
  "set, StateT.set, MonadStateOf.set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe, " ++
  "MonadExceptOf.throw, StateT.lift, Except.map, instMonadExceptOfExcept, StateT.run, Except.instMonad, " ++
  "Except.tryCatch, ExceptT.run, ExceptT.bind, ExceptT.pure, ExceptT.mk, ExceptT.bindCont"

/-- `s3_compile N := main [simp lemmas]`: generate the S3 program and its certificates -/
syntax (name := s3Compile) "s3_compile " ident " := " term (" simp " "[" ident,* "]")? : command

@[command_elab s3Compile] def elabS3 : CommandElab := fun stx => do
  let N := stx[1].getId
  -- the optional `simp [ids]` group: a node with its 4 parts (empty when absent)
  let extra : String := if stx[4].getNumArgs ≥ 3 then
      String.join ((stx[4][2].getSepArgs.toList.map (·.getId.toString)).map (", " ++ ·))
    else ""
  let txt ← liftTermElabM do
    let e ← Term.elabTerm stx[3] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let (_, st) ← (fnIdx e).run {}
    -- concrete `StateT` / `Except` / `ExceptT` code: the certificates unfold their monad operations
    let mentions (x : Lean.Expr) : Bool := (x.find? fun y =>
      y.isConstOf ``StateT || y.isConstOf ``Except || y.isConstOf ``ExceptT).isSome
    let monadic := st.fns.any fun fi => mentions fi.key || mentions fi.retTy || fi.pTys.any mentions
    let extra := if monadic then extra ++ monadSimp else extra
    genText N st extra
  logInfo m!"{txt}"
  let inputCtx := Parser.mkInputContext txt "<s3_compile>"
  let env ← getEnv
  let mut pstate : Parser.ModuleParserState := {}
  let mut cmds := #[]
  repeat
    let (cmd, ps', msgs) := Parser.parseCommand inputCtx { env, options := {} } pstate {}
    pstate := ps'
    unless msgs.toList.isEmpty do
      for m in msgs.toList do logError m!"S3 parse: {← m.toString}"
      return
    if cmd.isOfKind ``Parser.Command.eoi then break
    cmds := cmds.push cmd
  for cmd in cmds do elabCommand cmd

end Proven.S3.Front

namespace Proven.S3.Front
open Lean Meta Elab Command

/-- `s3_enc I`: an `Enc` instance for the inductive type `I` (its type parameters need `Enc`), with the simp lemmas
the certificates use -/
syntax (name := s3Enc) "s3_enc " ident : command

def genEnc (I : Name) : MetaM String := do
  let some (.inductInfo ii) := (← getEnv).find? I | throwError "s3_enc: not an inductive type"
  let np := ii.numParams
  let pnames := (List.range np).map (s!"α{·}")
  let pbind := String.join (pnames.map (s!"\{{·} : Type} "))
  let pinst := String.join (pnames.map (s!"[Proven.S3.Enc {·}] "))
  let Ity := if np == 0 then I.toString else s!"({I} {" ".intercalate pnames})"
  -- per constructor: field names and whether recursive
  let mut ctors : Array (Name × Array Bool) := #[]
  for c in ii.ctors do
    let cty := (← getConstInfo c).type
    let recs ← forallTelescopeReducing cty fun xs _ => do
      let mut r := #[]
      for x in xs.extract np xs.size do
        r := r.push ((← inferType x).getAppFn.isConstOf I)
      return r
    ctors := ctors.push (c, recs)
  let some dflt := ctors.findIdx? (fun (_, rs) => !rs.any id) | throwError "s3_enc: no non-recursive constructor"
  let fv (n : Nat) := (List.range n).map (s!"f{·}")
  let encF (rec : Bool) (f : String) := if rec then s!"{I}.s3enc {f}" else s!"Proven.S3.Enc.enc {f}"
  let decF (rec : Bool) (f : String) := if rec then s!"{I}.s3dec {f}" else s!"Proven.S3.Enc.dec {f}"
  let mut out := s!"def _root_.{I}.s3enc {pbind}{pinst}: {Ity} → Proven.S3.V\n"
  for j in [0:ctors.size] do
    let (c, rs) := ctors[j]!
    let fs := fv rs.size
    out := out ++ s!"  | @{c} {" ".intercalate pnames} {" ".intercalate fs} => .c {j} [{", ".intercalate ((List.range rs.size).map fun k => encF rs[k]! fs[k]!)}]\n"
  out := out ++ s!"def _root_.{I}.s3dec {pbind}{pinst}: Proven.S3.V → {Ity}\n"
  for j in [0:ctors.size] do
    let (c, rs) := ctors[j]!
    let fs := fv rs.size
    out := out ++ s!"  | .c {j} [{", ".intercalate fs}] => @{c} {" ".intercalate pnames} {" ".intercalate ((List.range rs.size).map fun k => "(" ++ decF rs[k]! fs[k]! ++ ")")}\n"
  let (dc, drs) := ctors[dflt]!
  out := out ++ s!"  | _ => @{dc} {" ".intercalate pnames} {" ".intercalate (drs.toList.map fun _ => "(Proven.S3.Enc.dec (.w 0))")}\n"
  out := out ++ s!"instance _root_.{I}.s3inst {pbind}{pinst}: Proven.S3.Enc {Ity} where\n  enc := {I}.s3enc\n  dec := {I}.s3dec\n" ++
    s!"  dec_enc x := by induction x <;> simp_all [{I}.s3enc, {I}.s3dec]\n"
  for j in [0:ctors.size] do
    let (c, rs) := ctors[j]!
    let fs := fv rs.size
    let fb := if fs.isEmpty then "" else s!"({" ".intercalate fs}) "
    out := out ++ s!"@[simp] theorem _root_.{I}.s3enc_{j} {pbind}{pinst}{fb}: Proven.S3.Enc.enc (@{c} {" ".intercalate pnames} {" ".intercalate fs}) = Proven.S3.V.c {j} [{", ".intercalate (fs.map (s!"Proven.S3.Enc.enc {·}"))}] := rfl\n"
    let vb := if fs.isEmpty then "" else s!"({" ".intercalate fs} : Proven.S3.V) "
    out := out ++ s!"@[simp] theorem _root_.{I}.s3dec_{j} {pbind}{pinst}{vb}: (Proven.S3.Enc.dec (Proven.S3.V.c {j} [{", ".intercalate fs}]) : {Ity}) = @{c} {" ".intercalate pnames} {" ".intercalate (fs.map (s!"(Proven.S3.Enc.dec {·})"))} := rfl\n"
  if ctors.size == 1 then
    let (c, rs) := ctors[0]!
    let projs ← do
      let some si := getStructureInfo? (← getEnv) I | pure none
      pure (some si.fieldNames)
    if let some fns := projs then
      out := out ++ s!"@[simp] theorem _root_.{I}.s3enc_eta {pbind}{pinst}(p : {Ity}) : Proven.S3.Enc.enc p = Proven.S3.V.c 0 [{", ".intercalate (fns.toList.map (s!"Proven.S3.Enc.enc p.{·}"))}] := by cases p; rfl\n"
    let _ := c; let _ := rs
  return out

@[command_elab s3Enc] def elabS3Enc : CommandElab := fun stx => do
  let I ← liftCoreM <| realizeGlobalConstNoOverload stx[1]
  let txt ← liftTermElabM (genEnc I)
  let inputCtx := Parser.mkInputContext txt "<s3_enc>"
  let env ← getEnv
  let mut pstate : Parser.ModuleParserState := {}
  let mut cmds := #[]
  repeat
    let (cmd, ps', msgs) := Parser.parseCommand inputCtx { env, options := {} } pstate {}
    pstate := ps'
    unless msgs.toList.isEmpty do
      logInfo m!"{txt}"
      for m in msgs.toList do logError m!"s3_enc parse: {← m.toString}"
      return
    if cmd.isOfKind ``Parser.Command.eoi then break
    cmds := cmds.push cmd
  for cmd in cmds do elabCommand cmd

end Proven.S3.Front
