/- Nano/Expr/ExprSpec: the REFERENCE Expr emitter (Testing/notes/EXPR.md). `X` = the Lean `Expr` fragment, `ser` = the
S format, `emitProg` = for each def of `pDefs`'s output, the Expr its AST means. The IR erases three things the Expr
needs; they come from the token stream in source order (= the IR's pre-order): `let x` vs `let (a, b)`, `[]` vs `bnew`,
and the def names / parameter shapes (`DefI`). -/
import Nano.Parser.ParSpec
namespace ExprSpec
open ParSpec

/-- the fragment: bvar, const (closed levels), app, lam, forallE, letE (nondep flag), nat literal -/
inductive X | bv (i : Nat) | c (n : String) (ls : List Nat) | app (f a : X) | lam (t b : X) | pi (t b : X)
  | lt (nd : Bool) (t v b : X) | nat (k : Nat)
  deriving Repr, DecidableEq, Inhabited

def X.ser : X → String
  | .bv i => s!"#{i}"
  | .c n [] => s!"c {n}"
  | .c n ls => s!"c {n}.\{{",".intercalate (ls.map toString)}}"
  | .app f a => s!"@ {f.ser} {a.ser}"
  | .lam t b => s!"\\ {t.ser} {b.ser}"
  | .pi t b => s!"> {t.ser} {b.ser}"
  | .lt nd t v b => s!"{if nd then "h" else "="} {t.ser} {v.ser} {b.ser}"
  | .nat k => s!"n{k}"

def apps (f : X) : List X → X := List.foldl X.app f
def U : X := .c "UInt64" []

def shTy : Sh → X
  | .uw => U | .bf => .c "Buf" [] | .ls => .app (.c "List" [0]) (.c "UInt8" []) | .nt => .c "Nat" []
  | .p a b => apps (.c "Prod" [0, 0]) [shTy a, shTy b]
def psSh : Ps → Sh | .inp => .ls | .fuel => .nt | .sh s => s

def lit (s : Sh) (k : Nat) : X :=
  match s with
  | .nt => apps (.c "OfNat.ofNat" [0]) [.c "Nat" [], .nat k, .app (.c "instOfNatNat" []) (.nat k)]
  | _ => apps (.c "OfNat.ofNat" [0]) [U, .nat k, .app (.c "UInt64.instOfNat" []) (.nat k)]

/-- `.bin` op codes 1..7 → (class op, instance) -/
def binX (op : Nat) (a b : X) : X :=
  let (f, i, j) := match op with
    | 1 => ("HAdd.hAdd", "instHAdd", "instAddUInt64") | 2 => ("HSub.hSub", "instHSub", "instSubUInt64")
    | 3 => ("HMul.hMul", "instHMul", "instMulUInt64") | 4 => ("HAnd.hAnd", "instHAndOfAndOp", "instAndOpUInt64")
    | 5 => ("HOr.hOr", "instHOrOfOrOp", "instOrOpUInt64")
    | 6 => ("HShiftLeft.hShiftLeft", "instHShiftLeftOfShiftLeft", "instShiftLeftUInt64")
    | _ => ("HShiftRight.hShiftRight", "instHShiftRightOfShiftRight", "instShiftRightUInt64")
  apps (.c f [0, 0, 0]) [U, U, U, apps (.c i [0]) [U, .c j []], a, b]

/-- shift free bvars ≥ `c` by `d` -/
def X.lift (d : Nat) : Nat → X → X
  | k, .bv i => .bv (if i < k then i else i + d)
  | k, .app f a => .app (f.lift d k) (a.lift d k)
  | k, .lam t b => .lam (t.lift d k) (b.lift d (k + 1))
  | k, .pi t b => .pi (t.lift d k) (b.lift d (k + 1))
  | k, .lt nd t v b => .lt nd (t.lift d k) (v.lift d k) (b.lift d (k + 1))
  | _, e => e
/-- substitute `v` for bvar `k` (and lower the bvars above it) -/
def X.inst (v : X) : Nat → X → X
  | k, .bv i => if i = k then v.lift k 0 else .bv (if i < k then i else i - 1)
  | k, .app f a => .app (X.inst v k f) (X.inst v k a)
  | k, .lam t b => .lam (X.inst v k t) (X.inst v (k + 1) b)
  | k, .pi t b => .pi (X.inst v k t) (X.inst v (k + 1) b)
  | k, .lt nd t w b => .lt nd (X.inst v k t) (X.inst v k w) (X.inst v (k + 1) b)
  | _, e => e
/-- bvar `k` occurs -/
def X.uses : Nat → X → Bool
  | k, .bv i => i = k
  | k, .app f a => f.uses k || a.uses k
  | k, .lam t b => t.uses k || b.uses (k + 1)
  | k, .pi t b => t.uses k || b.uses (k + 1)
  | k, .lt _ t v b => t.uses k || v.uses k || b.uses (k + 1)
  | _, _ => false
/-- drop the LEADING `letE`s whose variable is unused (nested ones stay) -/
def X.dropHead : X → X
  | .lt nd t v b => if b.uses 0 then .lt nd t v b else X.inst (.bv 0) 0 b.dropHead
  | e => e

/-- for `<`, Lean's `UInt64.decLt` instance takes the operands with their LEADING unused `have`s dropped (observed on fuzz
programs with `let` inside a condition); for `==` the `instDecidableEqBool` instance keeps them as they are -/
def iteX (r : Sh) (cmp : Nat) (a b t e : X) : X :=
  if cmp = 1 then
    let q := apps (.c "BEq.beq" [0]) [U, apps (.c "instBEqOfDecidableEq" [0]) [U, .c "instDecidableEqUInt64" []], a, b]
    apps (.c "ite" [1]) [shTy r, apps (.c "Eq" [1]) [.c "Bool" [], q, .c "Bool.true" []],
      apps (.c "instDecidableEqBool" []) [q, .c "Bool.true" []], t, e]
  else
    apps (.c "ite" [1]) [shTy r, apps (.c "LT.lt" [0]) [U, .c "instLTUInt64" [], a, b],
      apps (.c "UInt64.decLt" []) [a.dropHead, b.dropHead], t, e]

/-- prim ids 1..9 (ParSpec.primSig): name, parameter kinds incl. the input, result -/
def primInfo : Nat → String × List Ps × Sh
  | 1 => ("len'", [.inp], .nt) | 2 => ("rd", [.inp, .sh .uw], .uw) | 3 => ("len", [.inp], .uw)
  | 4 => ("put", [.sh .ls, .sh .uw], .ls) | 6 => ("bsize", [.sh .bf], .uw) | 7 => ("bget", [.sh .bf, .sh .uw], .uw)
  | 8 => ("bset", [.sh .bf, .sh .uw, .sh .uw], .bf) | _ => ("bpush", [.sh .bf, .sh .uw], .bf)

/-- the side info: `let` forms (true = `let (a, b)`) and nil forms (true = `[]`), in source order -/
def sideLets : List Tok → List Bool
  | .k 2 :: .k 6 :: r => true :: sideLets r
  | .k 2 :: r => false :: sideLets r
  | _ :: r => sideLets r
  | [] => []
def sideNils : List Tok → List Bool
  | .k 30 :: .k 31 :: r => true :: sideNils r
  | .k 43 :: r => false :: sideNils r
  | _ :: r => sideNils r
  | [] => []

/-- binder stack (innermost first; position = de Bruijn index): slot and kind -/
abbrev Bs := List (Nat × Ps)
structure St where
  lets : List Bool
  nils : List Bool
abbrev M := StateT St (Except String)

def find (bs : Bs) (p : Nat × Ps → Bool) (what : String) : M X :=
  match bs.findIdx? p with | some i => pure (.bv i) | none => throw s!"no binder: {what}"
def inpX (bs : Bs) : M X := find bs (fun b => b.2 == .inp) "input"

def popLet : M Bool := do
  let s ← get
  match s.lets with | b :: r => set { s with lets := r }; pure b | [] => throw "side info: lets"
def popNil : M Bool := do
  let s ← get
  match s.nils with | b :: r => set { s with nils := r }; pure b | [] => throw "side info: nils"

structure Cx where
  defs : List DefI
  self : String × List Ps   -- the loop's name and state kinds (CONTINUE)

def nameS (n : List Nat) : String := String.ofList (n.map Char.ofNat)

/-- emit `e` at expected shape `exp` (none: no expected type, as for a `let` value); returns the Expr and the
shape Lean infers (none for a CONTINUE) -/
partial def emit (cx : Cx) (bs : Bs) (exp : Option Sh) : Nd → M (X × Option Sh)
  | .const v => let s := match exp with | some .nt => Sh.nt | _ => .uw; pure (lit s v.toNat, some s)
  | .loc s w =>
    if w = 0 then do pure ((← inpX bs), some .ls)
    else do
      match (bs.zipIdx.find? fun (b, _) => b.1 == s && b.2 != .inp) with
      | some ((_, p), i) => pure (.bv i, some (psSh p))
      | none => throw s!"slot {s}"
  | .bin op a b => do
    let (x, _) ← emit cx bs (some .uw) a
    let (y, _) ← emit cx bs (some .uw) b
    pure (binX op x y, some .uw)
  | .ite cmp a b t e => do
    let (x, _) ← emit cx bs (some .uw) a
    let (y, _) ← emit cx bs (some .uw) b
    let (tx, ts) ← emit cx bs exp t
    let (ex, es) ← emit cx bs exp e
    let r ← match exp <|> ts <|> es with | some r => pure r | none => throw "ite type"
    pure (iteX r cmp x y tx ex, some r)
  | .letE s _ v b => do
    let pr ← popLet
    let (vx, vs) ← emit cx bs none v
    let some vs := vs | throw "let of CONTINUE"
    if pr then
      let .p l r := vs | throw "pair let of a non-pair"
      let (bx, bsh) ← emit cx ((s + l.width, .sh r) :: (s, .sh l) :: bs) exp b
      let some R := exp <|> bsh | throw "let body type"
      pure (apps (.c "Prod.casesOn" [1, 0, 0]) [shTy l, shTy r, .lam (shTy vs) (shTy R), vx,
        .lam (shTy l) (.lam (shTy r) bx)], some R)
    else
      let (bx, bsh) ← emit cx ((s, .sh vs) :: bs) exp b
      pure (.lt true (shTy vs) vx bx, bsh)
  | .pair cs => do
    let [a, b] := cs | throw "pair arity"
    let (ea, eb) := match exp with | some (.p x y) => (some x, some y) | _ => (none, none)
    let (ax, as) ← emit cx bs ea a
    let (bx, bs') ← emit cx bs eb b
    let some A := ea <|> as | throw "pair type"
    let some B := eb <|> bs' | throw "pair type"
    pure (apps (.c "Prod.mk" [0, 0]) [shTy A, shTy B, ax, bx], some (.p A B))
  | .call i as => do
    let some d := cx.defs[i]? | throw "callee"
    let xs ← args cx bs d.params as
    pure (apps (.c (nameS d.name) []) xs, some d.res)
  | .prim 5 [] => do
    if ← popNil then pure (.app (.c "List.nil" [0]) (.c "UInt8" []), some .ls) else pure (.c "bnew" [], some .bf)
  | .prim p as => do
    let (n, ps, r) := primInfo p
    pure (apps (.c n []) (← args cx bs ps as), some r)
  | .loop _ _ => throw "nested loop"
  | .cont e => do
    let (n, sps) := cx.self
    let k := (sps.filter (· != .inp)).length
    let es ← if k = 1 then pure [e] else match e with | .pair cs => pure cs | _ => throw "CONTINUE payload"
    let fx ← find bs (fun b => b.2 == .fuel) "fuel"
    pure (apps (.c n []) (fx :: (← args cx bs sps es)), none)
where
  /-- arguments for parameter kinds `ps` (the input re-inserted) -/
  args (cx : Cx) (bs : Bs) : List Ps → List Nd → M (List X)
    | [], [] => pure []
    | .inp :: ps, as => do pure ((← inpX bs) :: (← args cx bs ps as))
    | p :: ps, a :: as => do
      let (x, _) ← emit cx bs (some (psSh p)) a
      pure (x :: (← args cx bs ps as))
    | _, _ => throw "arity"

/-- parameter binders from slot `s` -/
def binders (s : Nat) : List Ps → Bs → Bs
  | [], bs => bs
  | p :: ps, bs => binders (s + p.width) ps ((s, p) :: bs)

def piX (ps : List Ps) (r : X) : X := ps.foldr (fun p a => .pi (shTy (psSh p)) a) r
def lamX (ps : List Ps) (b : X) : X := ps.foldr (fun p a => .lam (shTy (psSh p)) a) b

/-- one def: (type, value) -/
def emitDef (defs : List DefI) (di : DefI) (da : DefA) : M (X × X) := do
  let ty := piX di.params (shTy di.res)
  let cx : Cx := { defs, self := (nameS di.name, di.params.drop 1) }
  match da.body with
  | .loop z s =>
    let bs := binders 0 di.params []
    let (zx, _) ← emit cx bs (some di.res) z
    let (sx, _) ← emit cx ((0, .fuel) :: bs) (some di.res) s
    let k := bs.length - 1
    pure (ty, lamX di.params (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy di.res), .bv k, zx,
      .lam (.c "Nat" []) sx]))
  | b =>
    let (bx, _) ← emit cx (binders 0 di.params []) (some di.res) b
    pure (ty, lamX di.params bx)

/-- the S text of a program: one `D name type value` line per def -/
def emitProg (src : List UInt8) : Except String String := do
  let some ws := lexAll (src.length + 1) src | throw "lex"
  let some toks := tokens ws | throw "tokens"
  let some (ds, as) := pDefs (8 * toks.length + 8) (toks.length + 1) [] toks | throw "parse"
  let go : M String := do
    let mut out := ""
    for (di, da) in ds.zip as do
      let (t, v) ← emitDef ds di da
      out := out ++ s!"D {nameS di.name} {t.ser} {v.ser}\n"
    pure out
  let (o, st) ← go.run { lets := sideLets toks, nils := sideNils toks }
  if !st.lets.isEmpty || !st.nils.isEmpty then throw "side info left over"
  pure o

end ExprSpec
