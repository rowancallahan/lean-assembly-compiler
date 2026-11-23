/- Nano/Expr/ExprSpec: the REFERENCE Expr emitter (Testing/notes/EXPR.md). `X` = the Lean `Expr` fragment, `ser` = the
S format, `emitProg` = for each def of `pDefs`'s output, the Expr its AST means. The IR erases three things the Expr
needs; they come from the token stream in source order (= the IR's pre-order): `let x` vs `let (a, b)`, `[]` vs `bnew`,
and the def names / parameter shapes (`DefI`). -/
import Nano.Parser.ParSpec
import Nano.Parser.NumSpec
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
def iteX (r : Sh) (n : Bool) (cmp : Nat) (a b t e : X) : X :=
  let T := if n then X.c "Nat" [] else U
  if cmp = 1 then
    let q := apps (.c "BEq.beq" [0]) [T, apps (.c "instBEqOfDecidableEq" [0])
      [T, .c (if n then "instDecidableEqNat" else "instDecidableEqUInt64") []], a, b]
    apps (.c "ite" [1]) [shTy r, apps (.c "Eq" [1]) [.c "Bool" [], q, .c "Bool.true" []],
      apps (.c "instDecidableEqBool" []) [q, .c "Bool.true" []], t, e]
  else
    apps (.c "ite" [1]) [shTy r, apps (.c "LT.lt" [0]) [T, .c (if n then "instLTNat" else "instLTUInt64") [], a, b],
      apps (.c (if n then "Nat.decLt" else "UInt64.decLt") []) [a.dropHead, b.dropHead], t, e]

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

/-! ## annotated nodes: the IR plus what it erases (`let` form, nil form), from the token side info -/
inductive Na
  | const (v : UInt64) | loc (slot w : Nat) | bin (op : Nat) (a b : Na) | ite (cmp : Nat) (a b t e : Na)
  | letE (pr : Bool) (slot w : Nat) (v b : Na) | pair (cs : List Na) | call (id : Nat) (args : List Na)
  | prim (p : Nat) (args : List Na) | nil (lst : Bool) | loop (z s : Na) | cont (e : Na)

mutual
def Na.erase : Na → Nd
  | .const v => .const v | .loc s w => .loc s w | .bin op a b => .bin op a.erase b.erase
  | .ite c a b t e => .ite c a.erase b.erase t.erase e.erase | .letE _ s w v b => .letE s w v.erase b.erase
  | .pair cs => .pair (Na.eraseL cs) | .call i as => .call i (Na.eraseL as) | .prim p as => .prim p (Na.eraseL as)
  | .nil _ => .prim 5 [] | .loop z s => .loop z.erase s.erase | .cont e => .cont e.erase
def Na.eraseL : List Na → List Nd
  | [] => [] | a :: as => a.erase :: Na.eraseL as
end

/-- side info state: the remaining `let` and nil flags -/
abbrev Sd := List Bool × List Bool

mutual
/-- annotate in pre-order, consuming the side flags -/
def annot : Nd → Sd → Option (Na × Sd)
  | .const v, st => some (.const v, st)
  | .loc s w, st => some (.loc s w, st)
  | .bin op a b, st => do let (a', st) ← annot a st; let (b', st) ← annot b st; pure (.bin op a' b', st)
  | .ite c a b t e, st => do
    let (a', st) ← annot a st; let (b', st) ← annot b st; let (t', st) ← annot t st; let (e', st) ← annot e st
    pure (.ite c a' b' t' e', st)
  | .letE s w v b, (pr :: ls, ns) => do
    let (v', st) ← annot v (ls, ns); let (b', st) ← annot b st; pure (.letE pr s w v' b', st)
  | .letE _ _ _ _, ([], _) => none
  | .pair cs, st => do let (cs', st) ← annotL cs st; pure (.pair cs', st)
  | .call i as, st => do let (as', st) ← annotL as st; pure (.call i as', st)
  | .prim 5 [], (ls, n :: ns) => some (.nil n, (ls, ns))
  | .prim 5 [], (_, []) => none
  | .prim p as, st => do let (as', st) ← annotL as st; pure (.prim p as', st)
  | .loop z s, st => do let (z', st) ← annot z st; let (s', st) ← annot s st; pure (.loop z' s', st)
  | .cont e, st => do let (e', st) ← annot e st; pure (.cont e', st)
def annotL : List Nd → Sd → Option (List Na × Sd)
  | [], st => some ([], st)
  | a :: as, st => do let (a', st) ← annot a st; let (as', st) ← annotL as st; pure (a' :: as', st)
end

/-- binder stack (innermost first; position = de Bruijn index): slot and kind -/
abbrev Bs := List (Nat × Ps)

/-- the innermost binder satisfying q: its index -/
def findB (q : Nat × Ps → Bool) : Bs → Option Nat
  | [] => none
  | b :: bs => if q b then some 0 else (findB q bs).map (· + 1)

/-- the innermost value binder of slot s: (index, shape) -/
def findSlot (s : Nat) : Bs → Option (Nat × Sh)
  | [] => none
  | (s', .sh sh) :: bs => if s' = s then some (0, sh) else (findSlot s bs).map fun (i, sh) => (i + 1, sh)
  | _ :: bs => (findSlot s bs).map fun (i, sh) => (i + 1, sh)

def inpX (bs : Bs) : Option X := (findB (fun b => b.2 == .inp) bs).map .bv

/-- a slot s is fresh: every binder ends at or below it -/
def fresh (s : Nat) (bs : Bs) : Bool := bs.all fun b => b.1 + b.2.width ≤ s

/-- an inferred shape agrees with the claimed one (a CONTINUE has none) -/
def agree (r : Sh) : Option Sh → Bool | none => true | some t => t == r

/-- the expected component shapes of a pair -/
def expSplit : Option Sh → Option Sh × Option Sh
  | some (.p x y) => (some x, some y)
  | _ => (none, none)

structure Cx where
  defs : List DefI
  self : String × List Ps   -- the loop's name and state kinds (CONTINUE)
  nat : Nat → Bool          -- slot has numeral class Nat (NumSpec.slotNat)

/-- a literal-only term of numeral class Nat: literals and Nat-bound slots under `if` branches and `let`s (a `let` of
a Nat slot `s` to such a value binds a Nat) -/
def natE (nat : Nat → Bool) (bs : Bs) : Na → Bool
  | .const _ => true
  | .loc s w => w == 1 && (match findSlot s bs with | some (_, .nt) => true | _ => false)
  | .ite _ _ _ t e => natE nat bs t && natE nat bs e
  | .letE pr s _ v b => natE nat (if !pr && nat s && natE nat bs v then (s, .sh .nt) :: bs else bs) b
  | _ => false

/-- a tuple value with a Nat-class literal field (`let p := (1, ..)`): Lean types the field Nat; not supported -/
def natPair (nat : Nat → Bool) (bs : Bs) (s : Nat) : Na → Bool
  | .pair cs => cs.zipIdx.any fun (c, i) => nat (s + i) && natE nat bs c
  | _ => false

def nameS (n : List Nat) : String := String.ofList (n.map Char.ofNat)

/-- leading input parameters: their count and the rest -/
def leadInp : List Ps → Nat × List Ps
  | .inp :: ps => let (n, r) := leadInp ps; (n + 1, r)
  | ps => (0, ps)

/-- the arguments of a parameter list that is all input parameters -/
def inps (bs : Bs) : List Ps → Option (List X)
  | [] => some []
  | .inp :: ps => do some ((← inpX bs) :: (← inps bs ps))
  | _ => none

mutual
/-- emit `e` at expected shape `exp` (none: no expected type, as for a `let` value): the Expr and the shape of its
value (none for a CONTINUE). Every typing / slot fact the correctness proof uses is CHECKED here (none = reject):
operand and argument shapes, binder widths, fresh `let` slots, branch shapes. -/
def emit (cx : Cx) (bs : Bs) (exp : Option Sh) : Na → Option (X × Option Sh)
  | .const v => let s := (match exp with | some .nt => Sh.nt | _ => .uw); some (lit s v.toNat, some s)
  | .loc s w => do
    let (i, sh) ← findSlot s bs
    if w = sh.width ∧ 0 < w then some (.bv i, some sh) else none
  | .bin op a b => do
    let (x, sa) ← emit cx bs (some .uw) a
    let (y, sb) ← emit cx bs (some .uw) b
    if sa = some .uw ∧ sb = some .uw ∧ 1 ≤ op ∧ op ≤ 7 then some (binX op x y, some .uw) else none
  | .ite cmp a b t e => do
    let n := natE cx.nat bs a && natE cx.nat bs b
    let o := if n then Sh.nt else .uw
    let (x, sa) ← emit cx bs (some o) a
    let (y, sb) ← emit cx bs (some o) b
    let (tx, ts) ← emit cx bs exp t
    let (ex, es) ← emit cx bs exp e
    let r ← exp <|> ts <|> es
    if sa = some o ∧ sb = some o ∧ (cmp = 1 ∨ cmp = 2) ∧ agree r ts ∧ agree r es then
      some (iteX r n cmp x y tx ex, some r) else none
  | .letE pr s w v b => do
    let n := !pr && cx.nat s && natE cx.nat bs v
    if natPair cx.nat bs s v then none else
    let (vx, vs) ← emit cx bs (if n then some .nt else none) v
    let vsh ← vs
    if ¬ (vsh.width = w ∧ fresh s bs ∧ (n → vsh = .nt)) then none else
    if pr then
      match vsh with
      | .p l r => do
        let (bx, bsh) ← emit cx ((s + l.width, .sh r) :: (s, .sh l) :: bs) exp b
        let R ← exp <|> bsh
        if agree R bsh then
          some (apps (.c "Prod.casesOn" [1, 0, 0]) [shTy l, shTy r, .lam (shTy vsh) (shTy R), vx,
            .lam (shTy l) (.lam (shTy r) bx)], some R) else none
      | _ => none
    else do
      let (bx, bsh) ← emit cx ((s, .sh vsh) :: bs) exp b
      some (.lt true (shTy vsh) vx bx, bsh)
  | .pair [a, b] => do
    let (ea, eb) := expSplit exp
    let (ax, sa) ← emit cx bs ea a
    let (bx, sb) ← emit cx bs eb b
    let A ← sa
    let B ← sb
    if agree A ea ∧ agree B eb then some (apps (.c "Prod.mk" [0, 0]) [shTy A, shTy B, ax, bx], some (.p A B))
    else none
  | .pair _ => none
  | .call i as => do
    let d ← cx.defs[i]?
    let xs ← args cx bs d.params as
    some (apps (.c (nameS d.name) []) xs, some d.res)
  | .nil lst => some (if lst then (.app (.c "List.nil" [0]) (.c "UInt8" []), some .ls) else (.c "bnew" [], some .bf))
  | .prim p as => do
    if p = 5 ∨ p = 0 ∨ 9 < p then none else
    let (n, ps, r) := primInfo p
    some (apps (.c n []) (← args cx bs ps as), some r)
  | .loop _ _ => none
  | .cont e => do
    let (n, sps) := cx.self
    let fi ← findB (fun b => b.2 == .fuel) bs
    if (sps.filter (· != .inp)).length = 1 then
      let p ← sps.find? (· != .inp)
      let (x, sx) ← emit cx bs (some (psSh p)) e
      if sx ≠ some (psSh p) then none else
      let xs ← sps.mapM fun q => if q == .inp then inpX bs else some x
      some (apps (.c n []) (.bv fi :: xs), none)
    else
      match e with
      | .pair cs => do some (apps (.c n []) (.bv fi :: (← args cx bs sps cs)), none)
      | _ => none

/-- arguments for parameter kinds `ps` (the input re-inserted), each of its parameter's shape; structural on the
argument nodes (leading input parameters are taken first, see `leadInp`) -/
def args (cx : Cx) (bs : Bs) : List Ps → List Na → Option (List X)
  | ps, [] => inps bs ps
  | ps, a :: as =>
    match leadInp ps with
    | (n, p :: ps') => do
      let ix ← if n = 0 then some (.bv 0) else inpX bs
      let (x, sx) ← emit cx bs (some (psSh p)) a
      if sx ≠ some (psSh p) then none else
      some (List.replicate n ix ++ x :: (← args cx bs ps' as))
    | (_, []) => none
end

/-- parameter binders from slot `s` -/
def binders (s : Nat) : List Ps → Bs → Bs
  | [], bs => bs
  | p :: ps, bs => binders (s + p.width) ps ((s, p) :: bs)

def piX (ps : List Ps) (r : X) : X := ps.foldr (fun p a => .pi (shTy (psSh p)) a) r
def lamX (ps : List Ps) (b : X) : X := ps.foldr (fun p a => .lam (shTy (psSh p)) a) b

/-- one def: (type, value); the body's shape must be the result shape -/
def emitDef (defs : List DefI) (nat : Nat → Bool) (di : DefI) (b : Na) : Option (X × X) := do
  let ty := piX di.params (shTy di.res)
  let cx : Cx := { defs, self := (nameS di.name, di.params.drop 1), nat }
  let bs := binders 0 di.params []
  match b with
  | .loop z s =>
    if di.params.head? ≠ some .fuel then none else
    let (zx, zs) ← emit cx bs (some di.res) z
    let (sx, ss) ← emit cx ((0, .fuel) :: bs) (some di.res) s
    if agree di.res zs ∧ agree di.res ss ∧ zs.isSome then
      some (ty, lamX di.params (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy di.res), .bv (bs.length - 1), zx,
        .lam (.c "Nat" []) sx])) else none
  | b =>
    let (bx, bsh) ← emit cx bs (some di.res) b
    if bsh = some di.res then some (ty, lamX di.params bx) else none

/-- the def's slots of numeral class Nat: `NumSpec.slotNat ks ws da` on slots 0..nslots, the groups computed once -/
def natList (ks ws : List Nat) (da : DefA) : List Nat :=
  let gs := (NumSpec.colD ks ws da).1
  let u := NumSpec.markD 1 gs da
  (List.range (da.nslots + 1)).filter fun s => gs.any (·.vs.contains s) && !u.contains s
theorem natList_eq (ks ws : List Nat) (da : DefA) (s : Nat) (hs : s ≤ da.nslots) :
    (natList ks ws da).contains s = NumSpec.slotNat ks ws da s := by
  have hr : s ∈ List.range (da.nslots + 1) := List.mem_range.2 (by omega)
  simp only [natList, NumSpec.slotNat]
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.mem_filter]
  simp [hr]

/-- names a program may not use for its defs: the fragment's fixed constants -/
def reserved (n : String) : Bool :=
  n.any (· == '.') || n ∈ ["ite", "rd", "len", "len'", "put", "bnew", "bsize", "bget", "bset", "bpush"]

/-- the Exprs of a parsed program (defs `ds`, bodies `as` from position `i`, side flags `st`): (name, type, value)
per def; def `i` must have id `i` -/
def emitAllL (ds : List DefI) (i : Nat) : List (List Nat) → List DefA → Sd → Option (List (String × X × X))
  | _, [], ([], []) => some []
  | _, [], _ => none
  | n :: ns, (da :: as), st => do
    if da.id ≠ i then none else
    let (b, st) ← annot da.body st
    let di ← ds[i]?
    let (t, v) ← emitDef ds (fun s => n.contains s) di b
    let rest ← emitAllL ds (i + 1) ns as st
    some ((nameS di.name, t, v) :: rest)
  | [], _ :: _, _ => none

/-- with each def's Nat slots (`natList`, i.e. `NumSpec.slotNat`) -/
def emitAll (ds : List DefI) (ks ws : List Nat) (i : Nat) (as : List DefA) (st : Sd) : Option (List (String × X × X)) :=
  emitAllL ds i (as.map (natList ks ws)) as st

/-- the Exprs of a program text -/
def emitXs (src : List UInt8) : Except String (List (String × X × X)) := do
  let some ws := lexAll (src.length + 1) src | throw "lex"
  let some toks := tokens ws | throw "tokens"
  let some (ds, as) := pDefs (8 * toks.length + 8) (toks.length + 1) [] toks | throw "parse"
  if !NumSpec.numOkP as then throw "num"
  let some o := emitAll ds (as.map (·.kind)) (as.map (·.nres)) 0 as (sideLets toks, sideNils toks) | throw "emit"
  let ns := o.map (·.1)
  if ns.eraseDups.length ≠ ns.length ∨ ns.any reserved then throw "names" else pure o

/-- the S text of a program: one `D name type value` line per def -/
def emitProg (src : List UInt8) : Except String String := do
  pure (String.join ((← emitXs src).map fun (n, t, v) => s!"D {n} {t.ser} {v.ser}\n"))

end ExprSpec
