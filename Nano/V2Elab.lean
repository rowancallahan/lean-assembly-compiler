import Nano.Elab
import Nano.V2Ast
/- nano v2 elaborator, increment 1 (DRAFT spec): v1's `nanoElab` plus
     expr ::= ... | 'if' sum cmp sum 'then' expr 'else' expr        cmp ::= '==' | '<' | '<='
   (`if` only where `let` may stand: the start of a def body, a `let` body, an `if` branch, inside parentheses).
   `==`, `<`, `<=` must be followed by a space.  `<`/`<=` are unsigned in a `UInt64` file, signed in an `Int64` file.
   TYPING GUARD (exact-subset rule): Lean elaborates a comparison whose operands contain no word-typed leaf at type
   `Nat` (numerals default to `Nat`: `if 1 - 2 < 1` is true in Lean, false on words), so a comparison is accepted only
   if one operand is TYPED: contains a parameter, a call, a typed `let` variable, or a parenthesised `let`/`if` whose
   body/branch is typed (`typed`). -/
namespace Nano.V2
open Nano (isWordC isDigit spanId kwDef kwLet kwTy kwTyI identOk adjOk)

inductive Tok where
  | kdef | klet | kty (signed : Bool) | id (s : List UInt8) | num (n : UInt64)
  | lp | rp | colon | assign | plus | minus | star | semi
  | kif | kthen | kelse | eqeq | lt | le

def kwIf : List UInt8 := [105, 102]
def kwThen : List UInt8 := [116, 104, 101, 110]
def kwElse : List UInt8 := [101, 108, 115, 101]

def wordTok (w : List UInt8) : Option Tok :=
  match w with
  | [] => none
  | c :: _ =>
    if isDigit c then (if w.all isDigit then some (Tok.num (w.foldl (fun a d => a * 10 + (d - 48).toUInt64) 0)) else none)
    else if w == kwDef then some Tok.kdef else if w == kwLet then some Tok.klet
    else if w == kwTy then some (Tok.kty false) else if w == kwTyI then some (Tok.kty true)
    else if w == kwIf then some Tok.kif else if w == kwThen then some Tok.kthen else if w == kwElse then some Tok.kelse
    else if identOk w then some (Tok.id w) else none

def lex : Nat → List UInt8 → Option (List Tok)
  | 0, xs => if xs.isEmpty then some [] else none
  | _ + 1, [] => some []
  | f + 1, c :: xs =>
    if c == 32 then lex f xs
    else if c == 10 then
      match xs with
      | [] => some []
      | 32 :: _ => lex f xs
      | 10 :: _ => lex f xs
      | 100 :: 101 :: 102 :: z => if (match z with | d :: _ => isWordC d | [] => false) then none else lex f xs
      | _ => none
    else if c == 40 then (lex f xs).map (Tok.lp :: ·)
    else if c == 41 then (lex f xs).map (Tok.rp :: ·)
    else if c == 43 then (lex f xs).map (Tok.plus :: ·)
    else if c == 45 then
      match xs with
      | 45 :: _ => none
      | _ => (lex f xs).map (Tok.minus :: ·)
    else if c == 42 then (lex f xs).map (Tok.star :: ·)
    else if c == 59 then (lex f xs).map (Tok.semi :: ·)
    else if c == 58 then
      match xs with
      | 61 :: ys => (lex f ys).map (Tok.assign :: ·)
      | _ => (lex f xs).map (Tok.colon :: ·)
    else if c == 61 then
      -- `==` then a space (no `=`, `===`, `==>`)
      match xs with
      | 61 :: 32 :: ys => (lex f ys).map (Tok.eqeq :: ·)
      | _ => none
    else if c == 60 then
      -- `<` or `<=`, then a space (no `<-`, `<|`, `<<<`, `<==`, ...)
      match xs with
      | 32 :: ys => (lex f ys).map (Tok.lt :: ·)
      | 61 :: 32 :: ys => (lex f ys).map (Tok.le :: ·)
      | _ => none
    else if isWordC c then
      let r := spanId f (c :: xs)
      match wordTok r.1 with
      | some t => (lex f r.2).map (t :: ·)
      | none => none
    else none

/-- scope: (name, typed), newest first -/
abbrev Scope := List (List UInt8 × Bool)

def idx : List UInt8 → Scope → Nat → Option Nat
  | _, [], _ => none
  | s, (t, _) :: ts, i => if s == t then some i else idx s ts (i + 1)

abbrev Defs := List (List UInt8 × Nat × E)

def findDef : List UInt8 → Defs → Option (Nat × E)
  | _, [] => none
  | s, (n, a, b) :: ds => if s == n then some (a, b) else findDef s ds

/-- does the expression contain a word-typed leaf (so Lean fixes its type to the file's type)?  `fl`: the scope's flags -/
def typed : List Bool → E → Bool
  | fl, .var i => fl.getD i false
  | fl, .add a b => typed fl a || typed fl b
  | fl, .sub a b => typed fl a || typed fl b
  | fl, .mul a b => typed fl a || typed fl b
  | fl, .let_ v b => typed (typed fl v :: fl) b
  | _, .call _ _ => true
  | fl, .ite _ _ _ t e => typed fl t || typed fl e
  | _, _ => false

def cmpOf : Tok → Option Cmp
  | .eqeq => some .eq
  | .lt => some .ltu
  | .le => some .leu
  | _ => none

mutual
def pExpr : Nat → Scope → Defs → List Tok → Option (E × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, Tok.klet :: Tok.id x :: Tok.assign :: ts =>
    match pExpr f sc ds ts with
    | some (v, Tok.semi :: r) =>
      match pExpr f ((x, typed (sc.map (·.2)) v) :: sc) ds r with
      | some (b, r2) => some (E.let_ v b, r2)
      | none => none
    | _ => none
  | f + 1, sc, ds, Tok.kif :: ts =>
    match pSum f sc ds ts with
    | some (a, op :: r) =>
      match cmpOf op with
      | some k =>
        match pSum f sc ds r with
        | some (b, Tok.kthen :: r2) =>
          if typed (sc.map (·.2)) a || typed (sc.map (·.2)) b then
            match pExpr f sc ds r2 with
            | some (t, Tok.kelse :: r3) =>
              match pExpr f sc ds r3 with
              | some (e, r4) => some (E.ite k a b t e, r4)
              | none => none
            | _ => none
          else none
        | _ => none
      | none => none
    | _ => none
  | f + 1, sc, ds, ts => pSum f sc ds ts
def pSum : Nat → Scope → Defs → List Tok → Option (E × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, ts =>
    match pMul f sc ds ts with
    | some (e, r) => pAdd f sc ds e r
    | none => none
def pAdd : Nat → Scope → Defs → E → List Tok → Option (E × List Tok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, acc, Tok.plus :: ts =>
    match pMul f sc ds ts with
    | some (e, r) => pAdd f sc ds (E.add acc e) r
    | none => none
  | f + 1, sc, ds, acc, Tok.minus :: ts =>
    match pMul f sc ds ts with
    | some (e, r) => pAdd f sc ds (E.sub acc e) r
    | none => none
  | _ + 1, _, _, acc, ts => some (acc, ts)
def pMul : Nat → Scope → Defs → List Tok → Option (E × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, ts =>
    match pApp f sc ds ts with
    | some (e, r) => pMulT f sc ds e r
    | none => none
def pMulT : Nat → Scope → Defs → E → List Tok → Option (E × List Tok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, acc, Tok.star :: ts =>
    match pApp f sc ds ts with
    | some (e, r) => pMulT f sc ds (E.mul acc e) r
    | none => none
  | _ + 1, _, _, acc, ts => some (acc, ts)
def pApp : Nat → Scope → Defs → List Tok → Option (E × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, Tok.id g :: ts =>
    match idx g sc 0 with
    | some i => some (E.var i, ts)
    | none =>
      match findDef g ds with
      | some (k, b) =>
        match pArgs f sc ds k ts with
        | some (as, r) => some (E.call b as, r)
        | none => none
      | none => none
  | _ + 1, _, _, Tok.minus :: Tok.num n :: ts => some (E.num (0 - n), ts)
  | f + 1, sc, ds, ts => pAtom f sc ds ts
def pArgs : Nat → Scope → Defs → Nat → List Tok → Option (E × List Tok)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, 0, ts => some (E.anil, ts)
  | f + 1, sc, ds, k + 1, ts =>
    match pAtom f sc ds ts with
    | some (e, r) =>
      match pArgs f sc ds k r with
      | some (es, r2) => some (E.acons e es, r2)
      | none => none
    | none => none
def pAtom : Nat → Scope → Defs → List Tok → Option (E × List Tok)
  | 0, _, _, _ => none
  | _ + 1, _, _, Tok.num n :: ts => some (E.num n, ts)
  | _ + 1, sc, ds, Tok.id g :: ts =>
    match idx g sc 0 with
    | some i => some (E.var i, ts)
    | none =>
      match findDef g ds with
      | some (0, b) => some (E.call b E.anil, ts)
      | _ => none
  | f + 1, sc, ds, Tok.lp :: ts =>
    match pExpr f sc ds ts with
    | some (e, Tok.rp :: r) => some (e, r)
    | _ => none
  | _, _, _, _ => none
end

mutual
def pParams : Nat → Scope → Nat → List Tok → Option (Scope × Nat × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, n, Tok.lp :: Tok.id x :: ts =>
    -- a binder group has at least one name (v1's `pParams` accepts `( : UInt64)`, which Lean rejects)
    match pNames f ((x, true) :: sc) (n + 1) ts with
    | some (sc2, n2, r) => pParams f sc2 n2 r
    | none => none
  | _ + 1, sc, n, ts => some (sc, n, ts)
def pNames : Nat → Scope → Nat → List Tok → Option (Scope × Nat × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, n, Tok.id x :: ts => pNames f ((x, true) :: sc) (n + 1) ts
  | _ + 1, sc, n, Tok.colon :: Tok.kty _ :: Tok.rp :: ts => some (sc, n, ts)
  | _, _, _, _ => none
end

def pDefs : Nat → Defs → List Tok → Option Prog
  | 0, _, _ => none
  | f + 1, ds, Tok.kdef :: Tok.id g :: ts =>
    match pParams f [] 0 ts with
    | some (sc, n, Tok.colon :: Tok.kty _ :: Tok.assign :: r) =>
      match (match findDef g ds with | some _ => none | none => pExpr f sc ds r) with
      | some (e, []) => some (n, e)
      | some (e, r2) => pDefs f ((g, n, e) :: ds) r2
      | none => none
    | _ => none
  | _, _, _ => none

def uniTy : Option Bool → List Tok → Option Bool
  | t, [] => t
  | none, Tok.kty s :: ts => uniTy (some s) ts
  | some t, Tok.kty s :: ts => if t == s then uniTy (some t) ts else none
  | t, _ :: ts => uniTy t ts

/-- signed comparisons in an `Int64` file -/
def sgn : E → E
  | .add a b => .add (sgn a) (sgn b) | .sub a b => .sub (sgn a) (sgn b) | .mul a b => .mul (sgn a) (sgn b)
  | .let_ v b => .let_ (sgn v) (sgn b) | .call b as => .call (sgn b) (sgn as)
  | .acons e r => .acons (sgn e) (sgn r)
  | .ite k a b t e =>
    .ite (match k with | .ltu => .lts | .leu => .les | k => k) (sgn a) (sgn b) (sgn t) (sgn e)
  | e => e

/-- the elaborator, with the program's type (`true` = `Int64`) -/
def nanoElabT (xs : List UInt8) : Option (Bool × Prog) :=
  match (if adjOk xs then lex xs.length xs else none) with
  | some ts =>
    match uniTy none ts with
    | some s => (pDefs (ts.length + 1) [] ts).map fun p => (s, if s then (p.1, sgn p.2) else p)
    | none => none
  | none => none

/-- **the v2 elaborator** -/
def nanoElab (xs : List UInt8) : Option Prog := (nanoElabT xs).map (·.2)

end Nano.V2
