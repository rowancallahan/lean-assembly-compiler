import Nano.Ast
/- nano elaborator: bytes -> tokens -> resolved AST.  Plain structural recursion on fuel / lists, byte lists. -/
namespace Nano

inductive Tok where
  | kdef | klet | kty (signed : Bool) | id (s : List UInt8) | num (n : UInt64)
  | lp | rp | colon | assign | plus | minus | star | semi

def isLetter (c : UInt8) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95
def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
def isWordC (c : UInt8) : Bool := isLetter c || isDigit c

/-- longest prefix of word characters (letters, digits, `_`), and the rest -/
def spanId : Nat → List UInt8 → List UInt8 × List UInt8
  | 0, xs => ([], xs)
  | f + 1, c :: xs =>
    if isWordC c then (let r := spanId f xs; (c :: r.1, r.2)) else ([], c :: xs)
  | _, [] => ([], [])

def kwDef : List UInt8 := [100, 101, 102]
def kwLet : List UInt8 := [108, 101, 116]
def kwTy : List UInt8 := [85, 73, 110, 116, 54, 52]
/-- `Int64` -/
def kwTyI : List UInt8 := [73, 110, 116, 54, 52]

/-- identifiers are one lowercase letter followed by digits / `_` only: no Lean keyword (all have two or more letters), no
Init declaration (checked by `Testing/nano/edge.py`: the roots of `Init` and its token table) -/
def identOk : List UInt8 → Bool
  | c :: cs => (97 ≤ c && c ≤ 122) && cs.all fun d => isDigit d || d == 95
  | [] => false

/-- a word: a numeral (digits only, wraps mod 2^64), a keyword or an identifier; anything else is rejected -/
def wordTok (w : List UInt8) : Option Tok :=
  match w with
  | [] => none
  | c :: _ =>
    if isDigit c then (if w.all isDigit then some (Tok.num (w.foldl (fun a d => a * 10 + (d - 48).toUInt64) 0)) else none)
    else if w == kwDef then some Tok.kdef else if w == kwLet then some Tok.klet
    else if w == kwTy then some (Tok.kty false) else if w == kwTyI then some (Tok.kty true)
    else if identOk w then some (Tok.id w) else none

/-- Lean needs whitespace before an application argument, so `g(x)`, `(x)(y)`, `(x)y` are rejected -/
def adjOk : List UInt8 → Bool
  | [] => true
  | p :: ys =>
    match ys with
    | [] => true
    | q :: _ => !((isWordC p || p == 41) && q == 40) && !(p == 41 && isWordC q) && adjOk ys

/-- tokens; whitespace is space and newline only (Lean rejects tabs, lone carriage returns); a line starts with a space,
newline or `def` -/
def lex : Nat → List UInt8 → Option (List Tok)
  | 0, xs => if xs.isEmpty then some [] else none
  | _ + 1, [] => some []
  | f + 1, c :: xs =>
    if c == 32 then lex f xs
    else if c == 10 then
      -- Lean rejects an application argument at column 0: a line may only start (column 0) with a space, a newline or `def`
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
      | 45 :: _ => none  -- `--` starts a comment in Lean: rejected
      | _ => (lex f xs).map (Tok.minus :: ·)
    else if c == 42 then (lex f xs).map (Tok.star :: ·)
    else if c == 59 then (lex f xs).map (Tok.semi :: ·)
    else if c == 58 then
      match xs with
      | 61 :: ys => (lex f ys).map (Tok.assign :: ·)
      | _ => (lex f xs).map (Tok.colon :: ·)
    else if isWordC c then
      let r := spanId f (c :: xs)
      match wordTok r.1 with
      | some t => (lex f r.2).map (t :: ·)
      | none => none
    else none

/-- position of a name in a list (newest first) -/
def idx : List UInt8 → List (List UInt8) → Nat → Option Nat
  | _, [], _ => none
  | s, t :: ts, i => if s == t then some i else idx s ts (i + 1)

/-- defs: newest first, (name, arity, body) -/
abbrev Defs := List (List UInt8 × Nat × Ex)

def findDef : List UInt8 → Defs → Option (Nat × Ex)
  | _, [] => none
  | s, (n, a, b) :: ds => if s == n then some (a, b) else findDef s ds

mutual
/-- `expr ::= let x := expr; expr | mul (('+'|'-') mul)*` -/
def pExpr : Nat → List (List UInt8) → Defs → List Tok → Option (Ex × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, Tok.klet :: Tok.id x :: Tok.assign :: ts =>
    match pExpr f sc ds ts with
    | some (v, Tok.semi :: r) =>
      match pExpr f (x :: sc) ds r with
      | some (b, r2) => some (Ex.let_ v b, r2)
      | none => none
    | _ => none
  | f + 1, sc, ds, ts =>
    match pMul f sc ds ts with
    | some (e, r) => pAdd f sc ds e r
    | none => none
def pAdd : Nat → List (List UInt8) → Defs → Ex → List Tok → Option (Ex × List Tok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, acc, Tok.plus :: ts =>
    match pMul f sc ds ts with
    | some (e, r) => pAdd f sc ds (Ex.add acc e) r
    | none => none
  | f + 1, sc, ds, acc, Tok.minus :: ts =>
    match pMul f sc ds ts with
    | some (e, r) => pAdd f sc ds (Ex.sub acc e) r
    | none => none
  | _ + 1, _, _, acc, ts => some (acc, ts)
def pMul : Nat → List (List UInt8) → Defs → List Tok → Option (Ex × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, ts =>
    match pApp f sc ds ts with
    | some (e, r) => pMulT f sc ds e r
    | none => none
def pMulT : Nat → List (List UInt8) → Defs → Ex → List Tok → Option (Ex × List Tok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, acc, Tok.star :: ts =>
    match pApp f sc ds ts with
    | some (e, r) => pMulT f sc ds (Ex.mul acc e) r
    | none => none
  | _ + 1, _, _, acc, ts => some (acc, ts)
/-- application: `g a1 … ak` for a def of arity k ≥ 1, else an atom -/
def pApp : Nat → List (List UInt8) → Defs → List Tok → Option (Ex × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, Tok.id g :: ts =>
    match idx g sc 0 with
    | some i => some (Ex.var i, ts)
    | none =>
      match findDef g ds with
      | some (k, b) =>
        match pArgs f sc ds k ts with
        | some (as, r) => some (Ex.call b as, r)
        | none => none
      | none => none
  | _ + 1, _, _, Tok.minus :: Tok.num n :: ts => some (Ex.num (0 - n), ts)
  | f + 1, sc, ds, ts => pAtom f sc ds ts
def pArgs : Nat → List (List UInt8) → Defs → Nat → List Tok → Option (Ex × List Tok)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, 0, ts => some (Ex.anil, ts)
  | f + 1, sc, ds, k + 1, ts =>
    match pAtom f sc ds ts with
    | some (e, r) =>
      match pArgs f sc ds k r with
      | some (es, r2) => some (Ex.acons e es, r2)
      | none => none
    | none => none
def pAtom : Nat → List (List UInt8) → Defs → List Tok → Option (Ex × List Tok)
  | 0, _, _, _ => none
  | _ + 1, _, _, Tok.num n :: ts => some (Ex.num n, ts)
  | _ + 1, sc, ds, Tok.id g :: ts =>
    match idx g sc 0 with
    | some i => some (Ex.var i, ts)
    | none =>
      match findDef g ds with
      | some (0, b) => some (Ex.call b Ex.anil, ts)
      | _ => none
  | f + 1, sc, ds, Tok.lp :: ts =>
    match pExpr f sc ds ts with
    | some (e, Tok.rp :: r) => some (e, r)
    | _ => none
  | _, _, _, _ => none
end

mutual
/-- parameter groups `(x y : UInt64)`; names newest first, count -/
def pParams : Nat → List (List UInt8) → Nat → List Tok → Option (List (List UInt8) × Nat × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, n, Tok.lp :: ts =>
    match pNames f sc n ts with
    | some (sc2, n2, r) => pParams f sc2 n2 r
    | none => none
  | _ + 1, sc, n, ts => some (sc, n, ts)
def pNames : Nat → List (List UInt8) → Nat → List Tok → Option (List (List UInt8) × Nat × List Tok)
  | 0, _, _, _ => none
  | f + 1, sc, n, Tok.id x :: ts => pNames f (x :: sc) (n + 1) ts
  | _ + 1, sc, n, Tok.colon :: Tok.kty _ :: Tok.rp :: ts => some (sc, n, ts)
  | _, _, _, _ => none
end

/-- `def f (x y : UInt64) : UInt64 := e`, repeated; the last def is the entry -/
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

/-- the one type of a token list: every type token is `UInt64` (`false`) or every one is `Int64` (`true`) -/
def uniTy : Option Bool → List Tok → Option Bool
  | t, [] => t
  | none, Tok.kty s :: ts => uniTy (some s) ts
  | some t, Tok.kty s :: ts => if t == s then uniTy (some t) ts else none
  | t, _ :: ts => uniTy t ts

/-- the elaborator, with the program's type (`true` = `Int64`) -/
def nanoElabT (xs : List UInt8) : Option (Bool × Prog) :=
  match (if adjOk xs then lex xs.length xs else none) with
  | some ts =>
    match uniTy none ts with
    | some s => (pDefs (ts.length + 1) [] ts).map (s, ·)
    | none => none
  | none => none

/-- the elaborator -/
def nanoElab (xs : List UInt8) : Option Prog := (nanoElabT xs).map (·.2)

end Nano
