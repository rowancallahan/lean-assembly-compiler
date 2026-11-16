import Nano.Ast
/- nano elaborator: bytes -> tokens -> resolved AST.  Plain structural recursion on fuel / lists, byte lists. -/
namespace Nano

inductive Tok where
  | kdef | klet | kty | id (s : List UInt8) | num (n : UInt64)
  | lp | rp | colon | assign | plus | minus | star | semi

def isLetter (c : UInt8) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95
def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57

/-- longest prefix of identifier characters, and the rest -/
def spanId : Nat → List UInt8 → List UInt8 × List UInt8
  | 0, xs => ([], xs)
  | f + 1, c :: xs =>
    if isLetter c || isDigit c then (let r := spanId f xs; (c :: r.1, r.2)) else ([], c :: xs)
  | _, [] => ([], [])

def spanNum : Nat → UInt64 → List UInt8 → UInt64 × List UInt8
  | 0, a, xs => (a, xs)
  | f + 1, a, c :: xs => if isDigit c then spanNum f (a * 10 + (c - 48).toUInt64) xs else (a, c :: xs)
  | _, a, [] => (a, [])

def kwDef : List UInt8 := [100, 101, 102]
def kwLet : List UInt8 := [108, 101, 116]
def kwTy : List UInt8 := [85, 73, 110, 116, 54, 52]

def identTok (s : List UInt8) : Tok :=
  if s == kwDef then .kdef else if s == kwLet then .klet else if s == kwTy then .kty else .id s

def lex : Nat → List UInt8 → Option (List Tok)
  | 0, xs => if xs.isEmpty then some [] else none
  | _ + 1, [] => some []
  | f + 1, c :: xs =>
    if c == 32 || c == 10 || c == 13 || c == 9 then lex f xs
    else if c == 40 then (lex f xs).map (Tok.lp :: ·)
    else if c == 41 then (lex f xs).map (Tok.rp :: ·)
    else if c == 43 then (lex f xs).map (Tok.plus :: ·)
    else if c == 45 then (lex f xs).map (Tok.minus :: ·)
    else if c == 42 then (lex f xs).map (Tok.star :: ·)
    else if c == 59 then (lex f xs).map (Tok.semi :: ·)
    else if c == 58 then
      match xs with
      | 61 :: ys => (lex f ys).map (Tok.assign :: ·)
      | _ => (lex f xs).map (Tok.colon :: ·)
    else if isDigit c then
      let r := spanNum f 0 (c :: xs); (lex f r.2).map (Tok.num r.1 :: ·)
    else if isLetter c then
      let r := spanId f (c :: xs); (lex f r.2).map (identTok r.1 :: ·)
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
  | _ + 1, sc, n, Tok.colon :: Tok.kty :: Tok.rp :: ts => some (sc, n, ts)
  | _, _, _, _ => none
end

/-- `def f (x y : UInt64) : UInt64 := e`, repeated; the last def is the entry -/
def pDefs : Nat → Defs → List Tok → Option Prog
  | 0, _, _ => none
  | f + 1, ds, Tok.kdef :: Tok.id g :: ts =>
    match pParams f [] 0 ts with
    | some (sc, n, Tok.colon :: Tok.kty :: Tok.assign :: r) =>
      match pExpr f sc ds r with
      | some (e, []) => some (n, e)
      | some (e, r2) => pDefs f ((g, n, e) :: ds) r2
      | none => none
    | _ => none
  | _, _, _ => none

/-- the elaborator -/
def nanoElab (xs : List UInt8) : Option Prog :=
  match lex xs.length xs with
  | some ts => pDefs (ts.length + 1) [] ts
  | none => none

end Nano
