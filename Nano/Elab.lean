import Nano.Ast
/- nano elaborator: bytes -> tokens -> resolved AST.  Plain structural recursion on fuel / lists, byte lists. -/
namespace Nano

inductive Tok where
  | kdef | klet | kty (signed : Bool) | id (s : List UInt8) | num (n : UInt64)
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
/-- `Int64` -/
def kwTyI : List UInt8 := [73, 110, 116, 54, 52]

def isLower (c : UInt8) : Bool := 97 ≤ c && c ≤ 122

/-- after the leading letters: digits, or `_` followed by a digit -/
def nameTail : List UInt8 → Bool
  | [] => true
  | 95 :: d :: r => isDigit d && nameTail r
  | c :: r => isDigit c && nameTail r

/-- the shape of a nano name: 1 to 3 lowercase letters, then digits or `_` digit groups (`x`, `sq`, `add3`, `x_1`) -/
def nameShape : List UInt8 → Bool
  | a :: b :: c :: r => isLower a && (if isLower b then (if isLower c then nameTail r else nameTail (c :: r))
      else nameTail (b :: c :: r))
  | [a, b] => isLower a && (isLower b || isDigit b)
  | [a] => isLower a
  | [] => false

/-- names of that shape that Lean reads otherwise (computed exhaustively for every name of the shape with at most
one digit or `_1` suffix: Lean keyword tokens, root declarations and `export` aliases; `def`/`let` are nano keywords) -/
def reserved : List (List UInt8) :=
  [
   [97, 110, 100], [97, 116], [98, 105, 102], [98, 110, 101], [98, 121], [100, 111],  -- and at bif bne by do
   [101, 110, 100], [102, 111, 114], [102, 117, 110], [103, 101, 116], [105, 100], [105, 102],  -- end for fun get id if
   [105, 110], [105, 116, 101], [109, 97, 120], [109, 105, 110], [109, 116], [109, 117, 116],  -- in ite max min mt mut
   [110, 111, 116], [111, 114], [114, 102, 108], [115, 101, 116], [116, 114, 121], [120, 111, 114]]  -- not or rfl set try xor

/-- a word: a keyword of nano, or a name (shape, not reserved); `none` = rejected -/
def identTok? (s : List UInt8) : Option Tok :=
  if s == kwDef then some .kdef else if s == kwLet then some .klet else if s == kwTy then some (.kty false)
  else if s == kwTyI then some (.kty true)
  else if nameShape s && !reserved.contains s then some (.id s) else none

/-- Lean rejects a term token at column 0 (a body or an argument there): a line starts with a space, a newline, or `def` -/
def lineStart : List UInt8 → Bool
  | [] => true
  | 32 :: _ => true
  | 10 :: _ => true
  | 13 :: _ => true
  | 100 :: 101 :: 102 :: z => (match z with | d :: _ => !(isLetter d || isDigit d) | [] => true)
  | _ => false

def lex : Nat → List UInt8 → Option (List Tok)
  | 0, xs => if xs.isEmpty then some [] else none
  | _ + 1, [] => some []
  | f + 1, c :: xs =>
    if c == 32 then lex f xs
    else if c == 10 then (if lineStart xs then lex f xs else none)
    else if c == 13 then  -- CR only before LF (Lean rejects a lone CR); tabs are rejected (Lean rejects them)
      match xs with
      | 10 :: ys => if lineStart ys then lex f ys else none
      | _ => none
    else if c == 40 then (lex f xs).map (Tok.lp :: ·)
    else if c == 41 then  -- Lean needs whitespace before an argument: `)(`, `)x`, `)5` rejected
      match xs with
      | d :: _ => if d == 40 || isLetter d || isDigit d then none else (lex f xs).map (Tok.rp :: ·)
      | [] => (lex f xs).map (Tok.rp :: ·)
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
    else if isDigit c then  -- a numeral must not run into a name character (`0x10`, `1e5`, `1_000`)
      let r := spanNum f 0 (c :: xs)
      match r.2 with
      | d :: _ => if isLetter d || d == 40 then none else (lex f r.2).map (Tok.num r.1 :: ·)
      | [] => (lex f r.2).map (Tok.num r.1 :: ·)
    else if isLetter c then
      let r := spanId f (c :: xs)
      match identTok? r.1, r.2 with
      | _, 40 :: _ => none  -- `x(`: rejected (Lean needs whitespace before an argument)
      | some t, _ => (lex f r.2).map (t :: ·)
      | none, _ => none
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
    | some (sc2, n2, r) => if n2 == n then none else pParams f sc2 n2 r  -- `( : T)` rejected
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
    if (findDef g ds).isSome then none else  -- a name defined twice: Lean rejects
    match pParams f [] 0 ts with
    | some (sc, n, Tok.colon :: Tok.kty _ :: Tok.assign :: r) =>
      match pExpr f sc ds r with
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
  match lex xs.length xs with
  | some ts =>
    match uniTy none ts with
    | some s => (pDefs (ts.length + 1) [] ts).map (s, ·)
    | none => none
  | none => none

/-- the elaborator -/
def nanoElab (xs : List UInt8) : Option Prog := (nanoElabT xs).map (·.2)

end Nano
