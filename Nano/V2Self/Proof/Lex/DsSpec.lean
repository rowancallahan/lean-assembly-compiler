/- Nano/V2Self/Proof/Lex/DsSpec: the SPECIFICATION of the match desugaring stage (`C.t10`; exp-syntax,
Testing/notes/SYNTAX_EXP.md §2), independent of its code.  `ds ts = some ts'`: the lexer's token words `ts` desugar to
the token words `ts'` that the parser reads.  A token is `5` + 8 value words, `14 (1 b)* 0` (an identifier) or one word.
`match E with | 3 => a | 7 => b | y => c` becomes `let μ := E; if μ == 3 then a else if μ == 7 then b else let y := μ; c`
where μ = `MU`, an identifier no Lean text can spell; `| _ => e` becomes `else e`; a FIRST arm `| (x, y) => e` becomes
`let (x, y) := μ; e`.  Matches are tracked per paren depth (`cs`, innermost first): 0 none, 1 open (no catch-all arm
yet), 2 closed.  A match ends at the `)` of its depth, the next `def` (depth 0 only) or the end of the text, and must be
closed by then; an arm after the catch-all arm is rejected; a match inside a scrutinee is rejected. -/
import Nano.V2Self.Prelude
namespace DsSpec

/-- the identifier `$` (not a Lean name): the scrutinee's slot -/
def MU : List UInt64 := [14, 1, 36, 0]
/-- the identifiers `match`, `with`, `_` -/
def MATCH : List UInt64 := [14, 1, 109, 1, 97, 1, 116, 1, 99, 1, 104, 0]
def WITH : List UInt64 := [14, 1, 119, 1, 105, 1, 116, 1, 104, 0]
def WILD : List UInt64 := [14, 1, 95, 0]

/-- the rest of an identifier token after its `14`: `(1 b)* 0` -/
def identTok : List UInt64 → Option (List UInt64 × List UInt64)
  | 0 :: r => some ([0], r)
  | 1 :: b :: r => (identTok r).map fun (w, r') => (1 :: b :: w, r')
  | _ => none

/-- the first token and the rest -/
def splitTok : List UInt64 → Option (List UInt64 × List UInt64)
  | [] => none
  | k :: r =>
    if k = 5 then (if 8 ≤ r.length then some (5 :: r.take 8, r.drop 8) else none)
    else if k = 14 then (identTok r).map fun (w, r') => (14 :: w, r')
    else some ([k], r)

/-- an arm's pattern and the rest after its `=>` -/
inductive Pat | lit (w : List UInt64) | wild | var (y : List UInt64) | pair (x y : List UInt64)

def pat (ts : List UInt64) : Option (Pat × List UInt64) :=
  (splitTok ts).bind fun (a, r) =>
    if a.head? = some 5 then (match r with | 19 :: r' => some (.lit a, r') | _ => none)
    else if a = WILD then (match r with | 19 :: r' => some (.wild, r') | _ => none)
    else if a.head? = some 14 then (match r with | 19 :: r' => some (.var a, r') | _ => none)
    else if a = [6] then
      (splitTok r).bind fun (x, r1) =>
        if x.head? = some 14 then
          match r1 with
          | 15 :: r2 => (splitTok r2).bind fun (y, r3) =>
              if y.head? = some 14 then (match r3 with | 7 :: 19 :: r4 => some (.pair x y, r4) | _ => none) else none
          | _ => none
        else none
    else none

/-- the code of an arm (`first`: the first arm of its match) and whether it is the catch-all arm -/
def armCode (first : Bool) : Pat → Option (List UInt64 × Bool)
  | .lit w => some ((if first then [] else [34]) ++ [32] ++ MU ++ [23] ++ w ++ [33], false)
  | .wild => some ((if first then [] else [34]), true)
  | .var y => some ((if first then [] else [34]) ++ [2] ++ y ++ [9] ++ MU ++ [13], true)
  | .pair x y => if first then some ([2, 6] ++ x ++ [15] ++ y ++ [7, 9] ++ MU ++ [13], true) else none

def cell (c : Bool) : Nat := if c then 2 else 1

/-- the desugaring loop: `cs` the match cells per depth (innermost first), `sc` inside a scrutinee -/
def go : Nat → List UInt64 → List Nat → Bool → Option (List UInt64)
  | 0, _, _, _ => none
  | _ + 1, [], cs, sc => if !sc ∧ cs.length = 1 ∧ cs.head? ≠ some 1 then some [] else none
  | f + 1, ts, cs, sc => (splitTok ts).bind fun (a, r) =>
    if sc then
      if a = WITH then
        match r with
        | 18 :: r1 => (pat r1).bind fun (p, r2) => (armCode true p).bind fun (w, c) =>
            (go f r2 (cell c :: cs.tail) false).map fun o => [13] ++ w ++ o
        | _ => none
      else if a = MATCH ∨ a = [18] ∨ a = [19] then none
      else (go f r cs true).map (a ++ ·)
    else if a = MATCH then
      if cs.head? = some 1 then none else (go f r cs true).map ([2] ++ MU ++ [9] ++ ·)
    else if a = WITH then none
    else if a = [18] then
      if cs.head? = some 1 then
        (pat r).bind fun (p, r2) => (armCode false p).bind fun (w, c) =>
          (go f r2 (cell c :: cs.tail) false).map (w ++ ·)
      else if cs.head? = some 2 then none
      else (go f r cs false).map (18 :: ·)
    else if a = [6] then (go f r (0 :: cs) false).map (6 :: ·)
    else if a = [7] then
      if cs.head? = some 1 ∨ cs.length ≤ 1 then none else (go f r cs.tail false).map (7 :: ·)
    else if a = [1] then
      if cs.length = 1 ∧ cs.head? ≠ some 1 then (go f r [0] false).map (1 :: ·) else none
    else (go f r cs false).map (a ++ ·)

/-- every token is well formed and none is `match` -/
def noMatch : Nat → List UInt64 → Bool
  | 0, _ => false
  | _ + 1, [] => true
  | f + 1, ts => match splitTok ts with
    | none => false
    | some (a, r) => a != MATCH && noMatch f r

/-- **the desugaring**: fewer than 2^24 words in and out; a text without `match` is unchanged -/
def ds (ts : List UInt64) : Option (List UInt64) :=
  if ts.length < 2 ^ 24 then
    if noMatch (ts.length + 1) ts then some ts
    else (go (ts.length + 1) ts [0] false).bind fun o => if o.length < 2 ^ 24 then some o else none
  else none

end DsSpec
