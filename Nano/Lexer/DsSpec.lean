/- Nano/Lexer/DsSpec: the SPECIFICATION of the match desugaring stage (`C.t10`; exp-syntax,
Testing/notes/SYNTAX_EXP.md §2), independent of its code.  `ds ts = some ts'`: the lexer's token words `ts` desugar to
the token words `ts'` that the parser reads.  A token is `5` + 8 value words, `14 (1 b)* 0` (an identifier) or one word.
`match E with | 3 => a | 7 => b | y => c` becomes `let μ := E; if μ == 3 then a else if μ == 7 then b else let y := μ; c`
where μ = `MU`, an identifier no Lean text can spell; `| _ => e` becomes `else e`; a FIRST arm `| (x, y) => e` becomes
`let (x, y) := μ; e`.  Matches are tracked per paren depth (`cs`, innermost first): 0 none, 1 open (no catch-all arm
yet), 2 closed.  A match ends at the `)` of its depth, the next `def` (depth 0 only) or the end of the text, and must be
closed by then; an arm after the catch-all arm is rejected; a match inside a scrutinee is rejected; two literal arms of
one match with the same value are rejected (`dupOk`; Lean: redundant alternative). -/
import Nano.Main.Prelude
import Nano.Lexer.Lex2Spec
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

/-- **no redundant arm**: two literal arms of one match never have the same value (Lean rejects a redundant
alternative; a literal word is its value mod 2^64).  Matches and arms are found as `go` finds them.  Each match gets a
fresh number at its `with` (`m`: the last one); `ids`: per paren depth (innermost first) the number of the match open
there (0: none, or after its catch-all arm); `seen`: the (match number, literal) pairs of the arms read so far;
`sc`: inside a scrutinee.  Only `true` matters (a text `go` rejects may pass). -/
def dupOk : Nat → List UInt64 → List Nat → List (Nat × List UInt64) → Nat → Bool → Bool
  | 0, _, _, _, _, _ => false
  | _ + 1, [], _, _, _, _ => true
  | f + 1, ts, ids, seen, m, sc => match splitTok ts with
    | none => true
    | some (a, r) =>
      if sc then
        if a = WITH then
          match r with
          | 18 :: r1 => match pat r1 with
            | some (.lit w, r2) => dupOk f r2 ((m + 1) :: ids.tail) ((m + 1, w) :: seen) (m + 1) false
            | some (_, r2) => dupOk f r2 (0 :: ids.tail) seen (m + 1) false
            | none => true
          | _ => true
        else dupOk f r ids seen m true
      else if a = MATCH then dupOk f r ids seen m true
      else if a = [18] then
        match ids.head? with
        | some k =>
          if k = 0 then dupOk f r ids seen m false
          else match pat r with
            | some (.lit w, r2) => if seen.contains (k, w) then false else dupOk f r2 ids ((k, w) :: seen) m false
            | some (_, r2) => dupOk f r2 (0 :: ids.tail) seen m false
            | none => true
        | none => dupOk f r ids seen m false
      else if a = [6] then dupOk f r (0 :: ids) seen m false
      else if a = [7] then dupOk f r ids.tail seen m false
      else if a = [1] then dupOk f r [0] seen m false
      else dupOk f r ids seen m false

/-- every token is well formed and none is `match` -/
def noMatch : Nat → List UInt64 → Bool
  | 0, _ => false
  | _ + 1, [] => true
  | f + 1, ts => match splitTok ts with
    | none => false
    | some (a, r) => a != MATCH && noMatch f r

/-- **the scope frame** (Testing/notes/SYNTAX_EXP.md, frame rule): the lexer's scope markers (`LexSpec.scopeTok`) may only
open scopes before every other token (`ph = 0`) and close them after every other token (`ph = 2`); each `end` names the
innermost open scope (`st`, innermost first; `[]`: an unnamed section); scopes may stay open at the end, as in Lean.
The other tokens, in order.  So all definitions are in the same scope, and nano's flat names mean what Lean's do. -/
def frame : Nat → List UInt64 → Nat → List (List UInt64) → Option (List UInt64)
  | 0, _, _, _ => none
  | _ + 1, [], _, _ => some []
  | f + 1, k :: r, ph, st =>
    if k = 48 then
      (if ph = 0 then (match splitTok r with | some (n, r') => frame f r' 0 (n :: st) | none => none) else none)
    else if k = 50 then (if ph = 0 then frame f r 0 ([] :: st) else none)
    else if k = 49 then
      (match splitTok r with | some (n, r') => if st.head? = some n then frame f r' 2 st.tail else none | none => none)
    else if k = 51 then (if st.head? = some [] then frame f r 2 st.tail else none)
    else if ph = 2 then none
    else match splitTok (k :: r) with
      | some (a, r') => (frame f r' 1 st).map (a ++ ·)
      | none => none

/-- the match desugaring of the framed tokens -/
def ds0 (ts : List UInt64) : Option (List UInt64) :=
  if ts.length < 2 ^ 24 then
    if noMatch (ts.length + 1) ts then some ts
    else if !dupOk (ts.length + 1) ts [0] [] 0 false then none
    else (go (ts.length + 1) ts [0] false).bind fun o => if o.length < 2 ^ 24 then some o else none
  else none

/-- **the desugaring**: the scope frame (`frame`), then fewer than 2^24 words in and out; a text without `match` is
unchanged; no redundant arm -/
def ds (ts : List UInt64) : Option (List UInt64) := (frame (ts.length + 1) ts 0 []).bind ds0

/-- **the token words a text means**: it lexes (`LexSpec.Lexes`) and the lexer's words desugar (`ds`) to `ts` -/
def LexesD (x : List UInt8) (ts : List UInt64) : Prop := ∃ t0, LexSpec.Lexes x t0 ∧ ds t0 = some ts

end DsSpec
