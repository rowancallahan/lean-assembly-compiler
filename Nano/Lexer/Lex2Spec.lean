/- Nano/Lexer/Lex2Spec: the SPECIFICATION of the S lexer (`C.s10`), independent of Lex2's code.
`Lexes x t`: the byte list `x` lexes to the token word list `t`.  One token at a time (`step`), maximal munch:
whitespace (space, newline) is skipped; the operator table is searched longest-first; a word is a maximal run of
[A-Za-z0-9_'] (a keyword/prim, an identifier `14 (1,b)* 0`, or, when it starts with a digit, a decimal number
`5` + 8 little-endian bytes of the value mod 2^64, all characters of the word must then be digits).
Trivia (no tokens; exp-syntax, Testing/notes/SYNTAX_EXP.md): two dashes up to the newline; a nested block comment
(slash-dash ... dash-slash; unterminated: rejected); a doc comment (slash-dash-dash or slash-dash-bang): as Lean, the
whitespace, line comments and plain block comments right after the opener are skipped before its nested body; an
attribute `@[ name, … ]` (names `inline`, `reducible`); the word `private`.  A slash-dash-dash doc comment, an
attribute and `private` must be followed (after whitespace and comments) by what Lean allows after them: `@[`, `private`
or `def` (`declNext`); a slash-dash-bang module doc by a command (`cmdNext`), so nano accepts no modifier Lean
rejects.  Scope lines `namespace N`, `section`, `end`, `end N` (`scopeLine`, `nsName`) become marker tokens
(`scopeTok`), which `DsSpec.frame` allows only around the whole program; the word `open` is rejected.
Anything else (and a digit-led word with a non-digit) is rejected: no `step`, so no `Lexes`. -/
import Nano.Main.Prelude
namespace LexSpec

def isW (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || b == 95 || b == 39 || (48 ≤ b && b ≤ 57)
def isD (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- operators, longest first: (bytes, tag). -/
def opTable : List (List UInt8 × UInt64) :=
  [([38, 38, 38], 26), ([124, 124, 124], 27), ([60, 60, 60], 28), ([62, 62, 62], 29), ([226, 134, 146], 17),
   ([58, 61], 9), ([61, 62], 19), ([61, 61], 23), ([195, 151], 16),
   ([40], 6), ([41], 7), ([58], 8), ([43], 10), ([45], 11), ([42], 12), ([59], 13), ([44], 15),
   ([124], 18), ([60], 20), ([91], 30), ([93], 31)]

/-- keywords and prims: (ASCII bytes of def let UInt64 if then else Nat Buf List UInt8 len' rd len put bnew bsize bget bset bpush, tag). -/
def kwTable : List (List UInt8 × UInt64) :=
  [([100, 101, 102], 1),
   ([108, 101, 116], 2),
   ([85, 73, 110, 116, 54, 52], 3),
   ([105, 102], 32),
   ([116, 104, 101, 110], 33),
   ([101, 108, 115, 101], 34),
   ([78, 97, 116], 35),
   ([66, 117, 102], 36),
   ([76, 105, 115, 116], 37),
   ([85, 73, 110, 116, 56], 38),
   ([108, 101, 110, 39], 39),
   ([114, 100], 40),
   ([108, 101, 110], 41),
   ([112, 117, 116], 42),
   ([98, 110, 101, 119], 43),
   ([98, 115, 105, 122, 101], 44),
   ([98, 103, 101, 116], 45),
   ([98, 115, 101, 116], 46),
   ([98, 112, 117, 115, 104], 47)]

/-- the scope words `namespace`, `section`, `end`, and `open` (rejected: it can change name resolution) -/
def NS : List UInt8 := [110, 97, 109, 101, 115, 112, 97, 99, 101]
def SEC : List UInt8 := [115, 101, 99, 116, 105, 111, 110]
def END : List UInt8 := [101, 110, 100]
def OPEN : List UInt8 := [111, 112, 101, 110]
/-- the scope words and their `scopeLine` kind -/
def scopeKw : List (List UInt8 × Nat) := [(NS, 0), (SEC, 1), (END, 2)]
/-- words that are dropped: private -/
def dropKw : List (List UInt8) := [[112, 114, 105, 118, 97, 116, 101]]

/-- the rest after the dash-slash closing a block comment; `d` = comments still open inside it -/
def blockEnd : Nat → List UInt8 → Option (List UInt8)
  | _, [] => none
  | _, [_] => none
  | d, c :: c' :: r =>
    if c = 45 ∧ c' = 47 then (if d = 0 then some r else blockEnd (d - 1) r)
    else if c = 47 ∧ c' = 45 then blockEnd (d + 1) r
    else blockEnd d (c' :: r)

/-- Lean's whitespace after a doc-comment opener (fuel `f`): spaces, newlines (CR LF too), dash-dash lines and plain
nested block comments; the rest from the comment body's first byte.  A tab or an isolated CR is an error, as in Lean's
`whitespace` (Lean/Parser/Basic.lean: "tabs are not allowed", "isolated carriage returns are not allowed"); a plain block
comment skips the byte after its opener before its body, as Lean's `whitespace` does (`s.next` before
`finishCommentBlock`), so slash-dash-slash-dash does not nest -/
def docWs : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, c :: r =>
    if c = 32 ∨ c = 10 ∨ (c = 13 ∧ r.head? = some 10) then docWs f r
    else if c = 9 ∨ c = 13 then none
    else if c = 45 ∧ r.head? = some 45 then docWs f (r.dropWhile (· != 10))
    else if c = 47 ∧ r.head? = some 45 ∧ r.tail.head? ≠ some 45 ∧ r.tail.head? ≠ some 33 then
      (blockEnd 0 r.tail.tail).bind (docWs f)
    else some (c :: r)

/-- a scope name nano accepts (Testing/notes/SYNTAX_EXP.md, frame rule): one component, a capital letter, small
letters, then at least one digit, and not starting `Int` or `Float`.  The only root names of this shape in Lean 4.34.1
(`import Lean`, all constants) are Int8 Int16 Int32 Int64 Float32, so a declaration or a name inside such a namespace
cannot meet an existing one -/
def nsName : List UInt8 → Bool
  | c :: r =>
    let a := r.takeWhile fun b => 97 ≤ b && b ≤ 122
    let d := r.dropWhile fun b => 97 ≤ b && b ≤ 122
    65 ≤ c && c ≤ 90 && d != [] && d.all isD && !(c :: a == [73, 110, 116]) && !(c :: a == [70, 108, 111, 97, 116])
  | [] => false

/-- the rest of a `namespace` (`k = 0`: a name required), `section` (`k = 1`: no name) or `end` (`k = 2`: a name
optional) line: a space and the name (`nsName`), spaces, then a newline or the end of the text; the name and the rest
from the newline -/
def scopeLine (k : Nat) (r : List UInt8) : Option (List UInt8 × List UInt8) :=
  let s := r.dropWhile (· == 32)
  let n := s.takeWhile isW
  let e := (s.dropWhile isW).dropWhile (· == 32)
  if (e.head? = none ∨ e.head? = some 10) ∧ (if n = [] then k ≠ 0 else k ≠ 1 ∧ r.head? = some 32 ∧ nsName n = true)
  then some (n, e) else none

/-- the attribute names accepted: `inline`, `reducible` -/
def attrNames : List (List UInt8) := [[105, 110, 108, 105, 110, 101], [114, 101, 100, 117, 99, 105, 98, 108, 101]]

/-- the contents of `@[` … `]` as Lean's grammar, names from `attrNames`: `name (, name)*`, spaces around; the rest after
the `]`.  `w`: the name being read (reversed); `d`: a name has been read since the start or the last comma -/
def attrEnd : List UInt8 → List UInt8 → Bool → Option (List UInt8)
  | [], _, _ => none
  | b :: r, w, d =>
    if isW b then (if d then none else attrEnd r (b :: w) false)
    else if w ≠ [] ∧ !attrNames.contains w.reverse then none
    else
      let d' := d || w ≠ []
      if b == 32 then attrEnd r [] d'
      else if b == 44 then (if d' then attrEnd r [] false else none)
      else if b == 93 then (if d' then some r else none)
      else none

/-- `w` followed by a non-name byte (or the end) starts `l` -/
def startsWord (w l : List UInt8) : Bool := w.isPrefixOf l && !(((l.drop w.length).head?.map isW).getD false)

/-- the words `def`, `private` -/
def DEF : List UInt8 := [100, 101, 102]
def PRIV : List UInt8 := [112, 114, 105, 118, 97, 116, 101]

/-- what may follow a declaration modifier, after Lean's whitespace and comments (`docWs`): `@[` (`k = 2`: after a doc
comment), `private` (`k ≥ 1`: after a doc comment or an attribute) or `def` (Lean: docComment? attributes? private? def) -/
def declNext (k : Nat) (l : List UInt8) : Bool :=
  match docWs (l.length + 1) l with
  | some u => (k == 2 && [64, 91].isPrefixOf u) || (1 ≤ k && startsWord PRIV u) || startsWord DEF u
  | none => false

/-- what may follow a module doc comment (slash-dash-bang), after Lean's whitespace and comments: a command
(slash-dash-dash, slash-dash-bang, `@[`, `private`, `def`, `namespace`, `section`, `end`); Lean ends a term at a module doc
comment and then expects a command.  Stricter than Lean: the end of the text is not accepted here -/
def cmdNext (l : List UInt8) : Bool :=
  match docWs (l.length + 1) l with
  | some u => [47, 45].isPrefixOf u || [64, 91].isPrefixOf u || startsWord PRIV u || startsWord DEF u ||
      startsWord NS u || startsWord SEC u || startsWord END u
  | none => false

/-- a scope marker: `48`/`49` (opens/closes the scope of a name) with the name's identifier token, `50`/`51` (opens/closes
an unnamed section) -/
def scopeTok (o : Bool) (n : List UInt8) : List UInt64 :=
  if n = [] then [if o then 50 else 51] else (if o then 48 else 49) :: 14 :: (n.flatMap fun b => [1, b.toUInt64]) ++ [0]

/-- decimal value mod 2^64 -/
def numVal (w : List UInt8) : Nat := w.foldl (fun a b => (a * 10 + (b.toNat - 48)) % 2 ^ 64) 0
/-- 8 little-endian bytes -/
def le8 (n : Nat) : List UInt64 := (List.range 8).map fun i => ((n / 256 ^ i) % 256).toUInt64

/-- one lexing step: emitted words and the rest of the input -/
def step : List UInt8 → Option (List UInt64 × List UInt8)
  | [] => none
  | c :: r =>
    if c == 32 || c == 10 then some ([], r)
    else if c == 45 && r.head? == some 45 then some ([], r.tail.dropWhile (· != 10))
    else if c == 47 && r.head? == some 45 then
      (if r.tail.head? == some 45 || r.tail.head? == some 33 then (docWs r.length r.tail.tail).bind (blockEnd 0)
       else blockEnd 0 r.tail.tail).bind fun t =>
        if r.tail.head? == some 45 && !declNext 2 t then none
        else if r.tail.head? == some 33 && !cmdNext t then none else some ([], t)
    else if c == 64 && r.head? == some 91 then
      (attrEnd r.tail [] false).bind fun t => if declNext 1 t then some ([], t) else none
    else match opTable.find? (fun e => e.1.isPrefixOf (c :: r)) with
      | some (s, k) => some ([k], (c :: r).drop s.length)
      | none =>
        let w := (c :: r).takeWhile isW
        let rest := (c :: r).dropWhile isW
        if isD c then (if w.all isD then some (5 :: le8 (numVal w), rest) else none)
        else if isW c then
          if w == OPEN then none
          else match scopeKw.lookup w with
          | some k => (scopeLine k rest).map fun (n, e) => (scopeTok (k != 2) n, e)
          | none =>
            if dropKw.contains w then (if declNext 0 rest then some ([], rest) else none)
            else some ((match kwTable.lookup w with
                   | some k => [k]
                   | none => 14 :: (w.flatMap fun b => [1, b.toUInt64]) ++ [0]), rest)
        else none

inductive Lexes : List UInt8 → List UInt64 → Prop
  | nil : Lexes [] []
  | cons {l e r t} : step l = some (e, r) → Lexes r t → Lexes l (e ++ t)

end LexSpec

