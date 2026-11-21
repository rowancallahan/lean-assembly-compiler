/- Nano/V2Self/Proof/Lex/Lex2Spec: the SPECIFICATION of the S lexer (`C.s10`), independent of Lex2's code.
`Lexes x t`: the byte list `x` lexes to the token word list `t`.  One token at a time (`step`), maximal munch:
whitespace (space, newline) is skipped; the operator table is searched longest-first; a word is a maximal run of
[A-Za-z0-9_'] (a keyword/prim, an identifier `14 (1,b)* 0`, or, when it starts with a digit, a decimal number
`5` + 8 little-endian bytes of the value mod 2^64, all characters of the word must then be digits).
Trivia (no tokens; exp-syntax, Testing/notes/SYNTAX_EXP.md): two dashes up to the newline; a nested block comment
(slash-dash ... dash-slash; unterminated: rejected); a doc comment (slash-dash-dash or slash-dash-bang): as Lean, the
whitespace, line comments and plain block comments right after the opener are skipped before its nested body; an
attribute `@[ … ]` of names, spaces and commas; the words `namespace`, `open`, `section`, `end` with the rest of their
line, which must be names, dots and spaces and must not contain the word `in` (`open X in e` is a Lean term); the word
`private`.
Anything else (and a digit-led word with a non-digit) is rejected: no `step`, so no `Lexes`. -/
import Nano.V2Self.Prelude
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

/-- words that skip the rest of their line: namespace open section end -/
def lineKw : List (List UInt8) :=
  [[110, 97, 109, 101, 115, 112, 97, 99, 101], [111, 112, 101, 110], [115, 101, 99, 116, 105, 111, 110], [101, 110, 100]]
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
nested block comments; the rest from the comment body's first byte -/
def docWs : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, c :: r =>
    if c = 32 ∨ c = 10 ∨ (c = 13 ∧ r.head? = some 10) then docWs f r
    else if c = 45 ∧ r.head? = some 45 then docWs f (r.dropWhile (· != 10))
    else if c = 47 ∧ r.head? = some 45 ∧ r.tail.head? ≠ some 45 ∧ r.tail.head? ≠ some 33 then
      (blockEnd 0 r.tail).bind (docWs f)
    else some (c :: r)

/-- `in` as a word: after a space, followed by the end, a space or a newline -/
def inWord : List UInt8 → Bool
  | 105 :: 110 :: t => t.head? == none || t.head? == some 32 || t.head? == some 10
  | _ => false

/-- the rest of a `namespace`/`open`/`section`/`end` line: names, dots, spaces up to the newline, no word `in` -/
def lineOk : List UInt8 → Bool
  | [] => true
  | b :: r => b == 10 || ((isW b || b == 46 || b == 32) && !(b == 32 && inWord r) && lineOk r)

/-- the rest after the `]` of an attribute whose bytes are names, spaces and commas -/
def attrEnd : List UInt8 → Option (List UInt8)
  | [] => none
  | b :: r => if b == 93 then some r else if isW b || b == 32 || b == 44 then attrEnd r else none

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
       else blockEnd 0 r.tail).map fun t => ([], t)
    else if c == 64 && r.head? == some 91 then (attrEnd r.tail).map fun t => ([], t)
    else match opTable.find? (fun e => e.1.isPrefixOf (c :: r)) with
      | some (s, k) => some ([k], (c :: r).drop s.length)
      | none =>
        let w := (c :: r).takeWhile isW
        let rest := (c :: r).dropWhile isW
        if isD c then (if w.all isD then some (5 :: le8 (numVal w), rest) else none)
        else if isW c then
          if lineKw.contains w then (if lineOk rest then some ([], rest.dropWhile (· != 10)) else none)
          else if dropKw.contains w then some ([], rest)
          else some ((match kwTable.lookup w with
                 | some k => [k]
                 | none => 14 :: (w.flatMap fun b => [1, b.toUInt64]) ++ [0]), rest)
        else none

inductive Lexes : List UInt8 → List UInt64 → Prop
  | nil : Lexes [] []
  | cons {l e r t} : step l = some (e, r) → Lexes r t → Lexes l (e ++ t)

end LexSpec
