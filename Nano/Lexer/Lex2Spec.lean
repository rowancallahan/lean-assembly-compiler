/- Nano/Lexer/Lex2Spec: the SPECIFICATION of the S lexer (`C.s10`), independent of Lex2's code.
`Lexes x t`: the byte list `x` lexes to the token word list `t`.  One token at a time (`step`), maximal munch:
whitespace (space, newline) is skipped; the operator table is searched longest-first; a word is a maximal run of
[A-Za-z0-9_'] (a keyword/prim, an identifier `14 (1,b)* 0`, or, when it starts with a digit, a decimal number
`5` + 8 little-endian bytes of the value mod 2^64, all characters of the word must then be digits).
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

/-- decimal value mod 2^64 -/
def numVal (w : List UInt8) : Nat := w.foldl (fun a b => (a * 10 + (b.toNat - 48)) % 2 ^ 64) 0
/-- 8 little-endian bytes -/
def le8 (n : Nat) : List UInt64 := (List.range 8).map fun i => ((n / 256 ^ i) % 256).toUInt64

/-- one lexing step: emitted words and the rest of the input -/
def step : List UInt8 → Option (List UInt64 × List UInt8)
  | [] => none
  | c :: r =>
    if c == 32 || c == 10 then some ([], r)
    else match opTable.find? (fun e => e.1.isPrefixOf (c :: r)) with
      | some (s, k) => some ([k], (c :: r).drop s.length)
      | none =>
        let w := (c :: r).takeWhile isW
        let rest := (c :: r).dropWhile isW
        if isD c then (if w.all isD then some (5 :: le8 (numVal w), rest) else none)
        else if isW c then
          some ((match kwTable.lookup w with
                 | some k => [k]
                 | none => 14 :: (w.flatMap fun b => [1, b.toUInt64]) ++ [0]), rest)
        else none

inductive Lexes : List UInt8 → List UInt64 → Prop
  | nil : Lexes [] []
  | cons {l e r t} : step l = some (e, r) → Lexes r t → Lexes l (e ++ t)

end LexSpec
