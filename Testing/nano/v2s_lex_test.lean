-- differential test of lexV against lexA (run: lake env lean Testing/nano/v2s_lex_test.lean)
import Legacy.Nano.V2S.Lex
open Nano Nano.V2S Nano.LS
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64
def pieces : List String := ["def ", "f", " (x y : UInt64) : UInt64 := ", "x", " + ", "y", " * ", "(", ")", "let ", "z", " := ", "; ", "\n", "\n ", "12", "007", "-", "--", ":", "=", ":=", "Int64", "UInt64", "a_1", "A", "g(", ")x", " ", "\ndef", "\ndefx", "\nx", "18446744073709551617", "_", "letx", "\t", "q9"]
def gen : Nat → Nat → String → String × Nat
  | 0, s, acc => (acc, s)
  | n+1, s, acc => let s1 := lcg s; gen n s1 (acc ++ pieces[(s1 >>> 33) % pieces.length]!)
def good : List String := ["def f (x y : UInt64) : UInt64 := x + y * 3\n", "def f (x : Int64) : Int64 := let z := x - 1; z * z\n",
  "def g (a b : UInt64) : UInt64 := a - b\ndef f (x : UInt64) : UInt64 := g x 7\n"]
def test : Nat → Nat → Nat → Nat × Nat
  | 0, _, bad => (bad, 0)
  | k+1, s, bad =>
    let (str, s') := gen (k % 17) s ""
    let xs := str.toUTF8.toList
    test k s' (if lexV xs == lexA xs then bad else bad + 1)
#eval test 3000 7 0
#eval good.map fun g => (lexV g.toUTF8.toList == lexA g.toUTF8.toList, (lexA g.toUTF8.toList).length)
def cnt : Nat → Nat → Nat → Nat
  | 0, _, c => c
  | k+1, s, c => let (str, s') := gen (k % 17) s ""; cnt k s' (if (lexA str.toUTF8.toList).isEmpty then c else c + 1)
#eval cnt 3000 7 0
