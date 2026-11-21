-- differential test: the nano-subset stages (Nano/<stages>) against the Nano/V2S stages
-- (run: lake env lean Testing/nano/v2self/diff_test.lean; every #eval prints the number of MISMATCHES, 0 expected)
import Legacy.Nano.V2Self.Legacy.Lex
import Legacy.Nano.V2Self.Legacy.Inl
import Legacy.Nano.V2Self.Legacy.Parse
import Legacy.Nano.V2S.Lex
import Legacy.Nano.V2S.InlT
import Legacy.Nano.V2S.Parse
open Nano
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64
-- lexer: random strings from token pieces
def pieces : List String := ["def ", "f", " (x y : UInt64) : UInt64 := ", "x", " + ", "y", " * ", "(", ")", "let ", "z", " := ", "; ", "\n", "\n ", "12", "007", "-", "--", ":", "=", ":=", "Int64", "UInt64", "a_1", "A", "g(", ")x", " ", "\ndef", "\ndefx", "\nx", "18446744073709551617", "_", "letx", "\t", "q9"]
def gen : Nat → Nat → String → String × Nat
  | 0, s, acc => (acc, s)
  | n+1, s, acc => let s1 := lcg s; gen n s1 (acc ++ pieces[(s1 >>> 33) % pieces.length]!)
def good : List String := ["def f (x y : UInt64) : UInt64 := x + y * 3\n", "def f (x : Int64) : Int64 := let z := x - 1; z * z\n",
  "def g (a b : UInt64) : UInt64 := a - b\ndef f (x : UInt64) : UInt64 := g x 7\n",
  "def k : UInt64 := 7\ndef h (a : UInt64) : UInt64 := a * 3\ndef f (x y z : UInt64) : UInt64 := g (x + 1) y + h k - k\n",
  "def g (a b : UInt64) : UInt64 := a - b\ndef k : UInt64 := 7\ndef f (x y z : UInt64) : UInt64 := g k (-1) + (let q := x; q * -5) - h\n",
  "def f (x : UInt64) (y : UInt64) : UInt64 := let a := let b := x; b + y; a * (a - 1)\n"]
def testLex : Nat → Nat → Nat → Nat
  | 0, _, bad => bad
  | k+1, s, bad =>
    let (str, s') := gen (k % 17) s ""
    let xs := str.toUTF8.toList
    testLex k s' (if l15 xs == Nano.V2S.lexV xs then bad else bad + 1)
#eval testLex 5000 7 0
#eval good.map fun g => (l15 g.toUTF8.toList == Nano.V2S.lexV g.toUTF8.toList, (l15 g.toUTF8.toList).length)
-- inliner: random record streams
def genI : Nat → Nat → List UInt8 → List UInt8 × Nat
  | 0, s, acc => (acc.reverse, s)
  | n+1, s, acc =>
    let s1 := lcg s; let r := (s1 >>> 33) % 100
    let m : Nat := if r < 15 then 13 else if r < 25 then 14 else if r < 50 then 15 else (s1 >>> 20) % 13
    let s2 := lcg s1
    let x : Nat := if m == 14 then (s2 >>> 33) % 2 else (s2 >>> 33) % 6
    genI n s2 ((x.toUInt8) :: (m.toUInt8) :: acc)
def testInl : Nat → Nat → Nat → Nat
  | 0, _, bad => bad
  | k+1, s, bad =>
    let (xs, s') := genI (k % 23) s []
    let xs := if k % 3 == 0 then xs ++ [7] else xs
    testInl k s' (if j8 xs == Nano.V2S.inlTV xs then bad else bad + 1)
#eval testInl 2000 7 0
-- parser: tag streams of good sources, mutated
def mutate (xs : List UInt8) (s : Nat) : List UInt8 :=
  let i := (s >>> 7) % (xs.length + 1); let b : UInt8 := ((s >>> 20) % 16).toUInt8
  match (s >>> 40) % 3 with
  | 0 => xs.set i b
  | 1 => xs.take i ++ [b] ++ xs.drop i
  | _ => xs.take i ++ xs.drop (i + 1)
def testPar : Nat → Nat → Nat × Nat → Nat × Nat
  | 0, _, r => r
  | k+1, s, (bad, ok) =>
    let s1 := lcg s
    let src := good[(s1 >>> 33) % good.length]!
    let base := Nano.V2S.lexV src.toUTF8.toList
    let xs := if k % 4 == 0 then base else mutate (mutate base s1) (lcg s1)
    let r := r16 xs; let e := Nano.V2S.p2bV xs
    testPar k s1 (if r == e then bad else bad + 1, if e.isEmpty then ok else ok + 1)
#eval testPar 6000 5 (0, 0)
