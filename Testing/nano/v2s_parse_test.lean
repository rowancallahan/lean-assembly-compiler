-- differential test of the nano v2 source parser p2bV against stage2b (run: lake env lean Testing/nano/v2s_parse_test.lean)
import Nano.V2S.Parse
import Nano.V2S.Lex
open Nano Nano.V2S Nano.PS Nano.LS Nano.B
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64
def good : List String := [
 "def f (x y : UInt64) : UInt64 := x + y * 3\n",
 "def f (x : Int64) : Int64 := let z := x - 1; z * z\n",
 "def g (a b : UInt64) : UInt64 := a - b\ndef f (x : UInt64) : UInt64 := g x 7\n",
 "def k : UInt64 := 7\ndef h (a : UInt64) : UInt64 := a * 3\ndef f (x y z : UInt64) : UInt64 := g (x + 1) y + h k - k\n",
 "def g (a b : UInt64) : UInt64 := a - b\ndef k : UInt64 := 7\ndef f (x y z : UInt64) : UInt64 := g k (-1) + (let q := x; q * -5) - h\n",
 "def f (x : UInt64) (y : UInt64) : UInt64 := let a := let b := x; b + y; a * (a - 1)\n",
 "def f (x : UInt64) : UInt64 := ((x))\n",
 "def g : UInt64 := 1\ndef g : UInt64 := 2\n",
 "def f (x x : UInt64) : UInt64 := x\n"]
-- mutate: random byte replace/insert/delete on the tag stream
def mutate (xs : List UInt8) (s : Nat) : List UInt8 :=
  let i := (s >>> 7) % (xs.length + 1); let b : UInt8 := ((s >>> 20) % 16).toUInt8
  match (s >>> 40) % 3 with
  | 0 => xs.set i b
  | 1 => xs.take i ++ [b] ++ xs.drop i
  | _ => xs.take i ++ xs.drop (i + 1)
def test : Nat → Nat → Nat × Nat → Nat × Nat
  | 0, _, r => r
  | k+1, s, (bad, ok) =>
    let s1 := lcg s
    let src := good[(s1 >>> 33) % good.length]!
    let base := stage2a (lexB src.toUTF8.toList)
    let xs := if k % 4 == 0 then base else mutate (mutate base s1) (lcg s1)
    let r := p2bV xs; let e := stage2b xs
    test k s1 (if r == e then bad else bad + 1, if e.isEmpty then ok else ok + 1)
#eval good.map fun g => let xs := stage2a (lexB g.toUTF8.toList); (p2bV xs == stage2b xs, (stage2b xs).length)
#eval test 3000 5 (0, 0)
def findBad : Nat → Nat → List (List UInt8 × List UInt8 × List UInt8) → List (List UInt8 × List UInt8 × List UInt8)
  | 0, _, acc => acc
  | k+1, s, acc =>
    let s1 := lcg s
    let src := good[(s1 >>> 33) % good.length]!
    let base := stage2a (lexB src.toUTF8.toList)
    let xs := if k % 4 == 0 then base else mutate (mutate base s1) (lcg s1)
    let r := p2bV xs; let e := stage2b xs
    findBad k s1 (if r == e then acc else (xs, r, e) :: acc)
#eval (findBad 3000 5 []).length
#eval test 20000 11 (0, 0)
