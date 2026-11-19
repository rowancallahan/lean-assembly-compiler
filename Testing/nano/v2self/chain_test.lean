-- the chained nano driver `C.m` against the list-based chain (`chainS`) and the v1 compiler `Nano.selfHosted`'s stages
-- (run: lake env lean Testing/nano/v2self/chain_test.lean; first number = mismatches, expected 0)
import Nano.V2Self.Legacy.C.Main
import Nano.V2Self.Legacy.Driver
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64
def pieces : List String := ["def ", "f", " (x y : UInt64) : UInt64 := ", "x", " + ", "y", " * ", "(", ")", "let ", "z", " := ", "; ", "\n", "\n ", "12", "-", ":", "g ", "g(", " ", "\ndef", "UInt64", "Int64"]
def gen : Nat → Nat → String → String × Nat
  | 0, s, acc => (acc, s)
  | n+1, s, acc => let s1 := lcg s; gen n s1 (acc ++ pieces[(s1 >>> 33) % pieces.length]!)
def good : List String := ["def f (x y : UInt64) : UInt64 := x + y * 3\n", "def f (x : Int64) : Int64 := let z := x - 1; z * z\n",
  "def g (a b : UInt64) : UInt64 := a - b\ndef f (x : UInt64) : UInt64 := g x 7\n",
  "def k : UInt64 := 7\ndef h (a : UInt64) : UInt64 := a * 3\ndef f (x y z : UInt64) : UInt64 := g (x + 1) y + h k - k\n",
  "def g (a b : UInt64) : UInt64 := a - b\ndef k : UInt64 := 7\ndef f (x y z : UInt64) : UInt64 := g k (-1) + (let q := x; q * -5) - h\n",
  "def f (x : UInt64) (y : UInt64) : UInt64 := let a := let b := x; b + y; a * (a - 1)\n"]
#eval good.map fun g => let s := g.toUTF8.toList; (C.m s == chainS s, (C.m s).length)
def test : Nat → Nat → Nat × Nat → Nat × Nat
  | 0, _, r => r
  | k+1, s, (bad, ok) =>
    let (str, s') := gen (k % 25) s ""
    let xs := str.toUTF8.toList
    test k s' (if C.m xs == chainS xs then bad else bad + 1, if (C.m xs).isEmpty then ok else ok + 1)
#eval test 3000 3 (0, 0)
