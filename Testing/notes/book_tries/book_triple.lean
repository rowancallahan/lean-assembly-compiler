import Arm.CompilerArm
import Compiler.Front.Reify
/- Three-way test of the restated book functions (verdict B, expression class).
   Lean side = the ORIGINAL book definition over Nat (verbatim where the book gives one), evaluated by Lean;
   machine side = `compile`/`Arm.compile` of `reify%` of the 64-bit restatement.
   Output format of Testing/asm/triple.py. -/
open Proven
def hex (w : Nat) : String := String.ofList (Nat.toDigits 16 w)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
-- book definitions (fp-lean, Examples/Intro.lean and nearby)
def add1 (n : Nat) : Nat := n + 1
def Nat.double (x : Nat) : Nat := x + x
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
def timesTwelve (x : Nat) := x * 12
def maximum (n k : Nat) : Nat := if n < k then k else n
def isZero (n : Nat) : Bool := match n with | Nat.zero => true | Nat.succ _ => false
def pred (n : Nat) : Nat := match n with | Nat.zero => Nat.zero | Nat.succ k => k
def even : Nat → Bool | 0 => true | n + 1 => not (even n)
def halve : Nat → Nat | 0 => 0 | 1 => 0 | n + 2 => halve n + 1
def plus (n : Nat) : Nat → Nat | 0 => n | k + 1 => plus n k + 1   -- book: Nat.succ (plus n k')
def minus (n : Nat) : Nat → Nat | 0 => n | k + 1 => pred (minus n k)
-- restatements
def r_add1 (n : BitVec 64) : BitVec 64 := n + 1
def r_double (x : BitVec 64) : BitVec 64 := x + x
def r_triple (x : BitVec 64) : BitVec 64 := x + x + x
def r_quadruple (x : BitVec 64) : BitVec 64 := x + x + x + x
def r_times12 (x : BitVec 64) : BitVec 64 := (x <<< ((3 : BitVec 64).toNat % 64)) + (x <<< ((2 : BitVec 64).toNat % 64))
def r_maximum (a b : BitVec 64) : BitVec 64 := if (if a < b then 1 else 0 : BitVec 64) = 0 then a else b
def r_isZero (n : BitVec 64) : BitVec 64 := if n = 0 then 1 else 0
def r_pred (n : BitVec 64) : BitVec 64 := if n = 0 then 0 else n - 1
def r_even (n : BitVec 64) : BitVec 64 := if n &&& 1 = 0 then 1 else 0
def r_halve (n : BitVec 64) : BitVec 64 := n >>> ((1 : BitVec 64).toNat % 64)
def r_plus (a b : BitVec 64) : BitVec 64 := a + b
def r_minus (a b : BitVec 64) : BitVec 64 := if (if a < b then 1 else 0 : BitVec 64) = 0 then a - b else 0
def edge : List Nat := [0, 1, 2, 3, 4, 5, 63, 64, 65, 127, 128, 255, 256, 2^31, 2^32 - 1, 2^32, 2^62, 2^63 - 1, 2^63, 2^63 + 1, 2^64 - 2, 2^64 - 1]
/-- inputs (a,b): edge values and random values, all `< bound`; 2 inputs vary, c d are random junk -/
def ins (bound : Nat) (n : Nat) : List (List Nat) :=
  let es := (edge.filter (· < bound)) ++ [bound - 1]
  es.flatMap (fun a => es.map fun b => [a, b, rnd a b, rnd b a]) ++
  (List.range n).map fun i => [rnd i 1 % bound, rnd i 2 % bound, rnd i 3, rnd i 4]
def small (n : Nat) : List (List Nat) := (List.range n).flatMap fun a => (List.range 6).map fun b => [a, b, rnd a b, rnd b a]
def B (b : Bool) : Nat := if b then 1 else 0
-- name, expression, original book function on (a0,a1), inputs
def cases : List (String × Exp × (Nat → Nat → Nat) × List (List Nat)) := [
  ("add1", reify% r_add1, fun a _ => add1 a, ins (2^64 - 1) 300),
  ("double", reify% r_double, fun a _ => Nat.double a, ins (2^63) 300),
  ("triple", reify% r_triple, fun a _ => triple a, ins (2^64 / 3) 300),
  ("quadruple", reify% r_quadruple, fun a _ => quadruple a, ins (2^62) 300),
  ("timesTwelve", reify% r_times12, fun a _ => timesTwelve a, ins (2^64 / 12) 300),
  ("maximum", reify% r_maximum, fun a b => maximum a b, ins (2^64) 300),
  ("isZero", reify% r_isZero, fun a _ => B (isZero a), ins (2^64) 300),
  ("pred", reify% r_pred, fun a _ => pred a, ins (2^64) 300),
  -- recursive book definitions: original only runnable on small arguments
  ("even_small", reify% r_even, fun a _ => B (even a), small 2000),
  ("halve_small", reify% r_halve, fun a _ => halve a, small 2000),
  ("plus_small", reify% r_plus, fun a b => plus a b, small 300 ++ (small 300).map fun r => [r[1]!, r[0]!, r[2]!, r[3]!]),
  ("minus_small", reify% r_minus, fun a b => minus a b, small 300 ++ (small 300).map fun r => [r[1]!, r[0]!, r[2]!, r[3]!]),
  -- large inputs against Lean's own Nat operations (spec of the book def, not the def itself)
  ("even_large_vs_mod", reify% r_even, fun a _ => B (a % 2 == 0), ins (2^64) 300),
  ("halve_large_vs_div", reify% r_halve, fun a _ => a / 2, ins (2^64) 300),
  ("plus_large_vs_add", reify% r_plus, fun a b => a + b, ins (2^63) 300),
  ("minus_large_vs_sub", reify% r_minus, fun a b => a - b, ins (2^64) 300)]
#eval show IO Unit from do
  for (name, e, f, is) in cases do
    IO.println s!"case {name}"
    IO.println s!"rv {" ".intercalate ((compile e).map (hex ·.toNat))}"
    IO.println s!"arm {" ".intercalate ((Arm.compile e).map (hex ·.toNat))}"
    for a in is do
      IO.println s!"t {" ".intercalate (a.map hex)} {hex (f a[0]! a[1]!)}"
