/- Tagged data without allocation: structures, tuples and `Option` of scalars as parameters and results.
One variable per scalar component (`Option α`: `isSome` as a 0/1 word and the payload `getD 0`); a `match` on a
structure is field access, a `match` on an `Option` is a test of the tag variable.  All theorems are generated. -/
import Proven.Frontx.Translate

namespace Proven.Frontx.Data
open Proven Proven.Frontx

structure Point where
  x : Nat
  y : Nat
def addPoints (p1 p2 : Point) : Point := { x := p1.x + p2.x, y := p1.y + p2.y }
def swap (p : UInt64 × UInt64) : UInt64 × UInt64 :=
  match p with
  | (a, b) => (b, a)
def getOr (o : Option Nat) (d : Nat) : Nat :=
  match o with
  | none => d
  | some v => v
def fst3 (p : Nat × UInt8 × Bool) : UInt8 := p.2.1
def zeroX (p : Point) : Point := { p with x := 0 }
/-- recursion whose state is a structure -/
def countdown (p : Point) : Nat :=
  if h : p.x = 0 then p.y else countdown { x := p.x - 1, y := p.y + 2 }
termination_by p.x
decreasing_by show p.x - 1 < p.x; omega
frontx_compile addPoints
frontx_compile swap
frontx_compile getOr
frontx_compile fst3
frontx_compile zeroX
frontx_compile countdown with fun p => p.y + 2 * p.x < 2 ^ 64

end Proven.Frontx.Data
