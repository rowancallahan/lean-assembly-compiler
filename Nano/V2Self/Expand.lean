/- Nano/V2Self: the expander stage (Nano/V2S/Expand.lean) in the nano subset. -/
import Nano.V2Self.Prelude

def e0 (p q : UInt64) (o : List UInt8) : List UInt8 :=
  if p == 0 then put (put (put (put (put (put (put (put (put (put (put (put o 5) 31) 2) 3) 1) 31) 31) 3) 0) 28) 10) 0
  else if p == 1 then put (put (put (put o 4) 5) 28) 7
  else if p == 2 then put (put (put (put (put (put (put (put (put (put (put (put o 1) 5) 5) 8) 4) 6) 28) q) 14) 5) 5) 6
  else if p == 3 then put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put o 0) 31) 31) 248) 7) 0) 31) 12) 0) 10) 0) 255) 48) 0) 1) 0) 11) 5) 31) 0
  else if p == 4 then put (put (put (put o 8) 28) 28) 1
  else if p == 5 then put (put (put (put o 0) 5) 0) 0
  else if p == 6 then put (put (put (put (put (put (put (put o 1) 5) 5) 8) 6) 5) 5) q
  else if p == 7 then put (put (put (put o 3) 5) 31) q
  else if p == 8 then put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put (put o 3) 6) 31) 0) 3) 5) 31) 1) 8) 31) 31) 1) q) 5) 5) 6) 11) 5) 31) 0
  else if p == 9 then put (put (put (put (put (put (put (put (put (put (put (put o 3) 5) 31) 0) 8) 31) 31) q) 11) 5) 31) 0
  else if p == 10 then put (put (put (put o 5) 6) 5) q
  else if p == 11 then put (put (put (put o 16) 6) 13) q
  else put (put (put (put o 48) 0) 1) 0

def e1 : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, o => o
  | n + 1, x, i, o =>
    if i + 2 ≤ len x then
      let p := rd x i;
      let q := rd x (i + 1);
      e1 n x (i + 2) (e0 p q o)
    else o

def e2 (x : List UInt8) : List UInt8 := e1 (len' x) x 0 []
