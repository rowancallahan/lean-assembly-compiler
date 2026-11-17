/- Nano/V2Self/C: expander stage on Buf (from Nano/V2Self/Expand.lean) -/
import Nano.V2Self.C.Asm
namespace C

def e0 (p q : UInt64) (o : Buf) : Buf :=
  if p == 0 then q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 o 5) 31) 2) 3) 1) 31) 31) 3) 0) 28) 10) 0
  else if p == 1 then q0 (q0 (q0 (q0 o 4) 5) 28) 7
  else if p == 2 then q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 o 1) 5) 5) 8) 4) 6) 28) q) 14) 5) 5) 6
  else if p == 3 then q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 o 0) 31) 31) 248) 7) 0) 31) 12) 0) 10) 0) 255) 48) 0) 1) 0) 11) 5) 31) 0
  else if p == 4 then q0 (q0 (q0 (q0 o 8) 28) 28) 1
  else if p == 5 then q0 (q0 (q0 (q0 o 0) 5) 0) 0
  else if p == 6 then q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 o 1) 5) 5) 8) 6) 5) 5) q
  else if p == 7 then q0 (q0 (q0 (q0 o 3) 5) 31) q
  else if p == 8 then q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 o 3) 6) 31) 0) 3) 5) 31) 1) 8) 31) 31) 1) q) 5) 5) 6) 11) 5) 31) 0
  else if p == 9 then q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 o 3) 5) 31) 0) 8) 31) 31) q) 11) 5) 31) 0
  else if p == 10 then q0 (q0 (q0 (q0 o 5) 6) 5) q
  else if p == 11 then q0 (q0 (q0 (q0 o 16) 6) 13) q
  else q0 (q0 (q0 (q0 o 48) 0) 1) 0

def e1 : Nat → Buf → UInt64 → Buf → Buf
  | 0, x, i, o => o
  | n + 1, x, i, o =>
    if i + 2 ≤ bsize x then
      let p := bget x i;
      let q := bget x (i + 1);
      e1 n x (i + 2) (e0 p q o)
    else o

def e2 (x : Buf) : Buf := e1 16777216 x 0 bnew

end C
