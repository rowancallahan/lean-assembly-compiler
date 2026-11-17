/- Nano/V2Self/C: lexer stage, program input in, Buf out (from Nano/V2Self/Lex.lean) -/
import Nano.V2Self.C.Base
namespace C

def l16 (c : UInt64) : UInt64 := if (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95 || (48 ≤ c && c ≤ 57) then 1 else 0

def l0 : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, p, g => p
  | n + 1, x, p, g => if p < len x && l16 (rd x p) == 1 && g ≠ 0 then l0 n x (p + 1) (g - 1) else p

def l1 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, i, e, g => 1
  | n + 1, x, i, e, g => if i < e && g ≠ 0 then if 48 ≤ rd x i && rd x i ≤ 57 then l1 n x (i + 1) e (g - 1) else 0 else 1

def l2 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, i, e, g => 1
  | n + 1, x, i, e, g =>
    if i < e && g ≠ 0 then if (48 ≤ rd x i && rd x i ≤ 57) || rd x i == 95 then l2 n x (i + 1) e (g - 1) else 0 else 1

def l3 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, i, e, a, g => a
  | n + 1, x, i, e, a, g => if i < e && g ≠ 0 then l3 n x (i + 1) e (a * 10 + (rd x i - 48)) (g - 1) else a

def l4 (x : List UInt8) (p e g : UInt64) : UInt64 := if e ≤ p then 0
  else
    let c := rd x p;
    if 48 ≤ c && c ≤ 57 then if l1 (len' x) x p e g == 1 then 7 else 0
    else if e - p == 3 && c == 100 && rd x (p + 1) == 101 && rd x (p + 2) == 102 then 3
    else if e - p == 3 && c == 108 && rd x (p + 1) == 101 && rd x (p + 2) == 116 then 4
    else if e - p == 6 && c == 85 && rd x (p + 1) == 73 && rd x (p + 2) == 110 && rd x (p + 3) == 116 && rd x (p + 4) == 54 && rd x (p + 5) == 52 then 5
    else if e - p == 5 && c == 73 && rd x (p + 1) == 110 && rd x (p + 2) == 116 && rd x (p + 3) == 54 && rd x (p + 4) == 52 then 6
    else if 97 ≤ c && c ≤ 122 && l2 (len' x) x (p + 1) e g == 1 then 16
    else 0

def l5 (x : List UInt8) (p g : UInt64) : UInt64 := if p < len x then
    let c := rd x p;
    if c == 32 then 2
    else if c == 10 then
      if p + 1 < len x then
        let d := rd x (p + 1);
        if d == 32 || d == 10 then 2
        else if d == 100 && p + 3 < len x && rd x (p + 2) == 101 && rd x (p + 3) == 102 then
          if p + 4 < len x && l16 (rd x (p + 4)) == 1 then 0 else 2
        else 0
      else 1
    else if c == 40 then 8
    else if c == 41 then 9
    else if c == 43 then 12
    else if c == 45 then if p + 1 < len x && rd x (p + 1) == 45 then 0 else 13
    else if c == 42 then 14
    else if c == 59 then 15
    else if c == 58 then if p + 1 < len x && rd x (p + 1) == 61 then 11 else 10
    else if l16 c == 1 then l4 x p (l0 (len' x) x p g) g
    else 0
  else 1

def l6 (x : List UInt8) (p g : UInt64) : UInt64 := let c := rd x p;
  if c == 58 && p + 1 < len x && rd x (p + 1) == 61 then p + 2
  else if l16 c == 1 then l0 (len' x) x p g
  else p + 1

def l7 (k : UInt64) : UInt64 := if k == 5 then 1 else if k == 6 then 2 else 0

def l8 (t c : UInt64) : UInt64 := if c == 0 then t else if t == 0 then c else if t == c then c else 3

def l9 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, p, t, r => if p < len x then 4 else t
  | f + 1, x, p, t, r =>
    let g := r - 1;
    let k := l5 x p g;
    if k == 0 then 4
    else if k == 1 then t
    else l9 f x (l6 x p g) (l8 t (l7 k)) g

def l10 : Nat → List UInt8 → UInt64 → UInt64 → UInt64 → Buf → Buf
  | 0, x, i, e, g, o => q0 o 0
  | n + 1, x, i, e, g, o => if i < e && g ≠ 0 then l10 n x (i + 1) e (g - 1) (q0 (q0 o 1) (rd x i)) else q0 o 0

def l11 (v : UInt64) (o : Buf) : Buf := q0 (q0 (q0 (q0 (q0 (q0 (q0 (q0 o v) (v >>> 8)) (v >>> 16)) (v >>> 24)) (v >>> 32)) (v >>> 40)) (v >>> 48))
    (v >>> 56)

def l12 (x : List UInt8) (k p e g : UInt64) (o : Buf) : Buf := if k == 7 then l11 (l3 (len' x) x p e 0 g) (q0 o 5)
  else if k == 16 then l10 (len' x) x p e g (q0 o 14)
  else q0 o (k - 2)

def l13 : Nat → List UInt8 → UInt64 → UInt64 → Buf → Buf
  | 0, x, p, r, o => o
  | f + 1, x, p, r, o =>
    let g := r - 1;
    let k := l5 x p g;
    if k == 0 || k == 1 then o
    else if k == 2 then l13 f x (l6 x p g) g o
    else l13 f x (l6 x p g) g (l12 x k p (l6 x p g) g o)

def l14 : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, i => 1
  | n + 1, x, i =>
    if i + 1 < len x then
      let a := rd x i;
      let b := rd x (i + 1);
      if (l16 a == 1 || a == 41) && b == 40 then 0
      else if a == 41 && l16 b == 1 then 0
      else l14 n x (i + 1)
    else 1

def l15 (x : List UInt8) : Buf := if l14 (len' x) x 0 == 1 then
    let t := l9 (len' x) x 0 0 (len x);
    if t == 1 || t == 2 then l13 (len' x) x 0 (len x) (q0 bnew t) else bnew
  else bnew

end C
