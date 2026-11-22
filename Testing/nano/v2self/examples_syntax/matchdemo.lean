-- matchdemo: `match` on UInt64 literals with `_` / variable / pair arms (SYNTAX_EXP.md, construct 2).
-- per byte b: 'a' -> 'A', 'b' -> 'B', space -> '_', a digit d -> 2 * d - 48 mod 256, anything else -> b + 1
-- input  (hex): 61 62 20 33 7a
-- expect (hex): 41 42 5f 36 7b
/-- the digit rule, by a pair match -/
def dg (p : UInt64 × UInt64) : UInt64 := match p with
  | (d, z) => d + d - z

def cls (b : UInt64) : UInt64 :=
  let c := match b with
    | 97 => 65
    | 98 => 66
    | 32 => 95
    | _ => (if b < 58 then (if 47 < b then 1 else 0) else 0);
  if c == 1 then dg (b, 48) else if c == 0 then b + 1 else c

def f : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, o => o
  | n + 1, x, i, o => f n x (i + 1) (put o (match cls (rd x i) with | 300 => 0 | v => v))
def m (x : List UInt8) : List UInt8 := f (len' x) x 0 []
