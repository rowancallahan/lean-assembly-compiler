-- hex: every input byte as two lowercase hex digits (text).
-- example: "Hi!" (48 69 21) -> "486921"
-- input  (hex): 48 69 21
-- expect (hex): 34 38 36 39 32 31
def h (d : UInt64) : UInt64 := if d < 10 then d + 48 else d + 87
def f : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, o => o
  | n + 1, x, i, o =>
    let c := rd x i;
    let d := c >>> 4;
    f n x (i + 1) (put (put o (h d)) (h (c - d * 16)))
def m (x : List UInt8) : List UInt8 := f (len' x) x 0 []
