-- upper: ASCII letters a..z become A..Z, every other byte is copied.
-- example: "Hello, nano!" -> "HELLO, NANO!"
-- input  (hex): 48 65 6c 6c 6f 2c 20 6e 61 6e 6f 21
-- expect (hex): 48 45 4c 4c 4f 2c 20 4e 41 4e 4f 21
def u (c : UInt64) : UInt64 := if 96 < c then if c < 123 then c - 32 else c else c
def f : Nat → List UInt8 → UInt64 → List UInt8 → List UInt8
  | 0, x, i, o => o
  | n + 1, x, i, o => f n x (i + 1) (put o (u (rd x i)))
def m (x : List UInt8) : List UInt8 := f (len' x) x 0 []
