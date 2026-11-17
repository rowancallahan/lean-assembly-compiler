def l : Nat → List UInt8 → List UInt8 → List UInt8
  | 0, x, o => o
  | n + 1, x, o => l n x (put (put o 1) (rd x (len (put o 2))))
def m (x : List UInt8) : List UInt8 :=
  l (len' x) x []
