def l : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, i => i
  | n + 1, x, i => l n x (i + n)
def m (x : List UInt8) : List UInt8 :=
  put [] (l (len' x) x (len x))
